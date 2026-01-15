/**
 * WasmTranspilerAdapter - WebAssembly-Based Transpiler Adapter
 *
 * Implements ITranspiler interface using the official @hupyy/cpptoc-wasm package.
 * NO BACKEND - transpilation runs entirely in the browser!
 *
 * Following SOLID principles:
 * - Single Responsibility: WASM-based transpilation only
 * - Open/Closed: Can extend with caching without modifying core
 * - Liskov Substitution: Substitutable for any ITranspiler implementation
 * - Interface Segregation: Implements only ITranspiler methods
 * - Dependency Inversion: Depends on ITranspiler abstraction
 */

import type { ITranspiler } from '../core/interfaces/ITranspiler';
import type { TranspileOptions as ITranspileOptions, TranspileResult as ITranspileResult, ValidationResult } from '../core/interfaces/types';
import type {
  WASMModule,
  TranspilerInstance,
  TranspileOptions as WasmTranspileOptions,
  TranspileResult as WasmTranspileResult,
  CreateCppToCModule
} from '@hupyy/cpptoc-wasm';

/**
 * WebAssembly-based transpiler adapter
 *
 * Uses @hupyy/cpptoc-wasm for real C++ to C transpilation in the browser.
 * NO HTTP calls, NO backend dependency!
 */
export class WasmTranspilerAdapter implements ITranspiler {
  private wasmModule: WASMModule | null = null;
  private transpilerInstance: TranspilerInstance | null = null;
  private initPromise: Promise<void> | null = null;

  /**
   * Create WASM transpiler adapter
   *
   * Module is lazy-loaded on first transpile() call.
   */
  constructor() {
    console.log('✅ WasmTranspilerAdapter initializing (@hupyy/cpptoc-wasm will load on first use)');
  }

  /**
   * Initialize WASM module (lazy loaded on first use)
   *
   * @throws Error if WASM module fails to load
   */
  private async initialize(): Promise<void> {
    // Already initialized
    if (this.wasmModule && this.transpilerInstance) {
      return;
    }

    // Initialization in progress
    if (this.initPromise) {
      await this.initPromise;
      return;
    }

    // Start initialization
    this.initPromise = (async () => {
      try {
        console.log('⏳ Loading @hupyy/cpptoc-wasm transpiler...');

        // Dynamically import the WASM module factory
        // The package.json exports "." points to full build by default
        // Type assertion needed because Emscripten module doesn't export TypeScript types directly
        const module = await import('@hupyy/cpptoc-wasm');
        const createModule = (module as any).default as CreateCppToCModule;

        // Create WASM module with Emscripten options
        this.wasmModule = await createModule({
          // Locate WASM file (handled by bundler automatically for most cases)
          locateFile: (path: string, prefix: string) => {
            // Return default path (bundler will resolve this)
            return prefix + path;
          },
          // Called when WASM runtime is ready
          onRuntimeInitialized: () => {
            console.log('🚀 WASM runtime initialized');
          }
        });

        // Create transpiler instance
        this.transpilerInstance = new this.wasmModule.Transpiler();

        console.log('✅ @hupyy/cpptoc-wasm transpiler ready');
        console.log(`📦 Transpiler version: ${this.transpilerInstance.getVersion()}`);
      } catch (error) {
        console.error('❌ Failed to load transpiler:', error);
        this.initPromise = null; // Allow retry
        throw new Error(
          `Failed to initialize WASM transpiler: ${error instanceof Error ? error.message : 'Unknown error'}`
        );
      }
    })();

    await this.initPromise;
  }

  /**
   * Transpile C++ source code to C using @hupyy/cpptoc-wasm
   *
   * @param source - C++ source code
   * @param options - Transpilation options
   * @returns Transpilation result
   */
  async transpile(source: string, options?: ITranspileOptions): Promise<ITranspileResult> {
    try {
      // Ensure WASM is initialized
      await this.initialize();

      if (!this.transpilerInstance) {
        throw new Error('WASM transpiler not initialized');
      }

      console.log('🔄 Transpiling with @hupyy/cpptoc-wasm...', {
        sourceLength: source.length,
        target: options?.target || 'c99'
      });

      // Map interface options to WASM options
      const wasmOptions: WasmTranspileOptions = {
        target: options?.target as 'c89' | 'c99' | 'c11' | 'c17',
        optimize: options?.optimize,
        enableACSL: options?.acsl?.statements || options?.acsl?.typeInvariants || options?.acsl?.axiomatics,
        acsl: options?.acsl ? {
          statements: options.acsl.statements,
          typeInvariants: options.acsl.typeInvariants,
          axiomatics: options.acsl.axiomatics,
          ghostCode: options.acsl.ghostCode,
          behaviors: options.acsl.behaviors
        } : undefined
      };

      // Call WASM transpiler (synchronous call after async initialization)
      const result: WasmTranspileResult = this.transpilerInstance.transpile(source, wasmOptions);

      console.log('✅ @hupyy/cpptoc-wasm transpilation complete', {
        success: result.success,
        cLength: result.c?.length || 0,
        hLength: result.h?.length || 0,
        acslLength: result.acsl?.length || 0,
        diagnosticsCount: result.diagnostics?.length || 0
      });

      // Map WASM result to interface result
      const diagnostics = result.diagnostics.map(d => ({
        line: d.line || 0,
        column: d.column || 0,
        message: d.message,
        severity: d.severity as 'error' | 'warning' | 'info'
      }));

      return {
        success: result.success,
        cCode: result.c,
        hCode: result.h,
        acslCode: result.acsl,
        diagnostics,
        sourcePath: options?.sourcePath
      };
    } catch (error) {
      console.error('❌ WASM transpilation error:', error);

      return {
        success: false,
        error: error instanceof Error ? error.message : 'Unknown transpilation error',
        sourcePath: options?.sourcePath
      };
    }
  }

  /**
   * Validate C++ source code using WASM module
   *
   * Note: WASM doesn't have separate validation endpoint.
   * We transpile and check for errors.
   *
   * @param source - C++ source code
   * @returns Validation result
   */
  async validateInput(source: string): Promise<ValidationResult> {
    try {
      // Transpile and check for errors
      const result = await this.transpile(source);

      // Helper to check if diagnostic is a Diagnostic object (not string)
      const isDiagnosticObject = (d: unknown): d is import('../core/interfaces/types').Diagnostic => {
        return typeof d === 'object' && d !== null && 'severity' in d;
      };

      const errors = result.diagnostics
        ?.filter(isDiagnosticObject)
        .filter(d => d.severity === 'error')
        .map(d => `Line ${d.line}:${d.column}: ${d.message}`) || [];

      const warnings = result.diagnostics
        ?.filter(isDiagnosticObject)
        .filter(d => d.severity === 'warning')
        .map(d => `Line ${d.line}:${d.column}: ${d.message}`) || [];

      return {
        valid: errors.length === 0,
        errors,
        warnings
      };
    } catch (error) {
      return {
        valid: false,
        errors: [error instanceof Error ? error.message : 'Validation failed']
      };
    }
  }

  /**
   * Clean up WASM resources
   *
   * Call this when the adapter is no longer needed.
   * Important for memory management in long-running browser sessions.
   */
  dispose(): void {
    if (this.transpilerInstance) {
      console.log('🧹 Disposing WASM transpiler instance');
      this.transpilerInstance.delete();
      this.transpilerInstance = null;
    }
    this.wasmModule = null;
    this.initPromise = null;
  }
}
