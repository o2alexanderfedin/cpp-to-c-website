/**
 * WasmTranspilerAdapter - WebAssembly-Based Transpiler Adapter
 *
 * Implements ITranspiler interface by loading and using the actual WASM module.
 * NO BACKEND - transpilation runs entirely in the browser!
 *
 * Following SOLID principles:
 * - Single Responsibility: WASM module loading and transpilation only
 * - Open/Closed: Can extend with caching without modifying core
 * - Liskov Substitution: Substitutable for any ITranspiler implementation
 * - Interface Segregation: Implements only ITranspiler methods
 * - Dependency Inversion: Depends on ITranspiler abstraction
 */

import type { ITranspiler } from '../core/interfaces/ITranspiler';
import type { TranspileOptions, TranspileResult, ValidationResult } from '../core/interfaces/types';

/**
 * Extended WASM types with header field support (Phase 28)
 * TODO: Update @hupyy/cpptoc-wasm types to include h field
 */
interface WasmTranspileResult {
  success: boolean;
  c: string;
  h: string;
  acsl: string;
  diagnostics: Array<{
    line: number;
    column: number;
    message: string;
    severity: 'error' | 'warning' | 'note';
  }>;
}

interface WasmTranspileOptions {
  acsl?: {
    statements?: boolean;
    typeInvariants?: boolean;
    axiomatics?: boolean;
    ghostCode?: boolean;
    behaviors?: boolean;
  };
  target?: 'c89' | 'c99' | 'c11' | 'c17';
  optimize?: boolean;
}

interface WasmTranspilerInstance {
  transpile(code: string, options: WasmTranspileOptions): WasmTranspileResult;
  getVersion(): string;
  delete(): void;
}

interface WasmModule {
  Transpiler: new () => WasmTranspilerInstance;
}

interface CreateModuleOptions {
  locateFile?: (path: string, prefix?: string) => string;
  onRuntimeInitialized?: () => void;
}

type CreateCppToCModule = (options?: CreateModuleOptions) => Promise<WasmModule>;

/**
 * WebAssembly-based transpiler adapter
 *
 * Loads the actual WASM module and runs transpilation in the browser.
 * NO HTTP calls, NO backend dependency!
 */
export class WasmTranspilerAdapter implements ITranspiler {
  private module: WasmModule | null = null;
  private transpiler: WasmTranspilerInstance | null = null;
  private initPromise: Promise<void> | null = null;

  /**
   * Create WASM transpiler adapter
   *
   * Module is lazy-loaded on first transpile() call.
   */
  constructor() {
    console.log('✅ WasmTranspilerAdapter initializing (WASM module will load on first use)');
  }

  /**
   * Initialize WASM module (lazy loaded on first use)
   *
   * @throws Error if WASM module fails to load
   */
  private async initialize(): Promise<void> {
    // Already initialized
    if (this.module && this.transpiler) {
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
        console.log('⏳ Loading WASM module from @hupyy/cpptoc-wasm/full...');

        // Dynamically import the WASM module
        const createCppToC = (await import('@hupyy/cpptoc-wasm/full')).default as CreateCppToCModule;

        // Create WASM module instance with locateFile to fix 404 errors
        // WASM files are served from public/wasm/ directory
        this.module = await createCppToC({
          locateFile: (path: string) => {
            // Direct WASM file requests to public/wasm/ directory
            if (path.endsWith('.wasm')) {
              const baseUrl = import.meta.env.BASE_URL || '/';
              // Ensure proper slash handling - baseUrl may or may not end with /
              const normalizedBase = baseUrl.endsWith('/') ? baseUrl : `${baseUrl}/`;
              const wasmPath = `${normalizedBase}wasm/${path}`;
              console.log(`📍 Locating WASM file: ${path} → ${wasmPath}`);
              return wasmPath;
            }
            return path;
          }
        });

        // Create transpiler instance
        this.transpiler = new this.module.Transpiler();

        console.log('✅ WASM module loaded successfully');
        console.log(`📦 Transpiler version: ${this.transpiler.getVersion()}`);
      } catch (error) {
        console.error('❌ Failed to load WASM module:', error);
        this.initPromise = null; // Allow retry
        throw new Error(
          `Failed to initialize WASM transpiler: ${error instanceof Error ? error.message : 'Unknown error'}`
        );
      }
    })();

    await this.initPromise;
  }

  /**
   * Transpile C++ source code to C using WASM module
   *
   * @param source - C++ source code
   * @param options - Transpilation options
   * @returns Transpilation result
   */
  async transpile(source: string, options?: TranspileOptions): Promise<TranspileResult> {
    try {
      // Ensure WASM is initialized
      await this.initialize();

      if (!this.transpiler) {
        throw new Error('WASM transpiler not initialized');
      }

      // Map options to WASM format
      const wasmOptions: WasmTranspileOptions = {
        acsl: options?.acsl || {
          statements: false,
          typeInvariants: false,
          axiomatics: false,
          ghostCode: false,
          behaviors: false
        },
        target: (options?.target as 'c89' | 'c99' | 'c11' | 'c17') || 'c99',
        optimize: options?.optimize || false
      };

      console.log('🔄 Transpiling with WASM module...', {
        sourceLength: source.length,
        target: wasmOptions.target,
        acslEnabled: Object.values(wasmOptions.acsl || {}).some(v => v)
      });

      // Call REAL WASM transpiler!
      const result = this.transpiler.transpile(source, wasmOptions);

      console.log('✅ WASM transpilation complete', {
        success: result.success,
        cLength: result.c?.length || 0,
        hLength: result.h?.length || 0,
        acslLength: result.acsl?.length || 0,
        diagnosticsCount: result.diagnostics?.length || 0
      });

      // Convert diagnostics from Emscripten vector to JS array
      const diagnostics: Array<{line: number; column: number; message: string; severity: string}> = [];
      if (result.diagnostics && typeof result.diagnostics === 'object') {
        // Emscripten vector has size() and get(index) methods
        const diagVec = result.diagnostics as any;
        if (typeof diagVec.size === 'function') {
          const size = diagVec.size();
          for (let i = 0; i < size; i++) {
            const d = diagVec.get(i);
            diagnostics.push({
              line: d.line,
              column: d.column,
              message: d.message,
              severity: d.severity as 'error' | 'warning' | 'note'
            });
          }
        }
      }

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

      const errors = result.diagnostics
        ?.filter(d => d.severity === 'error')
        .map(d => `Line ${d.line}:${d.column}: ${d.message}`) || [];

      const warnings = result.diagnostics
        ?.filter(d => d.severity === 'warning')
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
    if (this.transpiler) {
      console.log('🧹 Disposing WASM transpiler instance');
      this.transpiler.delete();
      this.transpiler = null;
    }
    this.module = null;
    this.initPromise = null;
  }
}
