/**
 * WasmTranspilerAdapter - WebAssembly-Based Transpiler Adapter
 *
 * Implements ITranspiler interface using libclang.wasm for real C++ parsing.
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
import type { TranspileOptions, TranspileResult, ValidationResult } from '../core/interfaces/types';
import { SimpleTranspiler } from '../lib/simple-transpiler';

/**
 * WebAssembly-based transpiler adapter
 *
 * Uses libclang.wasm for real C++ parsing and runs transpilation in the browser.
 * NO HTTP calls, NO backend dependency!
 */
export class WasmTranspilerAdapter implements ITranspiler {
  private transpiler: SimpleTranspiler | null = null;
  private initPromise: Promise<void> | null = null;

  /**
   * Create WASM transpiler adapter
   *
   * Module is lazy-loaded on first transpile() call.
   */
  constructor() {
    console.log('✅ WasmTranspilerAdapter initializing (libclang.wasm will load on first use)');
  }

  /**
   * Initialize WASM module (lazy loaded on first use)
   *
   * @throws Error if WASM module fails to load
   */
  private async initialize(): Promise<void> {
    // Already initialized
    if (this.transpiler) {
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
        console.log('⏳ Loading libclang.wasm transpiler...');

        // Create and initialize transpiler
        this.transpiler = new SimpleTranspiler();
        await this.transpiler.initialize();

        console.log('✅ libclang.wasm transpiler ready');
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
   * Transpile C++ source code to C using libclang.wasm
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

      console.log('🔄 Transpiling with libclang.wasm...', {
        sourceLength: source.length,
        target: options?.target || 'c99'
      });

      // Call transpiler
      const result = await this.transpiler.transpile(source, {
        acsl: options?.acsl?.statements || options?.acsl?.typeInvariants || options?.acsl?.axiomatics,
        target: options?.target as 'c89' | 'c99' | 'c11' | 'c17',
        optimize: options?.optimize
      });

      console.log('✅ libclang.wasm transpilation complete', {
        success: result.success,
        cLength: result.c?.length || 0,
        hLength: result.h?.length || 0,
        acslLength: result.acsl?.length || 0,
        diagnosticsCount: result.diagnostics?.length || 0
      });

      // Map result to expected format
      const diagnostics = result.diagnostics.map(d => ({
        line: d.line || 0,
        column: d.column || 0,
        message: d.message,
        severity: d.severity
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
      this.transpiler.dispose();
      this.transpiler = null;
    }
    this.initPromise = null;
  }
}
