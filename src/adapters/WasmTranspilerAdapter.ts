/**
 * WasmTranspilerAdapter - WebAssembly Transpiler Adapter
 *
 * Implements ITranspiler interface by using the compiled WebAssembly transpiler.
 * Provides browser-based C++ to C transpilation without backend API.
 *
 * Following SOLID principles:
 * - Single Responsibility: WASM module initialization and communication only
 * - Open/Closed: Can extend with caching without modifying core
 * - Liskov Substitution: Substitutable for any ITranspiler implementation
 * - Interface Segregation: Implements only ITranspiler methods
 * - Dependency Inversion: Depends on ITranspiler abstraction
 */

import type { ITranspiler } from '../core/interfaces/ITranspiler';
import type { TranspileOptions, TranspileResult, ValidationResult } from '../core/interfaces/types';

// WASM module types (will be imported when package is added)
type WASMModule = any;
type TranspilerInstance = any;
type CreateCppToCModule = any;

/**
 * WebAssembly transpiler adapter
 */
export class WasmTranspilerAdapter implements ITranspiler {
  private module: WASMModule | null = null;
  private transpilerInstance: TranspilerInstance | null = null;
  private initPromise: Promise<void> | null = null;

  /**
   * Create WASM transpiler adapter
   *
   * The WASM module is loaded lazily on first use
   */
  constructor() {
    // Lazy initialization - module will be loaded on first transpile() call
  }

  /**
   * Initialize the WASM module
   *
   * @returns Promise that resolves when module is ready
   */
  private async initialize(): Promise<void> {
    if (this.module && this.transpilerInstance) {
      return; // Already initialized
    }

    if (this.initPromise) {
      return this.initPromise; // Already initializing
    }

    this.initPromise = (async () => {
      try {
        // Load the WASM module from public directory
        // The files are in public/wasm/ which maps to /cpp-to-c-website/wasm/ with base path
        // Determine base URL from current location
        // Use self.location instead of window.location to work in both main thread and workers
        const baseUrl = self.location.pathname.includes('/cpp-to-c-website/')
          ? '/cpp-to-c-website/'
          : '/';
        const wasmJsPath = `${baseUrl}wasm/cpptoc.js`;

        // Dynamically import the Emscripten module as an ES module
        // We need to create a blob URL to import it
        const response = await fetch(wasmJsPath);
        if (!response.ok) {
          throw new Error(`Failed to load WASM module: ${response.status} ${response.statusText}`);
        }

        const jsCode = await response.text();

        // Create a blob URL for the module
        const blob = new Blob([jsCode], { type: 'application/javascript' });
        const blobUrl = URL.createObjectURL(blob);

        try {
          // Import the module
          const wasmModule = await import(/* @vite-ignore */ blobUrl);
          const createCppToC = wasmModule.default;

          // Create the WASM module instance
          this.module = await createCppToC({
            locateFile: (path: string) => {
              // WASM file is in same directory as JS file
              return `${baseUrl}wasm/${path}`;
            }
          });

          // Check if Transpiler class exists
          if (!this.module.Transpiler) {
            console.error('WASM module structure:', Object.keys(this.module));
            throw new Error('WASM module does not export Transpiler class');
          }

          // Create transpiler instance
          this.transpilerInstance = new this.module.Transpiler();
          console.log('✅ WASM Transpiler initialized successfully');
        } finally {
          // Clean up blob URL
          URL.revokeObjectURL(blobUrl);
        }
      } catch (error) {
        this.initPromise = null; // Reset so we can retry
        throw new Error(
          `Failed to initialize WASM transpiler: ${error instanceof Error ? error.message : String(error)}`
        );
      }
    })();

    return this.initPromise;
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
      // Ensure WASM module is initialized
      await this.initialize();

      if (!this.transpilerInstance) {
        throw new Error('WASM transpiler not initialized');
      }

      // Map website options to WASM options
      const wasmOptions = {
        target: options?.targetStandard || 'c99',
        acsl: options?.includeACSL !== false ? {
          statements: true,
          typeInvariants: true,
          axiomatics: false,
          ghostCode: false,
          behaviors: true
        } : {
          // WASM requires acsl field to be present, not undefined
          statements: false,
          typeInvariants: false,
          axiomatics: false,
          ghostCode: false,
          behaviors: false
        },
        optimize: false,
        cppStandard: 17 // Default C++ standard
      };

      // Call WASM transpiler
      const wasmResult = this.transpilerInstance.transpile(source, wasmOptions);

      // Debug: Log WASM result structure
      console.log('WASM transpile result:', {
        success: wasmResult.success,
        hasC: !!wasmResult.c,
        hasCCode: !!wasmResult.cCode,
        cLength: wasmResult.c?.length || wasmResult.cCode?.length || 0,
        keys: Object.keys(wasmResult)
      });

      // Map WASM result to website result
      const diagnostics = Array.isArray(wasmResult.diagnostics)
        ? wasmResult.diagnostics.map((d: any) => this.formatDiagnostic(d))
        : [];

      // Try both .c and .cCode properties (WASM may use either)
      const cCode = wasmResult.c || wasmResult.cCode || wasmResult.output;

      if (!cCode && wasmResult.success) {
        console.warn('⚠️  WASM returned success but no C code. Result:', wasmResult);
      }

      return {
        success: wasmResult.success,
        cCode,
        error: wasmResult.success
          ? undefined
          : this.formatDiagnosticsAsError(wasmResult.diagnostics),
        diagnostics,
        sourcePath: options?.sourcePath
      };
    } catch (error) {
      // Handle WASM initialization or execution errors
      const errorMessage = error instanceof Error ? error.message : String(error);

      return {
        success: false,
        error: errorMessage,
        sourcePath: options?.sourcePath
      };
    }
  }

  /**
   * Validate C++ source code using WASM module
   *
   * @param source - C++ source code
   * @returns Validation result
   */
  async validateInput(source: string): Promise<ValidationResult> {
    try {
      // Use transpile for validation - it will parse and analyze the code
      const result = await this.transpile(source);

      return {
        valid: result.success,
        errors: result.success ? [] : [result.error || 'Validation failed'],
        warnings: result.diagnostics?.filter(d => !d.includes('[ERROR]')) || []
      };
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : String(error);

      return {
        valid: false,
        errors: [errorMessage]
      };
    }
  }

  /**
   * Format WASM diagnostic for display
   *
   * @param diagnostic - WASM diagnostic object
   * @returns Formatted diagnostic string
   */
  private formatDiagnostic(diagnostic: any): string {
    const location = diagnostic.line > 0
      ? `${diagnostic.line}:${diagnostic.column}`
      : 'global';
    return `[${diagnostic.severity.toUpperCase()}] ${location}: ${diagnostic.message}`;
  }

  /**
   * Format diagnostics array as a single error message
   *
   * @param diagnostics - Array of WASM diagnostics
   * @returns Combined error message
   */
  private formatDiagnosticsAsError(diagnostics: any[]): string {
    if (!diagnostics || diagnostics.length === 0) {
      return 'Transpilation failed';
    }

    const errors = diagnostics.filter(d => d.severity === 'error');
    if (errors.length === 0) {
      return 'Transpilation failed';
    }

    // Return first error message
    return this.formatDiagnostic(errors[0]);
  }

  /**
   * Clean up WASM resources
   *
   * Call this when the adapter is no longer needed
   */
  dispose(): void {
    if (this.transpilerInstance) {
      this.transpilerInstance.delete();
      this.transpilerInstance = null;
    }
    this.module = null;
    this.initPromise = null;
  }
}
