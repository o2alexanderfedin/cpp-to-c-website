/**
 * WASM Transpiler API Wrapper
 *
 * Provides a type-safe, Result-based API for transpilation.
 * No exceptions for expected errors, only for programming bugs.
 *
 * Following SOLID principles:
 * - Single Responsibility: API wrapper only
 * - Open/Closed: Can extend with new operations
 * - Liskov Substitution: Result pattern ensures consistent behavior
 * - Dependency Inversion: Depends on WASM module interface
 */

import type {
  TranspileOptions as WasmOptions,
  TranspileResult as WasmResult,
  Diagnostic,
  WASMModule
} from '@hupyy/cpptoc-wasm';
import { wasmLoader } from './loader';

/**
 * Transpilation success result
 */
export interface TranspileSuccess {
  success: true;
  /** C source code (.c file) */
  cCode: string;
  /** C header code (.h file) */
  hCode: string;
  /** ACSL annotations (if enabled) */
  acslCode: string;
  /** Compilation diagnostics (warnings, notes) */
  diagnostics: Diagnostic[];
  /** Missing headers (if any) */
  missingHeaders?: string[];
}

/**
 * Transpilation error result
 */
export interface TranspileError {
  success: false;
  /** Error message */
  error: string;
  /** Compilation diagnostics (errors, warnings) */
  diagnostics: Diagnostic[];
  /** Missing headers (if any) */
  missingHeaders?: string[];
}

/**
 * Transpilation result (discriminated union)
 */
export type TranspileResult = TranspileSuccess | TranspileError;

/**
 * Simplified transpilation options
 */
export interface TranspileOptions {
  /** Target C standard */
  target?: 'c89' | 'c99' | 'c11' | 'c17';
  /** Enable ACSL annotations */
  enableACSL?: boolean;
  /** Optimization level */
  optimize?: boolean;
  /** C++ standard version */
  cppStandard?: 11 | 14 | 17 | 20;
}

/**
 * Transpile C++ code to C
 *
 * Returns Result type (no exceptions for expected errors).
 *
 * @param code - C++ source code
 * @param options - Transpilation options
 * @returns Promise resolving to TranspileResult
 *
 * @example
 * ```ts
 * const result = await transpile('int main() { return 0; }');
 * if (result.success) {
 *   console.log(result.cCode);
 * } else {
 *   console.error(result.error);
 * }
 * ```
 */
export async function transpile(
  code: string,
  options?: TranspileOptions
): Promise<TranspileResult> {
  try {
    // Ensure WASM module is loaded
    const module = await wasmLoader.load();

    // Create transpiler instance
    const transpiler = new module.Transpiler();

    try {
      // Map simplified options to WASM options
      const wasmOptions: WasmOptions = {
        target: options?.target,
        optimize: options?.optimize,
        enableACSL: options?.enableACSL,
        cppStandard: options?.cppStandard
      };

      // Transpile
      const wasmResult: WasmResult = transpiler.transpile(code, wasmOptions);

      // Map WASM result to API result
      if (wasmResult.success) {
        return {
          success: true,
          cCode: wasmResult.c,
          hCode: wasmResult.h,
          acslCode: wasmResult.acsl,
          diagnostics: wasmResult.diagnostics,
          missingHeaders: wasmResult.missingHeaders
        };
      } else {
        // Transpilation failed
        return {
          success: false,
          error: extractErrorMessage(wasmResult),
          diagnostics: wasmResult.diagnostics,
          missingHeaders: wasmResult.missingHeaders
        };
      }
    } finally {
      // Always clean up instance
      transpiler.delete();
    }
  } catch (error) {
    // Unexpected error (WASM loading, instance creation, etc.)
    return {
      success: false,
      error: error instanceof Error ? error.message : String(error),
      diagnostics: []
    };
  }
}

/**
 * Transpile multiple files in sequence
 *
 * @param files - Map of filename -> source code
 * @param options - Transpilation options
 * @returns Promise resolving to Map of filename -> result
 *
 * @example
 * ```ts
 * const files = new Map([
 *   ['main.cpp', 'int main() { return 0; }'],
 *   ['utils.cpp', 'int add(int a, int b) { return a + b; }']
 * ]);
 *
 * const results = await transpileFiles(files);
 * for (const [filename, result] of results) {
 *   if (result.success) {
 *     console.log(`${filename}: OK`);
 *   } else {
 *     console.error(`${filename}: ${result.error}`);
 *   }
 * }
 * ```
 */
export async function transpileFiles(
  files: Map<string, string>,
  options?: TranspileOptions
): Promise<Map<string, TranspileResult>> {
  const results = new Map<string, TranspileResult>();

  // Ensure WASM module is loaded once
  const module = await wasmLoader.load();

  // Create single transpiler instance for all files
  const transpiler = new module.Transpiler();

  try {
    // Transpile each file
    for (const [filename, code] of files) {
      try {
        const wasmOptions: WasmOptions = {
          target: options?.target,
          optimize: options?.optimize,
          enableACSL: options?.enableACSL,
          cppStandard: options?.cppStandard
        };

        const wasmResult: WasmResult = transpiler.transpile(code, wasmOptions);

        if (wasmResult.success) {
          results.set(filename, {
            success: true,
            cCode: wasmResult.c,
            hCode: wasmResult.h,
            acslCode: wasmResult.acsl,
            diagnostics: wasmResult.diagnostics,
            missingHeaders: wasmResult.missingHeaders
          });
        } else {
          results.set(filename, {
            success: false,
            error: extractErrorMessage(wasmResult),
            diagnostics: wasmResult.diagnostics,
            missingHeaders: wasmResult.missingHeaders
          });
        }
      } catch (error) {
        results.set(filename, {
          success: false,
          error: error instanceof Error ? error.message : String(error),
          diagnostics: []
        });
      }
    }
  } finally {
    // Clean up instance
    transpiler.delete();
  }

  return results;
}

/**
 * Extract error message from WASM result
 */
function extractErrorMessage(result: WasmResult): string {
  // Look for error diagnostics first
  const errors = result.diagnostics.filter(d => d.severity === 'error');
  if (errors.length > 0) {
    return errors.map(e => `Line ${e.line}:${e.column}: ${e.message}`).join('\n');
  }

  // Fallback to generic message
  return 'Transpilation failed';
}

/**
 * Check if transpiler is ready (module loaded)
 */
export function isTranspilerReady(): boolean {
  const state = wasmLoader.getState();
  return state.status === 'ready';
}

/**
 * Get transpiler version
 *
 * Returns null if module not loaded.
 */
export async function getVersion(): Promise<string | null> {
  try {
    const module = await wasmLoader.load();
    const transpiler = new module.Transpiler();
    const version = transpiler.getVersion();
    transpiler.delete();
    return version;
  } catch {
    return null;
  }
}
