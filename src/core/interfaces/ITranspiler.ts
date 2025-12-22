/**
 * ITranspiler - Transpilation Engine Abstraction Interface
 *
 * Provides abstraction for C++ to C transpilation to enable testing
 * and support multiple backends (WASM module, server-side API, mock).
 *
 * Following SOLID principles:
 * - Interface Segregation: Focused on transpilation operations only
 * - Dependency Inversion: Services depend on this abstraction
 */

import type { TranspileOptions, TranspileResult, ValidationResult } from './types';

/**
 * Transpilation engine abstraction
 */
export interface ITranspiler {
  /**
   * Transpile C++ source code to C
   *
   * @param source - C++ source code
   * @param options - Transpilation options
   * @returns Transpilation result with success/error and generated C code
   */
  transpile(source: string, options?: TranspileOptions): Promise<TranspileResult>;

  /**
   * Validate C++ source code without transpiling
   *
   * @param source - C++ source code
   * @returns Validation result with errors/warnings
   */
  validateInput(source: string): Promise<ValidationResult>;
}
