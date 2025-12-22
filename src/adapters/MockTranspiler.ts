/**
 * MockTranspiler - Mock Transpilation Engine
 *
 * Test implementation of ITranspiler that returns synthetic C code.
 * Used for unit testing without calling real transpiler backend.
 *
 * Following SOLID principles:
 * - Single Responsibility: Only provides mock transpilation
 * - Liskov Substitution: Can replace any ITranspiler implementation
 */

import type { ITranspiler } from '../core/interfaces/ITranspiler';
import type {
  TranspileOptions,
  TranspileResult,
  ValidationResult,
} from '../core/interfaces/types';

/**
 * Mock transpiler for testing
 */
export class MockTranspiler implements ITranspiler {
  /**
   * Transpile C++ source to mock C code
   */
  async transpile(
    source: string,
    options?: TranspileOptions
  ): Promise<TranspileResult> {
    // Handle empty input
    if (!source || source.trim() === '') {
      return {
        success: false,
        error: 'Empty source code',
        sourcePath: options?.sourcePath,
      };
    }

    // Simulate validation
    const validation = await this.validateInput(source);

    if (!validation.valid) {
      return {
        success: false,
        error: validation.errors?.[0] || 'Invalid C++ code',
        diagnostics: validation.errors,
        sourcePath: options?.sourcePath,
      };
    }

    // Generate mock C code
    const cCode = this.generateMockCCode(source, options);

    return {
      success: true,
      cCode,
      diagnostics: validation.warnings || [],
      sourcePath: options?.sourcePath,
    };
  }

  /**
   * Validate C++ source code
   */
  async validateInput(source: string): Promise<ValidationResult> {
    const errors: string[] = [];
    const warnings: string[] = [];

    // Simple validation logic for testing
    if (source.includes('this is not valid C++')) {
      errors.push('Syntax error: Invalid C++ syntax');
    }

    // Check for unused variables (warning)
    if (source.includes('int unused')) {
      warnings.push('Warning: Unused variable "unused"');
    }

    return {
      valid: errors.length === 0,
      errors: errors.length > 0 ? errors : undefined,
      warnings: warnings.length > 0 ? warnings : undefined,
    };
  }

  /**
   * Generate mock C code from C++ source
   * @private
   */
  private generateMockCCode(
    source: string,
    options?: TranspileOptions
  ): string {
    // Remove C++ includes and replace with C equivalents
    let cCode = source.replace(/#include <iostream>/g, '#include <stdio.h>');

    // Add comment indicating this is mock output
    const header = `/* Transpiled from C++ to C (Mock) */\n`;
    const standardComment = options?.targetStandard
      ? `/* Target: ${options.targetStandard} */\n`
      : '';

    cCode = header + standardComment + cCode;

    // If ACSL annotations are requested (default true)
    if (options?.includeACSL !== false) {
      cCode = `/*@ ensures \\result == 0; */\n` + cCode;
    }

    return cCode;
  }

  /**
   * Test helper: Set custom transpilation behavior
   */
  setCustomBehavior(
    fn: (source: string, options?: TranspileOptions) => Promise<TranspileResult>
  ): void {
    this.transpile = fn;
  }

  /**
   * Test helper: Set custom validation behavior
   */
  setCustomValidation(
    fn: (source: string) => Promise<ValidationResult>
  ): void {
    this.validateInput = fn;
  }
}
