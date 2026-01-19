/**
 * BackendTranspilerAdapter - HTTP Client for Backend Transpilation API
 *
 * Implements ITranspiler interface by delegating to server-side transpiler.
 * Handles HTTP communication, error mapping, and response parsing.
 *
 * Following SOLID principles:
 * - Single Responsibility: HTTP communication with backend only
 * - Open/Closed: Can extend with retry logic without modifying core
 * - Liskov Substitution: Substitutable for any ITranspiler implementation
 * - Interface Segregation: Implements only ITranspiler methods
 * - Dependency Inversion: Depends on ITranspiler abstraction
 */

import type { ITranspiler } from '../core/interfaces/ITranspiler';
import type { TranspileOptions, TranspileResult, ValidationResult } from '../core/interfaces/types';

/**
 * Backend API response for transpilation
 */
interface BackendTranspileResponse {
  success: boolean;
  cCode?: string;
  error?: string;
  diagnostics?: string[];
}

/**
 * Backend API response for validation
 */
interface BackendValidationResponse {
  valid: boolean;
  errors?: string[];
  warnings?: string[];
}

/**
 * Backend transpiler adapter using HTTP API
 */
export class BackendTranspilerAdapter implements ITranspiler {
  private readonly apiUrl: string;

  /**
   * Create backend transpiler adapter
   *
   * @param apiUrl - Base URL of backend API (e.g., 'https://api.example.com')
   */
  constructor(apiUrl: string) {
    // Normalize URL: remove trailing slash
    this.apiUrl = apiUrl.endsWith('/') ? apiUrl.slice(0, -1) : apiUrl;
  }

  /**
   * Transpile C++ source code to C using backend API
   *
   * @param source - C++ source code
   * @param options - Transpilation options
   * @returns Transpilation result
   */
  async transpile(source: string, options?: TranspileOptions): Promise<TranspileResult> {
    try {
      const response = await fetch(`${this.apiUrl}/api/transpile`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json'
        },
        body: JSON.stringify({
          source,
          options: options || {}
        })
      });

      if (!response.ok) {
        const errorData = await response.json().catch(() => ({}));
        const errorMessage = errorData.error
          ? `${errorData.error} (${response.status})`
          : `Server error: ${response.status} ${response.statusText}`;

        return {
          success: false,
          error: errorMessage,
          sourcePath: options?.sourcePath
        };
      }

      const data: BackendTranspileResponse = await response.json();

      return {
        success: data.success,
        cCode: data.cCode,
        error: data.error,
        diagnostics: data.diagnostics,
        sourcePath: options?.sourcePath
      };
    } catch (error) {
      // Handle network errors, timeouts, JSON parsing errors
      const errorMessage = this.mapErrorToMessage(error);

      return {
        success: false,
        error: errorMessage,
        sourcePath: options?.sourcePath
      };
    }
  }

  /**
   * Validate C++ source code using backend API
   *
   * @param source - C++ source code
   * @returns Validation result
   */
  async validateInput(source: string): Promise<ValidationResult> {
    try {
      const response = await fetch(`${this.apiUrl}/api/validate`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json'
        },
        body: JSON.stringify({ source })
      });

      if (!response.ok) {
        const errorData = await response.json().catch(() => ({}));
        const errorMessage = errorData.error || `Server error: ${response.status} ${response.statusText}`;

        return {
          valid: false,
          errors: [errorMessage]
        };
      }

      const data: BackendValidationResponse = await response.json();

      return {
        valid: data.valid,
        errors: data.errors || [],
        warnings: data.warnings || []
      };
    } catch (error) {
      // Handle network errors
      const errorMessage = this.mapErrorToMessage(error);

      return {
        valid: false,
        errors: [errorMessage]
      };
    }
  }

  /**
   * Map various error types to user-friendly messages
   *
   * @param error - Error from fetch or JSON parsing
   * @returns User-friendly error message
   */
  private mapErrorToMessage(error: unknown): string {
    // Handle DOMException (which may or may not extend Error in all environments)
    if (error && typeof error === 'object' && 'name' in error && error.name === 'AbortError') {
      return 'Request timeout';
    }

    if (error instanceof Error) {
      // Handle timeout in message
      if (error.message.toLowerCase().includes('timeout')) {
        return `Request timeout: ${error.message}`;
      }

      // Handle network errors
      if (error.message.toLowerCase().includes('network')) {
        return 'Network error';
      }

      // Handle JSON parsing errors
      if (error.message.includes('JSON')) {
        return `Invalid JSON response: ${error.message}`;
      }

      // Generic error
      return error.message;
    }

    return 'Unknown error occurred';
  }
}
