/**
 * WasmTranspilerAdapter - HTTP-Based Transpiler Adapter
 *
 * Implements ITranspiler interface by using HTTP API for transpilation.
 * Originally designed for WASM, now delegates to backend API.
 *
 * NOTE: This adapter has been updated to use HTTP API instead of WebAssembly
 * because compiling Clang to WASM would result in 100MB+ bundle size.
 * Backend API provides real transpilation functionality.
 *
 * Following SOLID principles:
 * - Single Responsibility: HTTP communication with backend only
 * - Open/Closed: Can extend with caching/retry without modifying core
 * - Liskov Substitution: Substitutable for any ITranspiler implementation
 * - Interface Segregation: Implements only ITranspiler methods
 * - Dependency Inversion: Depends on ITranspiler abstraction
 */

import type { ITranspiler } from '../core/interfaces/ITranspiler';
import type { TranspileOptions, TranspileResult, ValidationResult } from '../core/interfaces/types';
import type { TranspileRequest, TranspileResponse, ValidateRequest, ValidateResponse, ApiErrorResponse } from '../types/transpiler';
import { getApiBaseUrl, getApiTimeout } from '../config/api';

/**
 * HTTP-based transpiler adapter (formerly WASM)
 *
 * Maintains same interface as WASM adapter for backward compatibility.
 * Uses backend API for actual transpilation.
 */
export class WasmTranspilerAdapter implements ITranspiler {
  private readonly apiUrl: string;
  private readonly timeout: number;
  private abortController: AbortController | null = null;

  /**
   * Create HTTP transpiler adapter
   *
   * Uses environment-based API configuration.
   */
  constructor() {
    this.apiUrl = getApiBaseUrl();
    this.timeout = getApiTimeout();
    console.log(`✅ WasmTranspilerAdapter initialized with API: ${this.apiUrl}`);
  }

  /**
   * Transpile C++ source code to C using HTTP API
   *
   * @param source - C++ source code
   * @param options - Transpilation options
   * @returns Transpilation result
   */
  async transpile(source: string, options?: TranspileOptions): Promise<TranspileResult> {
    try {
      // Create abort controller for timeout
      this.abortController = new AbortController();
      const timeoutId = setTimeout(() => {
        this.abortController?.abort();
      }, this.timeout);

      try {
        // Prepare request
        const request: TranspileRequest = {
          source,
          options: options || {}
        };

        // Make HTTP request
        const response = await fetch(`${this.apiUrl}/api/transpile`, {
          method: 'POST',
          headers: {
            'Content-Type': 'application/json'
          },
          body: JSON.stringify(request),
          signal: this.abortController.signal
        });

        // Clear timeout
        clearTimeout(timeoutId);

        // Handle HTTP errors
        if (!response.ok) {
          const errorData: ApiErrorResponse = await response.json().catch(() => ({
            error: `Server error: ${response.status} ${response.statusText}`
          }));

          const errorMessage = errorData.error
            ? `${errorData.error} (HTTP ${response.status})`
            : `Server error: ${response.status} ${response.statusText}`;

          return {
            success: false,
            error: errorMessage,
            sourcePath: options?.sourcePath
          };
        }

        // Parse response
        const data: TranspileResponse = await response.json();

        // Debug log
        console.log('HTTP transpile result:', {
          success: data.success,
          hasCCode: !!data.cCode,
          hasHCode: !!data.hCode,
          codeLength: data.cCode?.length || 0,
          headerLength: data.hCode?.length || 0,
          diagnosticsCount: data.diagnostics?.length || 0
        });

        return {
          success: data.success,
          cCode: data.cCode,
          hCode: data.hCode,
          error: data.error,
          diagnostics: data.diagnostics,
          sourcePath: options?.sourcePath
        };
      } finally {
        clearTimeout(timeoutId);
        this.abortController = null;
      }
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
   * Validate C++ source code using HTTP API
   *
   * @param source - C++ source code
   * @returns Validation result
   */
  async validateInput(source: string): Promise<ValidationResult> {
    try {
      // Create abort controller for timeout
      this.abortController = new AbortController();
      const timeoutId = setTimeout(() => {
        this.abortController?.abort();
      }, this.timeout);

      try {
        // Prepare request
        const request: ValidateRequest = {
          source
        };

        // Make HTTP request
        const response = await fetch(`${this.apiUrl}/api/validate`, {
          method: 'POST',
          headers: {
            'Content-Type': 'application/json'
          },
          body: JSON.stringify(request),
          signal: this.abortController.signal
        });

        // Clear timeout
        clearTimeout(timeoutId);

        // Handle HTTP errors
        if (!response.ok) {
          const errorData: ApiErrorResponse = await response.json().catch(() => ({
            error: `Server error: ${response.status} ${response.statusText}`
          }));

          const errorMessage = errorData.error || `Server error: ${response.status} ${response.statusText}`;

          return {
            valid: false,
            errors: [errorMessage]
          };
        }

        // Parse response
        const data: ValidateResponse = await response.json();

        return {
          valid: data.valid,
          errors: data.errors || [],
          warnings: data.warnings || []
        };
      } finally {
        clearTimeout(timeoutId);
        this.abortController = null;
      }
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
    if (error instanceof Error) {
      // Handle abort/timeout errors
      if (error.name === 'AbortError') {
        return `Request timeout after ${this.timeout / 1000} seconds`;
      }

      // Handle timeout in message
      if (error.message.toLowerCase().includes('timeout')) {
        return `Request timeout: ${error.message}`;
      }

      // Handle network errors
      if (error.message.toLowerCase().includes('network') || error.message.toLowerCase().includes('fetch')) {
        return `Network error: Cannot connect to transpiler API at ${this.apiUrl}`;
      }

      // Handle JSON parsing errors
      if (error.message.includes('JSON')) {
        return `Invalid response from server: ${error.message}`;
      }

      // Generic error
      return `Transpilation failed: ${error.message}`;
    }

    // Handle DOMException (like AbortError)
    if (error instanceof DOMException) {
      if (error.name === 'AbortError') {
        return `Request timeout after ${this.timeout / 1000} seconds`;
      }
    }

    return 'Unknown error occurred during transpilation';
  }

  /**
   * Cancel ongoing request
   *
   * Aborts the current HTTP request if one is in progress
   */
  cancel(): void {
    if (this.abortController) {
      this.abortController.abort();
      this.abortController = null;
    }
  }

  /**
   * Clean up resources
   *
   * Call this when the adapter is no longer needed
   */
  dispose(): void {
    this.cancel();
  }
}
