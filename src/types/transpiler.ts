/**
 * Shared Transpiler Types for HTTP API Communication
 *
 * Defines request/response types for HTTP API transpilation.
 * These types should match the backend API contract.
 *
 * Following SOLID principles:
 * - Single Responsibility: Type definitions only
 * - Interface Segregation: Separate types for requests and responses
 */

import type { TranspileOptions } from '../core/interfaces/types';

/**
 * Backend API request for transpilation
 */
export interface TranspileRequest {
  /**
   * C++ source code to transpile
   */
  source: string;

  /**
   * Transpilation options
   */
  options?: TranspileOptions;
}

/**
 * Backend API response for transpilation
 */
export interface TranspileResponse {
  /**
   * Whether transpilation succeeded
   */
  success: boolean;

  /**
   * Transpiled C implementation code (if successful)
   */
  cCode?: string;

  /**
   * Transpiled C header code (if successful)
   */
  hCode?: string;

  /**
   * Error message (if failed)
   */
  error?: string;

  /**
   * Detailed diagnostics (warnings, notes)
   */
  diagnostics?: string[];
}

/**
 * Backend API request for validation
 */
export interface ValidateRequest {
  /**
   * C++ source code to validate
   */
  source: string;
}

/**
 * Backend API response for validation
 */
export interface ValidateResponse {
  /**
   * Whether input is valid C++ code
   */
  valid: boolean;

  /**
   * Validation errors
   */
  errors?: string[];

  /**
   * Validation warnings
   */
  warnings?: string[];
}

/**
 * HTTP error response from backend API
 */
export interface ApiErrorResponse {
  /**
   * Error message
   */
  error: string;

  /**
   * Error code (optional)
   */
  code?: string;

  /**
   * Additional error details (optional)
   */
  details?: string;
}
