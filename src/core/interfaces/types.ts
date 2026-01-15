/**
 * Core Type Definitions for C++ to C Playground
 *
 * Shared types used across interfaces and implementations
 */

/**
 * ACSL annotation options
 */
export interface ACSLOptions {
  statements?: boolean;
  typeInvariants?: boolean;
  axiomatics?: boolean;
  ghostCode?: boolean;
  behaviors?: boolean;
}

/**
 * Options for transpilation
 */
export interface TranspileOptions {
  /**
   * Source file path (for error reporting)
   */
  sourcePath?: string;

  /**
   * Include ACSL annotations in output
   * @default true
   */
  includeACSL?: boolean;

  /**
   * Target C standard version
   * @default 'c99'
   */
  target?: 'c89' | 'c99' | 'c11' | 'c17';

  /**
   * @deprecated Use `target` instead
   */
  targetStandard?: 'c89' | 'c99' | 'c11' | 'c17';

  /**
   * Optimization flag
   */
  optimize?: boolean;

  /**
   * ACSL options (detailed)
   */
  acsl?: ACSLOptions;
}

/**
 * Diagnostic message
 */
export interface Diagnostic {
  line: number;
  column: number;
  message: string;
  severity: 'error' | 'warning' | 'info';
}

/**
 * Result of a transpilation operation
 */
export interface TranspileResult {
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
   * ACSL annotated code (if enabled)
   */
  acslCode?: string;

  /**
   * Error message (if failed)
   */
  error?: string;

  /**
   * Detailed diagnostics (warnings, notes, errors)
   * Can be either structured Diagnostic objects or simple strings for backward compatibility
   */
  diagnostics?: Diagnostic[] | string[];

  /**
   * Source file path (for error tracking)
   */
  sourcePath?: string;
}

/**
 * Validation result for input source code
 */
export interface ValidationResult {
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
 * Progress state for long-running operations
 */
export interface ProgressState {
  /**
   * Total number of items to process
   */
  total: number;

  /**
   * Number of items processed so far
   */
  current: number;

  /**
   * Current operation message
   */
  message?: string;

  /**
   * Percentage complete (0-100)
   */
  percentage: number;
}

/**
 * File information for directory traversal
 */
export interface FileInfo {
  /**
   * File path relative to root
   */
  path: string;

  /**
   * File name
   */
  name: string;

  /**
   * File size in bytes
   */
  size?: number;

  /**
   * Whether this is a directory
   */
  isDirectory: boolean;
}

/**
 * Directory handle abstraction
 */
export interface DirectoryHandle {
  /**
   * Directory name
   */
  name: string;

  /**
   * Directory path
   */
  path: string;
}

/**
 * File handle abstraction
 */
export interface FileHandle {
  /**
   * File name
   */
  name: string;

  /**
   * File path
   */
  path: string;
}
