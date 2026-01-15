/**
 * Type definitions for WASM module
 *
 * Re-exports and augments types from @hupyy/cpptoc-wasm
 */

// Re-export all types from WASM package
export type {
  Diagnostic,
  ACSLOptions,
  TranspileOptions as WasmTranspileOptions,
  TranspileResult as WasmTranspileResult,
  WASMModule,
  TranspilerInstance,
  CreateModuleOptions,
  CreateCppToCModule,
  HeaderProvider
} from '@hupyy/cpptoc-wasm';

// Re-export utility functions
export {
  DEFAULT_ACSL_OPTIONS,
  DEFAULT_TRANSPILE_OPTIONS,
  hasErrors,
  getErrors,
  getWarnings,
  formatDiagnostic
} from '@hupyy/cpptoc-wasm';

/**
 * WASM loading state
 */
export type WasmLoadingState =
  | 'idle'      // Not started
  | 'loading'   // Loading WASM module
  | 'ready'     // Module loaded and ready
  | 'error';    // Loading failed

/**
 * Severity levels for diagnostics
 */
export type DiagnosticSeverity = 'error' | 'warning' | 'note';

/**
 * C standard versions
 */
export type CStandard = 'c89' | 'c99' | 'c11' | 'c17';

/**
 * C++ standard versions
 */
export type CppStandard = 11 | 14 | 17 | 20;
