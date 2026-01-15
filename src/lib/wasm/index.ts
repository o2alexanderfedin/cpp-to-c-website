/**
 * WASM Module - Public API
 *
 * Exports all public APIs for WASM transpiler integration
 */

// Loader
export { wasmLoader, loadWasmModule, getLoaderState } from './loader';
export type { LoaderState, LoaderListener } from './loader';

// React hooks
export { useWasmModule, useTranspiler, useWasmLoadingState } from './hooks.js';
export type {
  UseWasmModuleResult,
  UseTranspilerResult,
  WasmLoadingStateProps
} from './hooks.js';

// API wrapper
export { transpile, transpileFiles, isTranspilerReady, getVersion } from './api';
export type {
  TranspileResult,
  TranspileSuccess,
  TranspileError,
  TranspileOptions
} from './api';

// Types
export type {
  Diagnostic,
  ACSLOptions,
  WasmTranspileOptions,
  WasmTranspileResult,
  WASMModule,
  TranspilerInstance,
  CreateModuleOptions,
  CreateCppToCModule,
  HeaderProvider,
  WasmLoadingState,
  DiagnosticSeverity,
  CStandard,
  CppStandard
} from './types';

export {
  DEFAULT_ACSL_OPTIONS,
  DEFAULT_TRANSPILE_OPTIONS,
  hasErrors,
  getErrors,
  getWarnings,
  formatDiagnostic
} from './types';
