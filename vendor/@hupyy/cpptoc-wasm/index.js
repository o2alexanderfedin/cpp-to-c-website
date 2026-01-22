export * from './types.js';
export { CStandardLibraryProvider } from './headers/stdlib-provider.js';
export { CppStandardLibraryProvider } from './headers/cpp-stdlib-provider.js';

// Re-export WASM module factory as default
// Using main cpptoc.js build (full transpiler with ACSL inference support)
export { default } from './cpptoc.js';
