/**
 * TypeScript types for cpptoc WASM API
 * Auto-generated types from embind are augmented here
 */

export interface Diagnostic {
    line: number;
    column: number;
    message: string;
    severity: 'error' | 'warning' | 'note';
}

export interface ACSLOptions {
    statements?: boolean;
    typeInvariants?: boolean;
    axiomatics?: boolean;
    ghostCode?: boolean;
    behaviors?: boolean;
    memoryPredicates?: boolean;
}

/**
 * Header provider interface for resolving #include directives
 * Enables on-demand header loading in WebAssembly scenario
 */
export interface HeaderProvider {
    /**
     * Get header content by name
     * @param headerName - e.g., "stdio.h", "vector", "custom/myheader.h"
     * @returns Header content as string, or null if not found
     */
    getHeader(headerName: string): string | null;

    /**
     * Check if header exists
     */
    hasHeader(headerName: string): boolean;

    /**
     * List all available headers
     */
    listHeaders(): string[];
}

export interface TranspileOptions {
    acsl?: ACSLOptions;
    target?: 'c89' | 'c99' | 'c11' | 'c17';
    optimize?: boolean;
    /**
     * Header provider for resolving #include directives
     * Required for transpiling code that includes headers
     */
    headerProvider?: HeaderProvider;
    /**
     * C++ standard version (11, 14, 17, 20, 23)
     */
    cppStandard?: 11 | 14 | 17 | 20 | 23;
    /**
     * ACSL coverage level
     */
    acslLevel?: 'Basic' | 'Full';
    /**
     * ACSL output mode
     */
    acslOutputMode?: 'Inline' | 'Separate';
    /**
     * Enable template monomorphization (Phase 11)
     */
    monomorphizeTemplates?: boolean;
    /**
     * Maximum template instantiations (Phase 11)
     */
    templateInstantiationLimit?: number;
    /**
     * Enable exception handling translation (Phase 12)
     */
    enableExceptions?: boolean;
    /**
     * Exception handling model (Phase 12)
     */
    exceptionModel?: 'sjlj' | 'tables';
    /**
     * Enable RTTI translation (Phase 13)
     */
    enableRTTI?: boolean;
    /**
     * Use #pragma once instead of include guards
     */
    usePragmaOnce?: boolean;
    /**
     * Generate dependency graph in DOT format
     */
    generateDependencyGraph?: boolean;
    /**
     * Virtual files for in-memory compilation (file_path, file_content)
     */
    virtualFiles?: Array<[string, string]>;
    /**
     * Include directories for header file resolution
     */
    includeDirectories?: string[];
    /**
     * @deprecated Use acslLevel instead
     */
    enableACSL?: boolean;
}

export interface TranspileResult {
    success: boolean;
    c: string;
    /**
     * Header file (.h) - Phase 28
     * Contains forward declarations, struct definitions, and function signatures
     */
    h: string;
    acsl: string;
    diagnostics: Diagnostic[];
    /**
     * Required headers not found by header provider
     */
    missingHeaders?: string[];
    /**
     * Header files generated or used (name → content)
     */
    headers?: Map<string, string>;
}

export interface WASMModule {
    Transpiler: new () => TranspilerInstance;
}

export interface TranspilerInstance {
    transpile(code: string, options: TranspileOptions): TranspileResult;
    getVersion(): string;
    delete(): void;
}

export interface CreateModuleOptions {
    locateFile?: (path: string, prefix: string) => string;
    onRuntimeInitialized?: () => void;
}

export type CreateCppToCModule = (options?: CreateModuleOptions) => Promise<WASMModule>;

/**
 * Default ACSL options for common use cases
 */
export const DEFAULT_ACSL_OPTIONS: ACSLOptions = {
    statements: false,
    typeInvariants: false,
    axiomatics: false,
    ghostCode: false,
    behaviors: false,
    memoryPredicates: false
};

/**
 * Default transpile options matching C++ defaults
 */
export const DEFAULT_TRANSPILE_OPTIONS: TranspileOptions = {
    acsl: DEFAULT_ACSL_OPTIONS,
    target: 'c99',
    optimize: false,
    cppStandard: 17,
    acslLevel: 'Basic',
    acslOutputMode: 'Inline',
    monomorphizeTemplates: true,
    templateInstantiationLimit: 1000,
    enableExceptions: true,
    exceptionModel: 'sjlj',
    enableRTTI: true,
    usePragmaOnce: false,
    generateDependencyGraph: false,
    includeDirectories: []
};

/**
 * Type guard for checking if result has errors
 */
export function hasErrors(result: TranspileResult): boolean {
    return !result.success || result.diagnostics.some(d => d.severity === 'error');
}

/**
 * Get only error diagnostics
 */
export function getErrors(result: TranspileResult): Diagnostic[] {
    return result.diagnostics.filter(d => d.severity === 'error');
}

/**
 * Get only warning diagnostics
 */
export function getWarnings(result: TranspileResult): Diagnostic[] {
    return result.diagnostics.filter(d => d.severity === 'warning');
}

/**
 * Format diagnostic message for display
 */
export function formatDiagnostic(diagnostic: Diagnostic): string {
    const location = diagnostic.line > 0
        ? `${diagnostic.line}:${diagnostic.column}`
        : 'global';
    return `[${diagnostic.severity.toUpperCase()}] ${location}: ${diagnostic.message}`;
}
