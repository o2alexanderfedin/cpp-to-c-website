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
export interface HeaderProvider {
    getHeader(headerName: string): string | null;
    hasHeader(headerName: string): boolean;
    listHeaders(): string[];
}
export interface TranspileOptions {
    acsl?: ACSLOptions;
    target?: 'c89' | 'c99' | 'c11' | 'c17';
    optimize?: boolean;
    headerProvider?: HeaderProvider;
    cppStandard?: 11 | 14 | 17 | 20 | 23;
    acslLevel?: 'Basic' | 'Full';
    acslOutputMode?: 'Inline' | 'Separate';
    monomorphizeTemplates?: boolean;
    templateInstantiationLimit?: number;
    enableExceptions?: boolean;
    exceptionModel?: 'sjlj' | 'tables';
    enableRTTI?: boolean;
    usePragmaOnce?: boolean;
    generateDependencyGraph?: boolean;
    virtualFiles?: Array<[string, string]>;
    includeDirectories?: string[];
    enableACSL?: boolean;
}
export interface TranspileResult {
    success: boolean;
    c: string;
    h: string;
    acsl: string;
    diagnostics: Diagnostic[];
    missingHeaders?: string[];
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
export declare const DEFAULT_ACSL_OPTIONS: ACSLOptions;
export declare const DEFAULT_TRANSPILE_OPTIONS: TranspileOptions;
export declare function hasErrors(result: TranspileResult): boolean;
export declare function getErrors(result: TranspileResult): Diagnostic[];
export declare function getWarnings(result: TranspileResult): Diagnostic[];
export declare function formatDiagnostic(diagnostic: Diagnostic): string;
//# sourceMappingURL=types.d.ts.map