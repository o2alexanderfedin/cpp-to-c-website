export const DEFAULT_ACSL_OPTIONS = {
    statements: false,
    typeInvariants: false,
    axiomatics: false,
    ghostCode: false,
    behaviors: false,
    memoryPredicates: false
};
export const DEFAULT_TRANSPILE_OPTIONS = {
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
export function hasErrors(result) {
    return !result.success || result.diagnostics.some(d => d.severity === 'error');
}
export function getErrors(result) {
    return result.diagnostics.filter(d => d.severity === 'error');
}
export function getWarnings(result) {
    return result.diagnostics.filter(d => d.severity === 'warning');
}
export function formatDiagnostic(diagnostic) {
    const location = diagnostic.line > 0
        ? `${diagnostic.line}:${diagnostic.column}`
        : 'global';
    return `[${diagnostic.severity.toUpperCase()}] ${location}: ${diagnostic.message}`;
}
