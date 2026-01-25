import { HeaderProvider } from '../types.js';
export declare class CppStandardLibraryProvider implements HeaderProvider {
    private cStdlibProvider;
    private mappings;
    constructor();
    getHeader(name: string): string | null;
    hasHeader(name: string): boolean;
    listHeaders(): string[];
    isSupported(name: string): boolean;
    getMappedHeaderName(cppHeaderName: string): string | null;
    listUnsupportedHeaders(): string[];
}
//# sourceMappingURL=cpp-stdlib-provider.d.ts.map