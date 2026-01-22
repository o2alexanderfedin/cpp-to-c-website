import { HeaderProvider } from '../types.js';
export declare class CStandardLibraryProvider implements HeaderProvider {
    private headers;
    getHeader(name: string): string | null;
    hasHeader(name: string): boolean;
    listHeaders(): string[];
}
//# sourceMappingURL=stdlib-provider.d.ts.map