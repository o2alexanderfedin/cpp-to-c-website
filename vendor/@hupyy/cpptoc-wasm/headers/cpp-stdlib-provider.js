import { CStandardLibraryProvider } from './stdlib-provider.js';
export class CppStandardLibraryProvider {
    constructor() {
        this.mappings = new Map([
            ['iostream', 'stdio.h'],
            ['fstream', 'stdio.h'],
            ['sstream', null],
            ['cstdio', 'stdio.h'],
            ['cstdlib', 'stdlib.h'],
            ['cstring', 'string.h'],
            ['cmath', 'math.h'],
            ['cassert', 'assert.h'],
            ['cstddef', 'stddef.h'],
            ['cstdarg', 'stdarg.h'],
            ['vector', null],
            ['list', null],
            ['deque', null],
            ['map', null],
            ['set', null],
            ['unordered_map', null],
            ['unordered_set', null],
            ['array', null],
            ['queue', null],
            ['stack', null],
            ['string', null],
            ['algorithm', null],
            ['memory', null],
            ['utility', null],
            ['functional', null],
            ['iterator', null],
            ['exception', null],
            ['stdexcept', null],
            ['type_traits', null],
            ['typeinfo', null],
            ['limits', null],
            ['numeric', null],
            ['complex', null],
            ['ctime', null],
            ['chrono', null],
            ['thread', null],
            ['mutex', null],
            ['condition_variable', null],
            ['atomic', null],
        ]);
        this.cStdlibProvider = new CStandardLibraryProvider();
    }
    getHeader(name) {
        if (this.mappings.has(name)) {
            const mapped = this.mappings.get(name);
            if (mapped) {
                return this.cStdlibProvider.getHeader(mapped);
            }
            return null;
        }
        return this.cStdlibProvider.getHeader(name);
    }
    hasHeader(name) {
        if (this.mappings.has(name)) {
            const mapped = this.mappings.get(name);
            if (mapped === null || mapped === undefined) {
                return false;
            }
            return this.cStdlibProvider.hasHeader(mapped);
        }
        return this.cStdlibProvider.hasHeader(name);
    }
    listHeaders() {
        const supported = [];
        for (const [cppHeader, cHeader] of this.mappings.entries()) {
            if (cHeader !== null) {
                supported.push(cppHeader);
            }
        }
        return [...supported, ...this.cStdlibProvider.listHeaders()];
    }
    isSupported(name) {
        return this.hasHeader(name);
    }
    getMappedHeaderName(cppHeaderName) {
        return this.mappings.get(cppHeaderName) || null;
    }
    listUnsupportedHeaders() {
        const unsupported = [];
        for (const [cppHeader, cHeader] of this.mappings.entries()) {
            if (cHeader === null) {
                unsupported.push(cppHeader);
            }
        }
        return unsupported;
    }
}
