/**
 * TypeScript wrapper around libclang.wasm C API
 * Provides type-safe interface to Clang's C API compiled to WebAssembly
 */

// CXCursor is an opaque structure in libclang
export interface CXCursor {
  kind: number;
  xdata: number;
  data: [number, number, number];
}

export interface CXType {
  kind: number;
  data: [number, number];
}

export enum CXCursorKind {
  UnexposedDecl = 1,
  StructDecl = 2,
  UnionDecl = 3,
  ClassDecl = 4,
  EnumDecl = 5,
  FieldDecl = 6,
  EnumConstantDecl = 7,
  FunctionDecl = 8,
  VarDecl = 9,
  ParmDecl = 10,
  TypedefDecl = 20,
  CXXMethod = 21,
  Namespace = 22,
  Constructor = 24,
  Destructor = 25,
  CXXAccessSpecifier = 39,
  TypeRef = 43,
  CXXBaseSpecifier = 44,
  TemplateRef = 45,
  NamespaceRef = 46,
  MemberRef = 47,
  FunctionTemplate = 60,
  ClassTemplate = 4,
  ClassTemplatePartialSpecialization = 62,
  NamespaceAlias = 63,
  TranslationUnit = 300,
  FirstDecl = 1,
  LastDecl = 63,
  FirstInvalid = 70,
  LastInvalid = 73
}

export enum CXChildVisitResult {
  Break = 0,
  Continue = 1,
  Recurse = 2
}

export enum CXTypeKind {
  Invalid = 0,
  Void = 2,
  Bool = 3,
  Char_S = 13,
  Int = 17,
  Long = 18,
  Float = 21,
  Double = 22,
  Pointer = 101,
  Record = 105,
  Typedef = 107,
  FunctionProto = 111,
  ConstantArray = 112,
  LValueReference = 120
}

export enum CX_CXXAccessSpecifier {
  Invalid = 0,
  Public = 1,
  Protected = 2,
  Private = 3
}

export type CursorVisitor = (cursor: CXCursor, parent: CXCursor) => CXChildVisitResult;

/**
 * Main wrapper class for libclang.wasm
 */
export class LibClangWrapper {
  private module: any = null;
  private index: number = 0;
  private initialized: boolean = false;

  /**
   * Dynamically load a module from URL (from public directory)
   */
  private async loadModule(url: string, useDefault: boolean = true): Promise<any> {
    // Fetch the module text, create a blob URL, then import it
    // This works around Vite's restriction on importing from /public
    const response = await fetch(url);
    if (!response.ok) {
      throw new Error(`Failed to fetch module from ${url}: ${response.statusText}`);
    }

    const moduleText = await response.text();
    const blob = new Blob([moduleText], { type: 'application/javascript' });
    const blobUrl = URL.createObjectURL(blob);

    try {
      const module = await import(/* @vite-ignore */ blobUrl);
      return useDefault ? module.default : module;
    } finally {
      // Clean up blob URL
      URL.revokeObjectURL(blobUrl);
    }
  }

  /**
   * Initialize libclang.wasm module and setup virtual filesystem
   */
  async initialize(): Promise<void> {
    if (this.initialized) {
      return;
    }

    console.log('[LibClang] Loading libclang.wasm module...');

    // Load the module by creating a script tag (works in both dev and prod)
    const baseUrl = import.meta.env.BASE_URL || '/';
    const normalizedBase = baseUrl.endsWith('/') ? baseUrl : `${baseUrl}/`;
    const moduleUrl = `${normalizedBase}wasm/libclang.mjs`;

    console.log(`[LibClang] Loading from: ${moduleUrl}`);

    // Dynamically load the WASM module
    const createLibClang = await this.loadModule(moduleUrl);

    console.log('[LibClang] Creating WASM instance...');

    // Provide locateFile to help Emscripten find the .wasm file
    this.module = await createLibClang({
      locateFile: (path: string) => {
        console.log(`[LibClang] Locating file: ${path}`);
        if (path.endsWith('.wasm')) {
          const wasmUrl = `${normalizedBase}wasm/${path}`;
          console.log(`[LibClang] WASM file URL: ${wasmUrl}`);
          return wasmUrl;
        }
        return path;
      }
    });

    console.log('[LibClang] WASM loaded successfully');
    // Note: HEAP8 not exported in this build, skipping heap size logging

    // Setup virtual filesystem
    console.log('[LibClang] Setting up virtual filesystem...');
    this.setupVirtualFilesystem();

    // Load Clang headers
    console.log('[LibClang] Loading Clang builtin headers...');
    await this.loadClangHeaders();

    // Create Clang index
    console.log('[LibClang] Creating Clang index...');
    const createIndex = this.module.cwrap('clang_createIndex', 'number', ['number', 'number']);
    this.index = createIndex(0, 0);
    console.log(`[LibClang] Index created: ${this.index}`);

    this.initialized = true;
    console.log('[LibClang] Initialization complete!');
  }

  /**
   * Setup the virtual filesystem structure required by Clang
   */
  private setupVirtualFilesystem(): void {
    try {
      this.module.FS.mkdir('/usr');
    } catch (e) {
      // Directory might already exist
    }

    try {
      this.module.FS.mkdir('/usr/lib');
    } catch (e) {
      // Directory might already exist
    }

    // Write fake executable - critical for resource path detection
    this.module.FS.writeFile('/usr/lib/libclang.wasm', 'fake executable');

    try {
      this.module.FS.mkdir('/usr/lib/clang');
    } catch (e) {
      // Directory might already exist
    }

    try {
      this.module.FS.mkdir('/usr/lib/clang/17.0.6');
    } catch (e) {
      // Directory might already exist
    }

    try {
      this.module.FS.mkdir('/usr/lib/clang/17.0.6/include');
    } catch (e) {
      // Directory might already exist
    }

    console.log('[LibClang] Virtual filesystem ready');
  }

  /**
   * Load Clang builtin headers into virtual filesystem
   */
  private async loadClangHeaders(): Promise<void> {
    // Load headers module
    const baseUrl = import.meta.env.BASE_URL || '/';
    const normalizedBase = baseUrl.endsWith('/') ? baseUrl : `${baseUrl}/`;
    const headersUrl = `${normalizedBase}wasm/clang-headers.mjs`;

    console.log(`[LibClang] Loading headers from: ${headersUrl}`);
    const headersModule = await this.loadModule(headersUrl, false); // Named export, not default
    const headers = headersModule.clangHeaders;

    let loadedCount = 0;
    for (const [path, content] of Object.entries(headers)) {
      const fullPath = `/usr/lib/clang/17.0.6/include/${path}`;
      const dirPath = fullPath.substring(0, fullPath.lastIndexOf('/'));

      // Create directories recursively
      const dirs = dirPath.split('/').filter(Boolean);
      let currentPath = '';
      for (const dir of dirs) {
        currentPath += '/' + dir;
        try {
          this.module.FS.mkdir(currentPath);
        } catch (e) {
          // Directory exists
        }
      }

      this.module.FS.writeFile(fullPath, content as string);
      loadedCount++;
    }

    console.log(`[LibClang] Loaded ${loadedCount} header files`);
  }

  /**
   * Parse C++ source code into a translation unit
   */
  parse(code: string, filename: string = '/input.cpp'): number {
    if (!this.initialized) {
      throw new Error('LibClang not initialized. Call initialize() first.');
    }

    console.log(`[LibClang] Parsing ${code.length} characters of C++ code...`);

    // Write source file to virtual filesystem
    this.module.FS.writeFile(filename, code);
    console.log(`[LibClang] Written source to ${filename}`);

    // Prepare compiler arguments
    const args = ['-nostdinc', '-nostdinc++', '-nobuiltininc'];
    console.log(`[LibClang] Compiler args: ${args.join(' ')}`);

    // Marshal arguments to WASM memory
    const argPtrs = args.map(arg => {
      const len = this.module.lengthBytesUTF8(arg) + 1;
      const ptr = this.module._malloc(len);
      this.module.stringToUTF8(arg, ptr, len);
      return ptr;
    });

    const argArrayPtr = this.module._malloc(argPtrs.length * 4);
    argPtrs.forEach((ptr, i) => {
      this.module.setValue(argArrayPtr + i * 4, ptr, 'i32');
    });

    // Parse translation unit
    const parseTranslationUnit = this.module.cwrap(
      'clang_parseTranslationUnit',
      'number',
      ['number', 'string', 'number', 'number', 'number', 'number', 'number']
    );

    const tu = parseTranslationUnit(
      this.index,
      filename,
      argArrayPtr,
      args.length,
      0,
      0,
      0
    );

    // Clean up arguments
    argPtrs.forEach(ptr => this.module._free(ptr));
    this.module._free(argArrayPtr);

    if (tu === 0) {
      throw new Error('Failed to parse translation unit');
    }

    console.log(`[LibClang] Parsed successfully! TU handle: ${tu}`);

    // Get diagnostics count
    const getNumDiagnostics = this.module.cwrap('clang_getNumDiagnostics', 'number', ['number']);
    const numDiags = getNumDiagnostics(tu);
    console.log(`[LibClang] Diagnostics: ${numDiags}`);

    return tu;
  }

  /**
   * Get the cursor for a translation unit
   */
  getTranslationUnitCursor(tu: number): CXCursor {
    const getCursor = this.module.cwrap('clang_getTranslationUnitCursor', 'number', ['number']);
    const cursorPtr = getCursor(tu);

    // CXCursor is a struct, need to read from memory
    // For now, return a placeholder - will need proper struct reading
    return {
      kind: 0,
      xdata: 0,
      data: [0, 0, 0]
    };
  }

  /**
   * Visit children of a cursor with a callback
   */
  visitChildren(cursor: CXCursor, visitor: CursorVisitor): void {
    // This will require function pointer marshaling with addFunction
    // Implementation deferred to next iteration
    console.log('[LibClang] visitChildren not yet implemented');
  }

  /**
   * Get the kind of a cursor
   */
  getCursorKind(cursor: CXCursor): CXCursorKind {
    return cursor.kind;
  }

  /**
   * Get the spelling (name) of a cursor
   */
  getCursorSpelling(cursor: CXCursor): string {
    // Will need to implement CXString handling
    return '';
  }

  /**
   * Get the type of a cursor
   */
  getCursorType(cursor: CXCursor): CXType {
    return {
      kind: 0,
      data: [0, 0]
    };
  }

  /**
   * Get cursor access specifier (public/private/protected)
   */
  getCXXAccessSpecifier(cursor: CXCursor): CX_CXXAccessSpecifier {
    const getAccess = this.module.cwrap('clang_getCXXAccessSpecifier', 'number', ['number']);
    // Need proper cursor passing
    return CX_CXXAccessSpecifier.Public;
  }

  /**
   * Dispose of a translation unit
   */
  disposeTranslationUnit(tu: number): void {
    const dispose = this.module.cwrap('clang_disposeTranslationUnit', null, ['number']);
    dispose(tu);
    console.log('[LibClang] Translation unit disposed');
  }

  /**
   * Cleanup resources
   */
  dispose(): void {
    if (this.index !== 0) {
      const disposeIndex = this.module.cwrap('clang_disposeIndex', null, ['number']);
      disposeIndex(this.index);
      console.log('[LibClang] Index disposed');
      this.index = 0;
    }
    this.initialized = false;
  }
}
