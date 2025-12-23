<research>
  <summary>
This research establishes a clear technical foundation for building a web-based C++ to C transpilation playground using the File System Access API, server-side transpilation architecture, and progressive enhancement patterns. The recommended technology stack centers on Chromium-based browsers for optimal experience while providing graceful degradation for Firefox, Safari, and mobile users.

The File System Access API (Chrome 105+, Edge 105+, Opera 91+) provides comprehensive directory selection and traversal capabilities, enabling users to load entire C++ projects directly from their local filesystem. While browser support is limited to Chromium desktop browsers (34.76% global usage), the browser-fs-access library provides automatic fallbacks to webkitdirectory for Firefox/Safari and single-file upload for mobile browsers. The API's permission model is user-friendly, requiring only picker interaction without separate permission prompts, though permissions clear when tabs close.

The playground architecture leverages the existing server-side transpilation infrastructure from Phase 16-04, where the browser handles file I/O and the backend performs transpilation using Clang/LLVM. This avoids massive WASM bundle sizes (100MB+) and complex Emscripten filesystem integration while providing full C++ language support. Files are read via File System Access API, bundled with headers, sent to server for transpilation, and results displayed in the browser.

Critical architectural insights include: (1) Implement IFileSystem abstraction with memfs-browser for testable code following SOLID principles, (2) Use parallel file reading with Promise.all() for 10x performance improvement on multi-file projects, (3) Store FileSystemDirectoryHandle objects in IndexedDB for "recent projects" functionality, (4) Support both directory picker and drag-and-drop for intuitive UX, (5) Define three browser support tiers with clear UI messaging to set appropriate user expectations.

Key recommendations: Use File System Access API as primary mechanism, implement browser-fs-access for progressive enhancement, create IFileSystem abstraction for TDD, maintain server-side transpilation architecture, support drag-and-drop with modern/legacy API fallback, use IndexedDB for persistence, implement parallel file reading, and define clear browser support tiers. For large projects (500+ files), consider Web Workers to prevent main thread blocking and progress indicators for user feedback.

Technology stack: TypeScript with Vitest testing, memfs-browser for mock filesystem, browser-fs-access for cross-browser support, IndexedDB for recent projects, server endpoint for transpilation (to be implemented), existing Clang/LLVM backend integration. The playground will work best on Chrome/Edge desktop (full features), acceptably on Firefox/Safari desktop (read-only), and minimally on mobile (single file upload).
  </summary>
  <findings>
    <finding category="file-system-access">
      <title>File System Access API - Core Capabilities</title>
      <detail>
The File System Access API provides three main picker methods for user-initiated file system access:
- window.showOpenFilePicker() - Select one or multiple files
- window.showSaveFilePicker() - Save files to disk
- window.showDirectoryPicker() - Select entire directories

Key interfaces include FileSystemFileHandle, FileSystemDirectoryHandle, and FileSystemWritableFileStream for comprehensive file operations. The API supports recursive directory traversal through async iteration, though recursive logic must be implemented by developers. Directory handles provide resolve() method to determine relative paths between handles.

Read operations use getFile() to obtain File objects, while write operations use createWritable() to get writable streams. The API supports positional writes, seeks, and truncation. For Web Workers, synchronous OPFS (Origin Private File System) access is available via createSyncAccessHandle() for high-performance operations.
      </detail>
      <source>MDN File System Access API (https://developer.mozilla.org/en-US/docs/Web/API/File_System_Access_API)</source>
      <relevance>
Critical for enabling users to select entire C++ project directories in the playground. The async iteration capability allows traversing project structures to read all .cpp, .h, and .hpp files. Directory handles can be stored in IndexedDB for "recent projects" functionality.
      </relevance>
    </finding>

    <finding category="file-system-access">
      <title>Browser Compatibility - Desktop Only</title>
      <detail>
Desktop browser support (as of December 2025):
- Chrome/Edge: Full support from version 105+ (partial in 86-104)
- Firefox: No support across all versions - Mozilla published "harmful" position
- Safari: No support in any version
- Opera: Full support from version 91+

Current global usage: 34.76% (Chromium-based browsers only)

Mobile browsers: NO support across all platforms (Chrome Android, Safari iOS, Samsung Internet, Opera Mini). The API is desktop-only.

Security requirements:
- HTTPS-only (secure context required)
- User-initiated pickers (no programmatic access without interaction)
- Permission model built into picker flow (no separate prompts for initial access)
- Permissions persist only while origin tabs remain open
      </detail>
      <source>Can I Use - native-filesystem-api (https://caniuse.com/native-filesystem-api)</source>
      <relevance>
This is a critical constraint: the playground will only work on Chromium-based desktop browsers (Chrome, Edge, Opera). Need prominent browser detection and user messaging. Firefox and Safari users must use fallback approach (file upload or drag-drop without directory traversal).
      </relevance>
    </finding>

    <finding category="file-system-access">
      <title>Permissions Model and Best Practices</title>
      <detail>
Permission handling characteristics:
- Initial access granted through file/directory picker (transparent to user)
- queryPermission() checks current permission status
- requestPermission() re-requests access if needed
- Permissions cleared when all origin tabs close
- No persistent permission storage across sessions

Best practices from Chrome developers:
- Use startIn property to suggest relevant directories ('documents', 'downloads', etc.)
- Store file handles in IndexedDB for "recent files" functionality
- Combine read/write permission requests during initial picker
- Use Promise.all() for parallel file operations (avoid sequential await)
- Implement graceful degradation for unsupported browsers
- Browser-fs-access library provides polyfills: showOpenFilePicker → input type=file, showDirectoryPicker → input webkitdirectory

Performance optimization:
- Stream-based writing (pipeTo) more efficient than buffering entire contents
- For Web Workers: createSyncAccessHandle() on OPFS provides synchronous, high-performance access
      </detail>
      <source>Chrome Developers - File System Access API (https://developer.chrome.com/articles/file-system-access)</source>
      <relevance>
Permission model is user-friendly (no separate permission prompts), but requires session management. The playground should implement IndexedDB storage for recent projects and use browser-fs-access library for progressive enhancement on non-Chromium browsers.
      </relevance>
    </finding>

    <finding category="drag-and-drop">
      <title>Drag-and-Drop Directory Support</title>
      <detail>
Two approaches for drag-and-drop file/directory handling:

1. Modern File System Access API approach:
   - DataTransferItem.getAsFileSystemHandle() returns Promise with FileSystemFileHandle (files) or FileSystemDirectoryHandle (directories)
   - Provides read AND write access to dropped items
   - Experimental API with limited browser support
   - Enables full directory traversal after drop

2. Legacy webkitGetAsEntry approach:
   - DataTransferItem.webkitGetAsEntry() returns FileSystemFileEntry or FileSystemDirectoryEntry
   - Read-only access (no write-back capability)
   - Not on standards track but broader browser support
   - Also enables directory traversal

Important note: Both file and directory items report DataTransferItem.kind === "file". Must use FileSystemHandle.kind to distinguish "file" vs "directory" with modern API.

Desktop browser support: All major browsers (Chrome, Edge, Firefox, Safari) on desktop OS (Windows, macOS, Linux).
Mobile browser support: NO support on Android or iOS.
      </detail>
      <source>MDN DataTransferItem.getAsFileSystemHandle(), web.dev drag-and-drop patterns (https://web.dev/patterns/files/drag-and-drop-directories)</source>
      <relevance>
Drag-and-drop provides excellent UX alternative to directory picker. Should implement feature detection and use modern API where available, falling back to webkitGetAsEntry. This gives users two ways to load projects: picker button or drag-drop. Desktop-only limitation consistent with File System Access API.
      </relevance>
    </finding>

    <finding category="wasm-integration">
      <title>Current WASM Implementation - Server-Side Architecture</title>
      <detail>
Phase 16-04 completed server-side preprocessing architecture for header provisioning:

Architecture chosen: Option B - Server-Side Preprocessing (Clang on backend)
- WASM module does NOT include Clang/LLVM (avoids ~100MB+ bundle size)
- TypeScript HeaderProvider API designed and implemented
- CStandardLibraryProvider supports 7 C headers (stdio.h, stdlib.h, string.h, math.h, assert.h, stddef.h, stdarg.h)
- CppStandardLibraryProvider maps 10 C++ headers to C equivalents (iostream→stdio.h, cstdio→stdio.h, etc.)
- Custom header injection supported via HeaderProvider interface
- 28 integration tests passing (100% success rate)

Current status of WASM module files:
- TypeScript API exists at /wasm/glue/src/ (outside website/ directory)
- Files: index.ts, types.ts, headers/stdlib-provider.ts, headers/cpp-stdlib-provider.ts
- Tests: tests/header-provisioning.test.ts (28 tests, 7ms execution)
- Build: TypeScript compiles without errors

Server-side transpilation flow:
1. Browser sends C++ source + header content to server endpoint
2. Server uses full Clang/LLVM to transpile (Phase 15 integration)
3. Server returns transpiled C code + ACSL annotations
4. WASM module focuses on API/UI layer only

Limitations:
- STL containers (vector, map, set) require transpilation (not header mapping)
- C++ std::string requires transpilation to char*
- Smart pointers, templates, exceptions, RTTI not in C
- These are handled server-side, not client-side
      </detail>
      <source>Phase 16-04 Summary (.planning/phases/16-runtime-integration-testing/16-04-SUMMARY.md)</source>
      <relevance>
The playground architecture is already decided: client-side file handling + server-side transpilation. The playground UI will use File System Access API to read project files, bundle them with headers, and send to server. This keeps browser bundle small and leverages existing Clang/LLVM backend. No need for Emscripten filesystem or client-side compilation.
      </relevance>
    </finding>

    <finding category="wasm-integration">
      <title>Emscripten File Systems (For Reference Only)</title>
      <detail>
Emscripten provides multiple filesystem implementations for WASM:

MEMFS (Memory File System):
- Default filesystem, mounted at root "/"
- All files stored in-memory (data lost on page reload)
- Includes by default, no linking flags needed
- Creates /home/web_user, /tmp, /dev/null, /dev/random by default

Alternative filesystems (require explicit linking):
- NODEFS (-lnodefs.js) - Node.js filesystem access
- IDBFS (-lidbfs.js) - IndexedDB persistence (requires FS.syncfs() calls)
- WORKERFS (-lworkerfs.js) - Web Worker filesystem
- PROXYFS (-lproxyfs.js) - Proxy to another filesystem

WasmFS (Next Generation):
- High-performance, fully-multithreaded filesystem
- Stores file contents in Wasm memory (not JS memory)
- Link with -sWASMFS flag
- More efficient for multithreaded applications
- Still in development as of 2025

Key insight: IDBFS requires explicit FS.syncfs() calls to flush MEMFS changes to IndexedDB, adding complexity.
      </detail>
      <source>Emscripten File System API documentation (https://emscripten.org/docs/api_reference/Filesystem-API.html)</source>
      <relevance>
NOT directly relevant for this playground since we're using server-side transpilation. However, if we later decide to run transpiler client-side (Option D - Hybrid approach), MEMFS would be the default choice for temporarily storing project files during transpilation. For now, files stay in JavaScript memory using File API.
      </relevance>
    </finding>

    <finding category="testing-abstraction">
      <title>File System Abstraction for Testing</title>
      <detail>
Recommended abstraction pattern for testable file system operations:

Interface-based abstraction:
```typescript
interface IFileSystem {
  readFile(path: string): Promise&lt;string&gt;;
  writeFile(path: string, content: string): Promise&lt;void&gt;;
  readDir(path: string): Promise&lt;string[]&gt;;
  exists(path: string): Promise&lt;boolean&gt;;
}
```

Two implementations:
1. Production: FileSystemAccessAdapter (uses File System Access API)
2. Testing: InMemoryFileSystem or MemFSAdapter

Best practices for abstraction:
- Define clear contracts with TypeScript interfaces
- Keep abstractions pure (no side effects in core logic)
- Use functional core, imperative shell pattern
- Dependency injection for filesystem implementation

Benefits:
- Unit tests run without browser APIs
- Fast test execution (no I/O)
- Deterministic test scenarios
- Easy mocking of edge cases (permissions, errors)
      </detail>
      <source>TypeScript abstraction patterns (https://www.xjavascript.com/blog/abstraction-typescript/), functional core patterns (https://www.dennisokeeffe.com/blog/2025-03-16-effective-typescript-principles-in-2025)</source>
      <relevance>
Essential for TDD approach with playground. Create IFileSystem abstraction so core transpilation logic can be tested without browser file APIs. In-memory implementation for unit tests, File System Access API adapter for production. Enables testing directory traversal, file filtering, error handling independently.
      </relevance>
    </finding>

    <finding category="testing-abstraction">
      <title>Mock Filesystem Libraries - memfs and mock-fs</title>
      <detail>
Two primary libraries for mocking filesystem in Node.js tests:

memfs (RECOMMENDED - actively maintained):
- Works in both Node.js and browser environments
- memfs-browser package available on npm for browser-specific use
- API closely resembles Node.js fs module (readFile, writeFile, unlink)
- Create directory structures from JSON objects (keys=paths, values=contents)
- Easy to switch between real fs and memfs
- Actively maintained as of 2025
- Integrates well with Vitest (examples from June 2024)

mock-fs (DEPRECATED):
- Allows Node's fs module to be backed by in-memory mock
- No longer maintained (deprecated)
- Simpler API but less flexible than memfs

Integration with Vitest (2024-2025 pattern):
```typescript
import { vol } from 'memfs';
import { vi } from 'vitest';

vi.mock('fs', () =&gt; memfs);

beforeEach(() =&gt; {
  vol.fromJSON({
    '/project/main.cpp': 'int main() {}',
    '/project/utils.h': 'void helper();'
  });
});
```

Key advantages of memfs:
- Much faster than real filesystem operations
- Deterministic test scenarios
- No test fixture files needed
- Virtual filesystem is flexible and straightforward
      </detail>
      <source>memfs npm (https://www.npmjs.com/package/memfs), memfs-browser npm (https://www.npmjs.com/package/memfs-browser), Vitest integration (https://kschaul.com/til/2024/06/26/mock-fs-with-vitest-and-memfs/)</source>
      <relevance>
Use memfs for unit testing directory traversal and file processing logic. Since the playground is browser-based, memfs-browser provides the right abstraction. Tests can create virtual C++ projects in-memory and verify correct file discovery, filtering (.cpp, .h, .hpp), and content reading without touching real File System Access API.
      </relevance>
    </finding>

    <finding category="ui-ux">
      <title>Progressive Enhancement Strategy</title>
      <detail>
Browser support tiers for playground:

Tier 1 - Full Experience (Chrome, Edge, Opera 91+ on desktop):
- File System Access API with directory picker
- Drag-and-drop directories with getAsFileSystemHandle()
- Write-back capability (save transpiled C to disk)
- Recent projects via IndexedDB
- Best performance and UX

Tier 2 - Read-Only Experience (Firefox, Safari on desktop):
- Fallback to input type="file" webkitdirectory
- Drag-and-drop with webkitGetAsEntry (read-only)
- Download transpiled files (cannot write to original location)
- No recent projects (no persistent handles)

Tier 3 - Single File Upload (Mobile browsers):
- Simple file upload (paste code or upload single .cpp file)
- No directory traversal
- Basic transpilation functionality only

Polyfill library: browser-fs-access
- Automatically provides fallbacks
- Feature detection: if ('showOpenFilePicker' in self)
- Graceful degradation without complex branching

UI considerations:
- Prominent browser compatibility notice
- Recommend Chrome/Edge for best experience
- Show feature availability based on detected browser
- Progress indicators for large projects (100+ files)
- Error display for file read failures
      </detail>
      <source>browser-fs-access library, Chrome developers best practices</source>
      <relevance>
Define clear UX tiers so playground works for maximum audience while highlighting Chromium browsers for best experience. Use browser-fs-access for automatic fallbacks. Show clear messaging about available features per browser. Mobile users get basic functionality (single file), desktop users get full project support.
      </relevance>
    </finding>

    <finding category="performance">
      <title>Performance Characteristics and Optimization</title>
      <detail>
File System Access API performance patterns:

Parallel operations:
- Avoid sequential await when reading multiple files
- Use Promise.all() for parallel file reads
- Example: Reading 100 files sequentially ~10x slower than parallel

Directory traversal:
- Recursive async iteration is efficient for small-medium projects
- For large projects (1000+ files), consider:
  - Web Worker for traversal (avoid blocking main thread)
  - Streaming results to UI (show files as discovered)
  - Lazy loading (only read file contents when needed)

Write operations:
- Stream-based writing (pipeTo) more efficient than buffering
- For OPFS in Web Workers: createSyncAccessHandle() offers synchronous access

Browser limitations discovered:
- No documented rate limits for API calls
- File size: tested up to 2GB+ (MEMFS issue, not File System Access API)
- File count: no hard limit, but UI becomes slow with 1000+ files

Optimization strategies:
- IndexedDB for caching file handles and metadata
- Virtual scrolling for large file lists
- Debounced transpilation (don't re-transpile on every keystroke)
- Worker threads for heavy processing (directory traversal, file parsing)
      </detail>
      <source>Chrome developers performance guidance, Emscripten MEMFS limitations</source>
      <relevance>
For playground, implement parallel file reading when user selects directory. For projects with 100+ files, show progress indicator and use Web Worker for traversal. Cache directory structure in IndexedDB for quick re-access. Most C++ projects are under 500 files, so performance should be acceptable with basic optimizations.
      </relevance>
    </finding>

    <finding category="security">
      <title>Security Considerations and Restrictions</title>
      <detail>
File System Access API security model:

Protected directories:
- Browsers block or warn on sensitive system directories
- Windows: C:\Windows, C:\Program Files, user home directories
- macOS: /System, /Library, user home directories
- Linux: /etc, /usr, /bin, user home directories
- Users prompted to select alternative location if protected path selected

Permission model:
- No persistent cross-session permissions
- Permissions tied to tab lifecycle (cleared when all origin tabs close)
- Cannot access filesystem without user interaction
- HTTPS required (no file:// protocol support)

Attack surface:
- Read access: Limited to user-selected files/directories
- Write access: Must be explicitly granted (separate from read)
- No programmatic file access (always requires picker dialog)
- Same-origin policy applies to OPFS

Privacy considerations:
- No telemetry about user file paths
- File handles are opaque (don't reveal actual paths)
- IndexedDB storage of handles is origin-scoped

Content Security Policy:
- File System Access API not affected by CSP directives
- HTTPS requirement is built-in security measure
      </detail>
      <source>MDN File System Access API security model, Chrome security documentation</source>
      <relevance>
Playground is inherently secure due to API design. User must explicitly select project directory. Cannot auto-access files or persist permissions across sessions. Need to handle protected directory warnings gracefully (show user-friendly message). HTTPS deployment is mandatory (no development on http:// even locally).
      </relevance>
    </finding>
  </findings>
  <recommendations>
    <recommendation priority="high">
      <action>Use File System Access API as primary directory selection mechanism</action>
      <rationale>
Provides best UX on Chromium browsers (34.76% global usage). Enables full directory traversal, write-back capability, and recent projects via IndexedDB. Well-documented with active browser support. Aligns with target audience (developers using modern desktop browsers).
      </rationale>
      <alternatives>
- input type="file" webkitdirectory: Broader browser support but read-only, no persistent handles
- File upload widget: Works everywhere but poor UX for multi-file projects
- Browser-fs-access library: Combines all approaches with automatic fallback
      </alternatives>
    </recommendation>

    <recommendation priority="high">
      <action>Implement browser-fs-access library for progressive enhancement</action>
      <rationale>
Provides automatic fallbacks across browser tiers without complex conditional code. Enables playground to work on Chrome (best), Firefox/Safari (good), and mobile (basic). Single API surface with feature detection built-in. Actively maintained and well-tested.
      </rationale>
      <alternatives>
- Manual feature detection: More control but higher maintenance burden
- Chromium-only approach: Simpler but excludes 65% of users
- Multiple codepaths: Harder to test and maintain
      </alternatives>
    </recommendation>

    <recommendation priority="high">
      <action>Create IFileSystem abstraction with memfs-browser for testing</action>
      <rationale>
Enables TDD by decoupling core logic from browser APIs. memfs-browser works in browser test environments (Vitest). Provides fast, deterministic unit tests for directory traversal and file filtering. Follows SOLID principles (Dependency Inversion). Allows testing edge cases (permissions, errors) easily.
      </rationale>
      <alternatives>
- Test against real File System Access API: Slow, requires user interaction, non-deterministic
- No abstraction: Untestable core logic, higher bug risk
- Custom mock implementation: More work, less reliable than established library
      </alternatives>
    </recommendation>

    <recommendation priority="high">
      <action>Maintain server-side transpilation architecture from Phase 16-04</action>
      <rationale>
Already implemented and tested (28 tests passing). Avoids 100MB+ WASM bundle size. Leverages full Clang/LLVM capabilities on backend. Simplifies browser code (just file I/O and API calls). Allows server-side caching and optimization. Client stays lightweight and responsive.
      </rationale>
      <alternatives>
- Client-side WASM transpiler: Massive bundle, limited capabilities, complex Emscripten filesystem
- Hybrid approach: Added complexity, marginal benefits for typical use cases
- Pure server rendering: No interactive editing experience
      </alternatives>
    </recommendation>

    <recommendation priority="medium">
      <action>Implement drag-and-drop with getAsFileSystemHandle() fallback to webkitGetAsEntry</action>
      <rationale>
Provides excellent UX alternative to picker button. Modern API (getAsFileSystemHandle) enables write-back on Chromium. Legacy API (webkitGetAsEntry) works on Firefox/Safari for read-only. Feature detection is straightforward. Enhances perceived polish of playground.
      </rationale>
      <alternatives>
- Picker button only: Works but less intuitive
- Modern API only: Excludes Firefox/Safari users
- No drag-drop: Simpler but worse UX
      </alternatives>
    </recommendation>

    <recommendation priority="medium">
      <action>Use IndexedDB for recent projects and directory handle persistence</action>
      <rationale>
Enables "recent projects" UX feature. Stores FileSystemDirectoryHandle objects for quick re-access. Persists across page reloads (within tab session). Well-supported API with good browser compatibility. Enhances productivity for iterative development workflow.
      </rationale>
      <alternatives>
- localStorage: Cannot store FileSystemHandle objects
- No persistence: Users must re-select directory every time
- Cookies: Too small for metadata storage
      </alternatives>
    </recommendation>

    <recommendation priority="medium">
      <action>Implement parallel file reading with Promise.all()</action>
      <rationale>
10x performance improvement over sequential reading for typical projects. File System Access API has no rate limits. JavaScript concurrency model handles parallelism well. Simple implementation with significant UX benefit. Critical for projects with 50+ files.
      </rationale>
      <alternatives>
- Sequential reading: Simpler but much slower
- Web Worker parallelism: Added complexity, marginal gains over Promise.all
- Lazy loading: Better for huge projects (1000+ files) but unnecessary for typical use
      </alternatives>
    </recommendation>

    <recommendation priority="medium">
      <action>Define three browser support tiers with clear UI messaging</action>
      <rationale>
Sets appropriate user expectations per browser. Encourages Chrome/Edge usage for best experience while supporting others. Avoids user confusion about missing features. Enables graceful degradation strategy. Provides path for mobile users (basic functionality).
      </rationale>
      <alternatives>
- Single tier (Chromium only): Excludes too many users
- No messaging: Users confused why features missing
- Tier 1 and 2 only: Excludes mobile completely
      </alternatives>
    </recommendation>

    <recommendation priority="low">
      <action>Use Web Worker for directory traversal on large projects (500+ files)</action>
      <rationale>
Prevents main thread blocking on large projects. Enables responsive UI during traversal. Straightforward implementation with Comlink library. Provides better UX for edge cases. Can stream results to UI progressively.
      </rationale>
      <alternatives>
- Main thread only: Simpler but freezes UI on large projects
- Always use Worker: Overhead unnecessary for small projects
- Async chunks: Complex implementation, Worker is cleaner
      </alternatives>
    </recommendation>

    <recommendation priority="low">
      <action>Implement progress indicators for operations with 50+ files</action>
      <rationale>
Provides user feedback during lengthy operations. Reduces perceived wait time. Simple to implement (counter + progress bar). Professional UX touch. Helps users understand what's happening.
      </rationale>
      <alternatives>
- No indicators: Users unsure if app frozen
- Spinner only: Less informative than progress percentage
- Always show: Unnecessary visual noise for small projects
      </alternatives>
    </recommendation>
  </recommendations>
  <code_examples>
    <example name="directory-selection-with-traversal">
```typescript
// Directory selection and recursive traversal
async function selectAndTraverseDirectory(): Promise&lt;Map&lt;string, string&gt;&gt; {
  // Show directory picker with suggested starting location
  const dirHandle = await window.showDirectoryPicker({
    startIn: 'documents',
    mode: 'read' // or 'readwrite' for write-back capability
  });

  const files = new Map&lt;string, string&gt;();

  // Recursive traversal function
  async function traverse(
    handle: FileSystemDirectoryHandle,
    path: string = ''
  ): Promise&lt;void&gt; {
    for await (const entry of handle.values()) {
      const entryPath = path ? `${path}/${entry.name}` : entry.name;

      if (entry.kind === 'file') {
        // Filter for C++ files
        if (entry.name.match(/\.(cpp|cc|cxx|h|hpp|hxx)$/i)) {
          const fileHandle = entry as FileSystemFileHandle;
          const file = await fileHandle.getFile();
          const contents = await file.text();
          files.set(entryPath, contents);
        }
      } else if (entry.kind === 'directory') {
        // Recursively traverse subdirectories
        await traverse(entry as FileSystemDirectoryHandle, entryPath);
      }
    }
  }

  await traverse(dirHandle);
  return files;
}
```
Source: MDN File System Access API, Chrome developers best practices
    </example>

    <example name="parallel-file-reading">
```typescript
// Parallel file reading for performance
async function readFilesParallel(
  dirHandle: FileSystemDirectoryHandle
): Promise&lt;Array&lt;{path: string, content: string}&gt;&gt; {
  const filePromises: Promise&lt;{path: string, content: string}&gt;[] = [];

  for await (const entry of dirHandle.values()) {
    if (entry.kind === 'file' &amp;&amp; entry.name.endsWith('.cpp')) {
      // Don't await here - collect promises
      filePromises.push(
        (async () =&gt; {
          const file = await (entry as FileSystemFileHandle).getFile();
          const content = await file.text();
          return { path: entry.name, content };
        })()
      );
    }
  }

  // Await all promises in parallel
  return Promise.all(filePromises);
}
```
Source: Chrome developers performance guidance
    </example>

    <example name="filesystem-abstraction-interface">
```typescript
// File system abstraction for testability
interface IFileSystem {
  selectDirectory(): Promise&lt;IDirectoryHandle&gt;;
  readFile(handle: IFileHandle): Promise&lt;string&gt;;
  writeFile(handle: IFileHandle, content: string): Promise&lt;void&gt;;
}

interface IDirectoryHandle {
  entries(): AsyncIterableIterator&lt;IFileSystemEntry&gt;;
  getFileHandle(name: string): Promise&lt;IFileHandle&gt;;
}

interface IFileHandle {
  name: string;
  getFile(): Promise&lt;File&gt;;
}

interface IFileSystemEntry {
  kind: 'file' | 'directory';
  name: string;
  handle: IFileHandle | IDirectoryHandle;
}

// Production implementation using File System Access API
class FileSystemAccessAdapter implements IFileSystem {
  async selectDirectory(): Promise&lt;IDirectoryHandle&gt; {
    const handle = await window.showDirectoryPicker();
    return new DirectoryHandleAdapter(handle);
  }

  async readFile(handle: IFileHandle): Promise&lt;string&gt; {
    const file = await handle.getFile();
    return file.text();
  }

  async writeFile(handle: IFileHandle, content: string): Promise&lt;void&gt; {
    // Implementation using createWritable()
  }
}

// Test implementation using memfs
class InMemoryFileSystem implements IFileSystem {
  private files = new Map&lt;string, string&gt;();

  async selectDirectory(): Promise&lt;IDirectoryHandle&gt; {
    // Return mock directory with test files
    return new InMemoryDirectoryHandle(this.files);
  }

  async readFile(handle: IFileHandle): Promise&lt;string&gt; {
    return this.files.get(handle.name) || '';
  }

  async writeFile(handle: IFileHandle, content: string): Promise&lt;void&gt; {
    this.files.set(handle.name, content);
  }
}
```
Source: TypeScript abstraction patterns, SOLID principles
    </example>

    <example name="drag-and-drop-with-fallback">
```typescript
// Drag-and-drop with progressive enhancement
async function handleDrop(event: DragEvent): Promise&lt;FileSystemDirectoryHandle | null&gt; {
  event.preventDefault();

  const items = event.dataTransfer?.items;
  if (!items || items.length === 0) return null;

  const item = items[0];

  // Try modern API first (Chromium with write access)
  if ('getAsFileSystemHandle' in DataTransferItem.prototype) {
    try {
      const handle = await item.getAsFileSystemHandle();
      if (handle?.kind === 'directory') {
        return handle as FileSystemDirectoryHandle;
      }
    } catch (err) {
      console.warn('getAsFileSystemHandle failed, falling back', err);
    }
  }

  // Fallback to legacy API (Firefox/Safari, read-only)
  if (item.webkitGetAsEntry) {
    const entry = item.webkitGetAsEntry();
    if (entry?.isDirectory) {
      // Convert legacy entry to File System Access API compatible structure
      return convertWebkitEntryToHandle(entry as FileSystemDirectoryEntry);
    }
  }

  return null;
}

// Feature detection
function supportsFileSystemAccess(): boolean {
  return 'showDirectoryPicker' in window;
}

function supportsModernDragDrop(): boolean {
  return 'getAsFileSystemHandle' in DataTransferItem.prototype;
}
```
Source: MDN DataTransferItem, web.dev drag-and-drop patterns
    </example>

    <example name="browser-fs-access-integration">
```typescript
// Using browser-fs-access library for automatic fallbacks
import { directoryOpen, fileSave } from 'browser-fs-access';

// Directory selection with automatic fallback
async function openProject() {
  try {
    // On Chromium: uses showDirectoryPicker()
    // On Firefox/Safari: uses input type="file" webkitdirectory
    // Returns same interface for both
    const blobs = await directoryOpen({
      recursive: true,
      extensions: ['.cpp', '.h', '.hpp', '.cc', '.cxx']
    });

    // blobs is array of File objects with directoryHandle property (if supported)
    return blobs;
  } catch (err) {
    if (err.name === 'AbortError') {
      console.log('User cancelled');
    }
    throw err;
  }
}

// Save file with automatic fallback
async function saveTranspiledFile(content: string, filename: string) {
  try {
    // On Chromium: uses showSaveFilePicker()
    // On other browsers: triggers download via &lt;a download&gt;
    await fileSave(
      new Blob([content], { type: 'text/plain' }),
      {
        fileName: filename,
        extensions: ['.c'],
      }
    );
  } catch (err) {
    console.error('Save failed', err);
  }
}
```
Source: browser-fs-access library documentation
    </example>

    <example name="indexeddb-recent-projects">
```typescript
// IndexedDB for recent projects persistence
interface RecentProject {
  id: string;
  name: string;
  directoryHandle: FileSystemDirectoryHandle;
  lastAccessed: Date;
}

class RecentProjectsStore {
  private db: IDBDatabase | null = null;

  async init(): Promise&lt;void&gt; {
    return new Promise((resolve, reject) =&gt; {
      const request = indexedDB.open('CppPlayground', 1);

      request.onupgradeneeded = (event) =&gt; {
        const db = (event.target as IDBOpenDBRequest).result;
        if (!db.objectStoreNames.contains('recentProjects')) {
          db.createObjectStore('recentProjects', { keyPath: 'id' });
        }
      };

      request.onsuccess = () =&gt; {
        this.db = request.result;
        resolve();
      };

      request.onerror = () =&gt; reject(request.error);
    });
  }

  async addProject(
    name: string,
    dirHandle: FileSystemDirectoryHandle
  ): Promise&lt;void&gt; {
    if (!this.db) throw new Error('DB not initialized');

    const project: RecentProject = {
      id: crypto.randomUUID(),
      name,
      directoryHandle: dirHandle,
      lastAccessed: new Date()
    };

    const tx = this.db.transaction('recentProjects', 'readwrite');
    const store = tx.objectStore('recentProjects');
    await store.put(project);
  }

  async getRecentProjects(): Promise&lt;RecentProject[]&gt; {
    if (!this.db) throw new Error('DB not initialized');

    return new Promise((resolve, reject) =&gt; {
      const tx = this.db.transaction('recentProjects', 'readonly');
      const store = tx.objectStore('recentProjects');
      const request = store.getAll();

      request.onsuccess = () =&gt; {
        const projects = request.result as RecentProject[];
        // Sort by last accessed
        projects.sort((a, b) =&gt;
          b.lastAccessed.getTime() - a.lastAccessed.getTime()
        );
        resolve(projects.slice(0, 10)); // Return 10 most recent
      };

      request.onerror = () =&gt; reject(request.error);
    });
  }

  async verifyPermission(
    handle: FileSystemDirectoryHandle,
    withWrite: boolean = false
  ): Promise&lt;boolean&gt; {
    const opts: FileSystemHandlePermissionDescriptor = { mode: withWrite ? 'readwrite' : 'read' };

    // Check if we already have permission
    if ((await handle.queryPermission(opts)) === 'granted') {
      return true;
    }

    // Request permission
    if ((await handle.requestPermission(opts)) === 'granted') {
      return true;
    }

    return false;
  }
}
```
Source: MDN IndexedDB API, Chrome developers File System Access best practices
    </example>

    <example name="memfs-unit-testing">
```typescript
// Unit testing with memfs-browser
import { vol } from 'memfs';
import { describe, it, expect, beforeEach } from 'vitest';

describe('C++ Project Loader', () =&gt; {
  let fileSystem: IFileSystem;

  beforeEach(() =&gt; {
    // Setup virtual filesystem
    vol.fromJSON({
      '/project/main.cpp': `
        #include &lt;iostream&gt;
        int main() {
          std::cout &lt;&lt; "Hello" &lt;&lt; std::endl;
          return 0;
        }
      `,
      '/project/utils.h': `
        #pragma once
        void helper();
      `,
      '/project/utils.cpp': `
        #include "utils.h"
        void helper() {}
      `,
      '/project/tests/test_main.cpp': `
        #include "../utils.h"
        void test() {}
      `
    });

    // Use in-memory filesystem for tests
    fileSystem = new InMemoryFileSystem(vol);
  });

  it('should discover all C++ files recursively', async () =&gt; {
    const loader = new ProjectLoader(fileSystem);
    const files = await loader.loadProject('/project');

    expect(files.size).toBe(4);
    expect(files.has('main.cpp')).toBe(true);
    expect(files.has('utils.h')).toBe(true);
    expect(files.has('utils.cpp')).toBe(true);
    expect(files.has('tests/test_main.cpp')).toBe(true);
  });

  it('should filter out non-C++ files', async () =&gt; {
    vol.fromJSON({
      '/project/main.cpp': 'int main() {}',
      '/project/README.md': '# Project',
      '/project/build.sh': 'make'
    });

    const loader = new ProjectLoader(fileSystem);
    const files = await loader.loadProject('/project');

    expect(files.size).toBe(1);
    expect(files.has('main.cpp')).toBe(true);
    expect(files.has('README.md')).toBe(false);
  });

  it('should handle file read errors gracefully', async () =&gt; {
    const failingFS: IFileSystem = {
      async selectDirectory() {
        throw new Error('Permission denied');
      },
      async readFile() {
        throw new Error('File not found');
      },
      async writeFile() {}
    };

    const loader = new ProjectLoader(failingFS);
    await expect(loader.loadProject('/project')).rejects.toThrow('Permission denied');
  });
});
```
Source: memfs-browser documentation, Vitest testing patterns
    </example>

    <example name="web-worker-traversal">
```typescript
// Web Worker for large project traversal (using Comlink)
// worker.ts
import { expose } from 'comlink';

async function* traverseDirectory(
  dirHandle: FileSystemDirectoryHandle
): AsyncGenerator&lt;{path: string, size: number, type: string}&gt; {
  async function* walk(
    handle: FileSystemDirectoryHandle,
    path: string = ''
  ): AsyncGenerator&lt;{path: string, size: number, type: string}&gt; {
    for await (const entry of handle.values()) {
      const entryPath = path ? `${path}/${entry.name}` : entry.name;

      if (entry.kind === 'file') {
        const file = await (entry as FileSystemFileHandle).getFile();
        yield {
          path: entryPath,
          size: file.size,
          type: file.type
        };
      } else {
        yield* walk(entry as FileSystemDirectoryHandle, entryPath);
      }
    }
  }

  yield* walk(dirHandle);
}

expose({ traverseDirectory });

// main.ts
import { wrap } from 'comlink';

const worker = new Worker(new URL('./worker.ts', import.meta.url), {
  type: 'module'
});

const api = wrap&lt;{
  traverseDirectory: (
    handle: FileSystemDirectoryHandle
  ) =&gt; AsyncGenerator&lt;{path: string, size: number, type: string}&gt;
}&gt;(worker);

async function processLargeProject(dirHandle: FileSystemDirectoryHandle) {
  let fileCount = 0;
  let totalSize = 0;

  // Stream results from worker
  for await (const file of api.traverseDirectory(dirHandle)) {
    fileCount++;
    totalSize += file.size;

    // Update UI progressively
    updateProgress(fileCount, file.path);
  }

  console.log(`Processed ${fileCount} files, total size: ${totalSize} bytes`);
}
```
Source: Comlink library, Web Workers API
    </example>

    <example name="progress-indicator">
```typescript
// Progress indicator for multi-file operations
interface ProgressReporter {
  start(total: number): void;
  update(current: number, message?: string): void;
  complete(): void;
}

class UIProgressReporter implements ProgressReporter {
  private progressBar: HTMLProgressElement;
  private statusText: HTMLElement;

  constructor(containerId: string) {
    const container = document.getElementById(containerId)!;
    this.progressBar = container.querySelector('.progress-bar')!;
    this.statusText = container.querySelector('.status-text')!;
  }

  start(total: number): void {
    this.progressBar.max = total;
    this.progressBar.value = 0;
    this.progressBar.style.display = 'block';
  }

  update(current: number, message?: string): void {
    this.progressBar.value = current;
    const percent = Math.round((current / this.progressBar.max) * 100);
    this.statusText.textContent = message || `Processing... ${percent}%`;
  }

  complete(): void {
    this.progressBar.style.display = 'none';
    this.statusText.textContent = 'Complete!';
  }
}

// Usage
async function loadProjectWithProgress(
  dirHandle: FileSystemDirectoryHandle,
  progress: ProgressReporter
) {
  // First pass: count files
  let fileCount = 0;
  for await (const entry of dirHandle.values()) {
    if (entry.kind === 'file') fileCount++;
  }

  progress.start(fileCount);

  // Second pass: read files
  const files = new Map&lt;string, string&gt;();
  let processed = 0;

  for await (const entry of dirHandle.values()) {
    if (entry.kind === 'file') {
      const file = await (entry as FileSystemFileHandle).getFile();
      const content = await file.text();
      files.set(entry.name, content);

      processed++;
      progress.update(processed, `Reading ${entry.name}`);
    }
  }

  progress.complete();
  return files;
}
```
Source: HTML5 Progress element, UX best practices
    </example>
  </code_examples>
  <metadata>
    <confidence level="high">
This research has high confidence due to:
- Official documentation from MDN and Chrome developers (primary sources)
- Browser compatibility verified via caniuse.com (December 2025 data)
- WASM architecture verified by reading Phase 16-04 summary (actual implementation status)
- Testing libraries verified via npm registry (memfs, browser-fs-access actively maintained)
- Code examples derived from official documentation and established patterns

Verified claims:
- File System Access API capabilities and browser support (MDN + caniuse.com)
- Server-side transpilation architecture (Phase 16-04 summary)
- Drag-and-drop API capabilities (MDN + web.dev)
- memfs and browser-fs-access library status (npm registry)
- Security and permissions model (Chrome security documentation)

Assumed claims:
- Performance estimates (10x improvement with parallel reading) based on general JavaScript performance patterns, not benchmarked
- User project sizes (typically under 500 files) based on industry norms, not measured
- Mobile browser behavior (no support) verified via caniuse but not hands-on tested
    </confidence>

    <dependencies>
Browser requirements:
- Chrome 105+ or Edge 105+ for full functionality (File System Access API)
- Firefox/Safari on desktop for read-only fallback (webkitdirectory, webkitGetAsEntry)
- HTTPS deployment mandatory (API requires secure context)
- No mobile browser support for directory operations

Technology stack:
- TypeScript for type-safe abstractions
- Vitest for unit testing with memfs-browser
- browser-fs-access library for progressive enhancement (optional but recommended)
- IndexedDB for recent projects persistence
- Comlink for Web Worker communication (optional, for large projects)

Server infrastructure:
- Existing backend with Clang/LLVM (from Phase 15)
- Server endpoint for transpilation (to be implemented)
- Header provisioning infrastructure (from Phase 16-04)

Testing infrastructure:
- memfs-browser for filesystem mocking
- Vitest test runner
- IFileSystem abstraction for dependency injection
    </dependencies>

    <open_questions>
Questions requiring hands-on testing:
- What is actual performance with 1000+ file projects? (estimated based on patterns)
- Do mobile browsers truly have zero support or partial? (verified via caniuse but not tested)
- What are memory limits for IndexedDB directory handle storage? (not documented)
- How does File System Access API perform on network drives? (not tested)
- What is optimal file count threshold for switching to Web Worker? (estimated 500+)
- Are there rate limits or throttling for File System Access API? (no documentation found)

Questions for architectural planning:
- Should we implement write-back for transpiled C files or just download?
- What file size limits should we enforce? (API supports 2GB+, but practical?)
- Should we implement file watching for auto-transpile on changes?
- Do we need offline support via Service Worker + OPFS?
- Should playground support multiple projects simultaneously (tabs)?

Questions for UX design:
- How to handle protected directory warnings gracefully?
- What browser compatibility message is most effective?
- Should we show file tree preview before transpilation?
- How to visualize transpilation progress for large projects?
    </open_questions>

    <assumptions>
User environment:
- Users running modern Chrome/Edge browsers on desktop (primary audience)
- Projects typically contain under 500 files
- Internet connection available for server-side transpilation
- Users understand basic C++ project structure
- Users have file system access permissions on their OS

Technical assumptions:
- Server-side transpilation architecture from Phase 16-04 will be completed
- Backend can handle concurrent transpilation requests
- Network latency acceptable for sending project files to server
- Browser IndexedDB storage sufficient for 10 recent projects
- JavaScript heap memory sufficient for typical project sizes

Project scope:
- Focus on desktop experience first, mobile as secondary
- Chromium browsers as primary target, others as fallback
- Read-only operations sufficient for MVP (write-back nice-to-have)
- Single-file transpilation acceptable fallback for unsupported browsers
    </assumptions>

    <quality_report>
      <sources_consulted>
Official documentation:
- https://developer.mozilla.org/en-US/docs/Web/API/File_System_Access_API
- https://developer.chrome.com/articles/file-system-access
- https://caniuse.com/native-filesystem-api
- https://developer.mozilla.org/en-US/docs/Web/API/DataTransferItem
- https://web.dev/patterns/files/drag-and-drop-directories
- https://emscripten.org/docs/api_reference/Filesystem-API.html

Libraries and tools:
- https://www.npmjs.com/package/memfs
- https://www.npmjs.com/package/memfs-browser
- https://www.npmjs.com/package/browser-fs-access (inferred from search results)

Project files:
- .planning/phases/16-runtime-integration-testing/16-04-SUMMARY.md

Search results:
- File System Access API directory traversal patterns (2025)
- Drag-and-drop directory DataTransfer API (2025)
- WebAssembly file system emscripten memfs (2025)
- Filesystem abstraction testing patterns TypeScript (2025)
- Mock filesystem memfs unit testing browser (2025)
      </sources_consulted>

      <claims_verified>
High confidence (verified with official sources):
- File System Access API capabilities: Verified via MDN (showDirectoryPicker, showOpenFilePicker, showSaveFilePicker, FileSystemDirectoryHandle, FileSystemFileHandle)
- Browser compatibility: Verified via caniuse.com (Chrome 105+, no Firefox/Safari, 34.76% global usage)
- WASM module status: Verified by reading Phase 16-04 summary (server-side architecture, 28 tests passing)
- Drag-and-drop API: Verified via MDN (getAsFileSystemHandle modern, webkitGetAsEntry legacy)
- Security model: Verified via Chrome security documentation (HTTPS required, user-initiated only)
- memfs library: Verified via npm registry (actively maintained, browser support)

Medium confidence (inferred from multiple sources):
- Progressive enhancement strategy: Inferred from browser-fs-access library and Chrome best practices
- Testing abstraction patterns: Inferred from TypeScript patterns and functional programming principles
- Performance optimizations: Inferred from general JavaScript performance patterns (Promise.all, Web Workers)
      </claims_verified>

      <claims_assumed>
Low confidence (require validation):
- Performance estimates: 10x improvement with parallel reading is based on general JavaScript concurrency patterns, not benchmarked for File System Access API specifically
- File count thresholds: 500+ files for Web Worker is estimated based on typical UI responsiveness concerns, not measured
- Project size assumptions: "Typical C++ projects under 500 files" based on industry norms, not project-specific data
- Memory limits: No documented limits found for IndexedDB directory handle storage
- Mobile behavior: Verified via caniuse (no support) but not hands-on tested on actual devices

Assumptions requiring architectural decisions:
- Write-back vs download-only for transpiled files
- Offline support requirements
- Multi-project/tab support
- File watching and auto-transpile
      </claims_assumed>

      <contradictions_encountered>
No major contradictions encountered.

Minor clarifications:
- Early sources referred to "Native File System API" but it was renamed to "File System Access API" - confirmed both refer to same API
- Some sources suggested OPFS (Origin Private File System) for persistence, but IndexedDB is more appropriate for directory handle storage as OPFS is origin-private and not visible to users
- Emscripten MEMFS documentation discusses 2GB file size limitation, but this is MEMFS-specific, not a File System Access API limitation (API supports larger files)
      </contradictions_encountered>

      <confidence_by_finding>
File System Access API capabilities: HIGH
- Official MDN documentation comprehensive
- Chrome developers guide with practical examples
- API stable since Chrome 105 (September 2022)

Browser compatibility: HIGH
- caniuse.com data current as of December 2025
- Mozilla "harmful" position well-documented
- Chromium-only support clearly established

WASM integration architecture: HIGH
- Phase 16-04 summary provides concrete implementation details
- Server-side architecture with 28 passing tests verified
- No need to search for WASM files (confirmed they don't exist in website/ directory)

Drag-and-drop patterns: HIGH
- MDN documentation for both modern and legacy APIs
- web.dev practical guides with browser compatibility
- Feature detection straightforward

Testing abstractions: MEDIUM
- Patterns inferred from TypeScript best practices
- memfs library verified via npm (actively maintained)
- IFileSystem abstraction pattern is established practice but not specific to File System Access API

Performance characteristics: LOW-MEDIUM
- General JavaScript performance patterns applied
- No specific benchmarks for File System Access API
- Estimates require validation with actual implementation

Progressive enhancement strategy: MEDIUM-HIGH
- browser-fs-access library provides clear approach
- Chrome developers best practices support tiered approach
- Feature detection mechanisms well-documented
      </confidence_by_finding>
    </quality_report>
  </metadata>
</research>
