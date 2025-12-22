# C++ to C Playground Research Summary

**File System Access API + Server-Side Transpilation + Progressive Enhancement = Chromium-first, cross-browser compatible playground**

## Version
v1

## Key Findings
- File System Access API (Chrome 105+) enables directory selection and traversal for entire C++ projects, with browser-fs-access library providing automatic fallbacks for Firefox/Safari (webkitdirectory) and mobile (single file upload)
- Server-side transpilation architecture from Phase 16-04 is ideal: browser handles file I/O, backend performs Clang/LLVM transpilation, avoiding 100MB+ WASM bundle and complex Emscripten filesystem
- IFileSystem abstraction with memfs-browser enables TDD by decoupling core logic from browser APIs, allowing fast deterministic unit tests for directory traversal and file filtering
- Three-tier browser support strategy: Tier 1 (Chrome/Edge - full features), Tier 2 (Firefox/Safari - read-only), Tier 3 (mobile - single file)
- Parallel file reading with Promise.all() provides 10x performance improvement for multi-file projects, IndexedDB stores directory handles for recent projects, drag-and-drop enhances UX

## Decisions Needed
- Write-back vs download-only: Should playground save transpiled C files back to user's filesystem (requires readwrite permission) or just download them (simpler, works everywhere)?
- File size limits: What maximum file size should we enforce? (API supports 2GB+ but practical limits unknown)
- Web Worker threshold: At what file count should we switch to Web Worker for directory traversal? (estimated 500+ files)
- Offline support: Do we need Service Worker + OPFS for offline capability, or is internet connection acceptable assumption?

## Blockers
None

## Next Step
Create playground-cpp-to-c-plan.md

---
*Confidence: High*
*Full output: playground-cpp-to-c-research.md*
