# C++ to C Playground Architecture Plan Summary

**Vertical slice architecture with 6 phases, File System Access API + WASM integration, progressive enhancement across 3 browser tiers**

## Version
v1

## Key Findings
- **Architecture Approach**: Vertical slicing organizes code by feature capability (file-selection, transpile, progress) rather than technical layers, with SOLID principles applied throughout (Single Responsibility, Dependency Inversion via interfaces, Open/Closed via adapters)
- **Technology Stack**: TypeScript + Astro + React for UI, File System Access API for directory selection, server-side Clang/LLVM transpilation (Phase 16-04 infrastructure), browser-fs-access for progressive enhancement, memfs-browser for TDD
- **Testing Strategy**: Three-tier approach with unit tests (MockFileSystem, MockTranspiler), integration tests (browser-fs-access fallbacks, MSW for backend API), and E2E tests (Playwright with synthetic C++ projects of 10/50/100/500 files)
- **Browser Support**: Tier 1 (Chrome/Edge 105+ full features), Tier 2 (Firefox/Safari read-only via webkitdirectory), Tier 3 (mobile single file upload)
- **6 Implementation Phases**: (1) Foundation (interfaces, mocks, test infrastructure), (2) Backend Transpiler Adapter (HTTP client for Phase 16-04 API), (3) File System Adapter (File System Access API integration), (4) Transpile Service (orchestration with parallel processing), (5) UI Components (React components for interaction), (6) Integration & E2E (wiring, performance testing, cross-browser validation)
- **6 Mermaid Diagrams**: System context (browser + backend + filesystem), container (UI/features/adapters), component (vertical slices with DI), sequence (end-to-end transpilation flow), class (interface hierarchy with implementations), data flow (file processing pipeline)

## Decisions Needed
- **Write-back vs Download**: Should playground save transpiled C files back to user's filesystem (requires readwrite permission, Chromium only) or just download them (simpler, works everywhere)? **Recommendation**: Download-only for MVP, add write-back based on user feedback.
- **File Size Limit**: What maximum individual file size? **Recommendation**: 10MB per file to prevent memory issues (most C++ files are <1MB).
- **Web Worker Threshold**: At what file count switch to Web Worker for directory traversal? **Recommendation**: 500+ files based on UI responsiveness, validate with real projects in Phase 6.
- **Offline Support**: Do we need Service Worker + OPFS for offline mode? **Recommendation**: No for MVP (requires client-side WASM with 100MB+ bundle, contradicts server-side architecture).

## Blockers
None

## Next Step
Execute Phase 1: Foundation - Create core interfaces (IFileSystem, ITranspiler, IProgressReporter), implement MockFileSystem and MockTranspiler with 100% test coverage, configure Vitest test infrastructure with memfs-browser, set up ESLint/Prettier with strict TypeScript rules

---
*Confidence: High*
*Full output: playground-cpp-to-c-plan.md*
