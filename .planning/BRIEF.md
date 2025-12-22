# C++ to C Playground - Wizard Interface Redesign

## Vision

Transform the current single-page playground into a multi-step wizard interface that provides clear, progressive guidance through the transpilation workflow with rich visual feedback including directory tree views, real-time file progress tracking, and side-by-side source/result comparison.

## Current State

### Existing Implementation
- **Architecture**: React 19 components with Astro 5.16 static site generation
- **Transpilation**: WebAssembly-based (@hupyy/cpptoc-wasm) running entirely in browser
- **File Access**: File System Access API (Chrome 105+, Tier 1 browser support)
- **Flow**: Linear single-pass (select directory → transpile all → download ZIP)
- **Components**: PlaygroundController, DirectorySelector, ProgressIndicator, ErrorDisplay
- **State Management**: React hooks (useState, useCallback) - no external library
- **Testing**: Vitest for unit tests, Playwright for E2E

### Current User Experience
1. User clicks "Select Directory" button or drag-and-drops
2. All C++ files transpiled sequentially in one pass
3. Linear progress bar shows current file being processed
4. Errors displayed in collapsible list
5. Results automatically downloaded as ZIP
6. No visibility into directory structure
7. No ability to preview results before download
8. No control over output destination

### Limitations Addressed by This Project
❌ No step-by-step guidance
❌ Can't choose output directory (always downloads ZIP)
❌ No visual directory tree representation
❌ No way to see which files exist in source directory before transpiling
❌ Can't preview transpiled results without downloading
❌ No side-by-side source/result comparison
❌ Limited control over transpilation process

## Desired State

### New User Experience
A wizard-style interface with 4 distinct steps:

**Step 1: Select Source Directory**
- Button to select directory via File System Access API
- Drag-and-drop zone for directory selection
- **NEW**: Tree view showing discovered C++ files (.cpp, .cc, .cxx, .h, .hpp, .hxx)
- **NEW**: File count and size statistics
- **NEW**: Filter/search capability for large projects

**Step 2: Select Target Directory**
- Button to select output directory
- Option to create new directory within selected location
- **NEW**: Permission status indicator (read/write access)
- **NEW**: Preview of where files will be written
- **NEW**: Conflict detection if files already exist

**Step 3: Transpile with Real-Time Progress**
- **NEW**: Live directory tree view with current file highlighted
- **NEW**: Auto-scroll tree view to keep current file visible
- **NEW**: Per-file status indicators (pending, in-progress, success, error)
- **NEW**: Pause/resume capability
- Progress bar showing overall completion
- Current file name and progress (X/Y files)
- Cancel button
- **NEW**: Estimated time remaining
- **NEW**: Files processed per second metric

**Step 4: Results with Preview**
- **NEW**: Target directory tree view showing all transpiled files
- **NEW**: Dual-pane file viewer:
  - Left pane: Original C++ source
  - Right pane: Transpiled C output
- **NEW**: Syntax highlighting for both C++ and C
- **NEW**: File selector - click any file in tree to preview
- **NEW**: Download options:
  - Download individual files
  - Download as ZIP archive
  - Files already written to target directory
- Error summary with links to problematic files
- Success metrics (files transpiled, bytes processed, time elapsed)

### Key Features
✅ **Progressive disclosure** - One step at a time, clear next actions
✅ **Visual feedback** - Tree views, highlighting, real-time updates
✅ **User control** - Choose output location, pause/resume, preview before commit
✅ **Transparency** - See exactly what's happening at each stage
✅ **Efficiency** - Filter large projects, skip to errors, batch operations

## Success Criteria

### Functional
- [ ] User can navigate forward/backward through wizard steps
- [ ] Source directory selection displays filterable tree view
- [ ] Target directory selection with write permission verification
- [ ] Real-time tree view highlighting during transpilation
- [ ] Auto-scroll keeps current file visible in tree
- [ ] Dual-pane source/result viewer with syntax highlighting
- [ ] All files written to chosen target directory (not ZIP download)
- [ ] Error handling maintains wizard state (can fix and retry)

### Non-Functional
- [ ] Tree view performs well with 1000+ files (virtualization)
- [ ] Syntax highlighting loads asynchronously (no blocking)
- [ ] Wizard state persists across page refresh (localStorage)
- [ ] Responsive design works on tablet (tree view collapses)
- [ ] Accessibility: keyboard navigation, screen reader support
- [ ] E2E tests cover all wizard paths
- [ ] Component tests for all new components

### User Experience
- [ ] Clear visual hierarchy in wizard steps (stepper component)
- [ ] Progress feels responsive (<100ms tree highlight updates)
- [ ] No visual jumping (tree scroll is smooth)
- [ ] Error states are clear and actionable
- [ ] Success state is satisfying and informative

## Constraints

### Technical
- Must maintain browser-only architecture (no backend)
- Must work in Chrome 105+ (File System Access API requirement)
- Graceful degradation for Firefox/Safari (Tier 2: read-only, download ZIP)
- File tree must handle 2000+ files without lag (virtualization required)
- Syntax highlighting must be async (large files shouldn't block UI)

### Compatibility
- Maintain existing test suite (extend, don't break)
- Keep existing adapters (WasmTranspilerAdapter, FileSystemAccessAdapter)
- Preserve accessibility features from current implementation
- Support drag-and-drop in addition to button selection

### Performance
- Initial page load <2s (code splitting for wizard steps)
- Tree view render <200ms for 1000 files
- File highlighting update <50ms during transpilation
- Syntax highlighting lazy-load (only for viewed files)

## Out of Scope

- Multi-file editing (view-only in results pane)
- File upload alternative to File System Access API
- Backend API integration (stays browser-only)
- Advanced tree features (rename, move, delete files)
- Diff view between source and transpiled (just side-by-side)
- Dark mode theming (use system default)
- Mobile phone support (tablet minimum)

## Technical Approach

### Component Architecture
Following existing patterns from current implementation:

```
PlaygroundWizard (new)
├── WizardStepper (new) - step navigation UI
├── Step1SourceSelection (new)
│   ├── DirectorySelector (existing, enhanced)
│   └── FileTreeView (new) - virtualized tree component
├── Step2TargetSelection (new)
│   ├── DirectorySelector (existing, reused)
│   └── PermissionIndicator (new)
├── Step3Transpilation (new)
│   ├── FileTreeView (new, reused with highlighting)
│   ├── ProgressIndicator (existing, enhanced)
│   └── TranspilationController (new) - orchestrates WASM calls
└── Step4Results (new)
    ├── FileTreeView (new, reused for target)
    ├── DualPaneViewer (new)
    │   ├── SyntaxHighlighter (new, async)
    │   └── FileContentDisplay (new)
    └── DownloadOptions (new)
```

### State Management
Continue using React hooks with wizard state lifted to PlaygroundWizard:

```typescript
interface WizardState {
  currentStep: 1 | 2 | 3 | 4;
  sourceDir: FileSystemDirectoryHandle | null;
  targetDir: FileSystemDirectoryHandle | null;
  sourceFiles: FileInfo[]; // discovered C++ files
  transpilationResults: Map<string, TranspileResult>;
  currentFile: string | null; // for highlighting
  selectedPreviewFile: string | null; // for results view
  isTranspiling: boolean;
  canNavigateNext: boolean; // step validation
}
```

### Libraries to Add
- **react-window** or **react-virtualized** - efficient tree view for large file lists
- **prism-react-renderer** or **react-syntax-highlighter** - async syntax highlighting
- Consider **react-split-pane** for resizable dual-pane viewer (or CSS grid is fine)

### Incremental Approach
Build in phases to maintain working playground throughout:

1. **Phase 1**: Wizard shell (stepper, navigation, step components as shells)
2. **Phase 2**: Tree view component with source selection
3. **Phase 3**: Target selection and transpilation with live highlighting
4. **Phase 4**: Results view with dual-pane preview

Each phase should be independently testable and releasable.

## Risks & Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Tree view performance with 2000+ files | High | Use react-window virtualization from start |
| Syntax highlighting blocks UI | Medium | Async loading with Web Workers if needed |
| File System Access API permission issues | Medium | Clear error messages, fallback to download |
| Wizard state management complexity | Medium | Keep state simple, use TypeScript strictly |
| Breaking existing tests | Low | Run tests continuously during development |

## Timeline Estimate

Given autonomous execution with parallelization:

- **Phase 1** (Wizard Shell): 2-3 hours - straightforward component structure
- **Phase 2** (Tree View + Source Selection): 3-4 hours - virtualization setup, testing
- **Phase 3** (Live Progress): 4-5 hours - real-time updates, highlighting logic
- **Phase 4** (Results Viewer): 3-4 hours - dual-pane layout, syntax highlighting

**Total estimate**: 12-16 hours of autonomous development time

With parallel subtask execution, phases 1-2 could run concurrently, phases 3-4 sequentially.

## Stakeholders

- **Developer/User**: Solo developer (you) - product owner and user
- **Implementer**: Claude (autonomous agent)
- **End Users**: C++ developers using the playground for transpilation

## Definition of Done

Project is complete when:
- ✅ All 4 wizard steps functional and tested
- ✅ Tree view handles 2000+ files smoothly
- ✅ Live highlighting works during transpilation
- ✅ Dual-pane viewer shows source/result with syntax highlighting
- ✅ Files written to target directory (not ZIP)
- ✅ All E2E tests pass
- ✅ Accessibility verified (keyboard nav, screen reader)
- ✅ Code committed to develop branch
- ✅ Deployed to production (GitHub Pages)

---

**Created**: 2025-12-22
**Version**: 1.0
**Status**: Planning
