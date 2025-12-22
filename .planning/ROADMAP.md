# C++ to C Playground Wizard - Development Roadmap

**Project**: Wizard Interface Redesign
**Brief**: `.planning/BRIEF.md`
**Timeline**: 12-16 hours autonomous development
**Approach**: Incremental phases, each independently testable and releasable

---

## Milestone: v1.0 - Wizard Interface Launch

**Target**: Complete wizard-style playground with tree views and live progress

**Scope**: 4 phases, 18 atomic plans

---

## Phase 1: Wizard Foundation & Navigation

**Goal**: Create wizard shell with step navigation and state management

**Deliverables**:
- Wizard stepper component (progress indicator at top)
- Step navigation logic (next/back/skip)
- Wizard state management (current step, validation)
- Shell components for each step (no functionality yet)
- Basic E2E tests for navigation

**Dependencies**: None (greenfield)

**Plans**:

### 01-01: Wizard Stepper Component
**Scope**: Visual stepper + navigation controls
**Tasks**:
1. Create `WizardStepper.tsx` with step indicator UI (1/2/3/4 circles)
2. Add next/back button components with disabled states
3. Write component tests for stepper rendering and click handlers

**Files**: `src/components/playground/wizard/WizardStepper.tsx`, tests
**Verify**: Stepper renders 4 steps, highlights current, buttons work
**Estimate**: 1-2 hours

### 01-02: Wizard State & Step Shells
**Scope**: Central state management + empty step components
**Tasks**:
1. Create `PlaygroundWizard.tsx` with wizard state hook
2. Create shell components for each step (Step1Source, Step2Target, Step3Transpile, Step4Results)
3. Implement step transition logic with validation rules

**Files**: `src/components/playground/wizard/PlaygroundWizard.tsx`, step shells
**Verify**: Can navigate through all 4 steps, back button works, validation blocks invalid transitions
**Estimate**: 1-2 hours

### 01-03: Wizard E2E Tests
**Scope**: End-to-end test coverage for wizard navigation
**Tasks**:
1. Create `wizard-navigation.spec.ts` for step transitions
2. Test forward/backward navigation paths
3. Test validation rules (can't proceed without data)

**Files**: `tests/e2e/specs/wizard-navigation.spec.ts`
**Verify**: All navigation paths tested, validation works
**Estimate**: 1 hour

**Phase 1 Complete When**: Can navigate through wizard steps, tests pass

---

## Phase 2: File Tree View & Source Selection

**Goal**: Rich directory tree visualization with virtualization for performance

**Deliverables**:
- Reusable FileTreeView component (virtualized for 1000+ files)
- Source directory selection with tree display
- File filtering and search
- Component and E2E tests

**Dependencies**: Phase 1 (wizard shell must exist)

**Plans**:

### 02-01: FileTreeView Component Foundation
**Scope**: Basic tree rendering with expand/collapse
**Tasks**:
1. Create `FileTreeView.tsx` with recursive tree structure
2. Implement expand/collapse logic for folders
3. Add file/folder icons and indentation styling

**Files**: `src/components/playground/wizard/FileTreeView.tsx`
**Verify**: Tree renders nested structure, folders expand/collapse
**Estimate**: 2 hours

### 02-02: Tree Virtualization
**Scope**: Add react-window for performance with large file lists
**Tasks**:
1. Install and configure `react-window`
2. Refactor FileTreeView to use VariableSizeList
3. Benchmark with 2000-file test project

**Files**: `package.json`, `FileTreeView.tsx`
**Verify**: Tree handles 2000+ files smoothly (<200ms render)
**Estimate**: 2 hours

### 02-03: Source Selection Integration
**Scope**: Wire tree view to Step 1 with file discovery
**Tasks**:
1. Enhance `Step1SourceSelection.tsx` to use FileTreeView
2. Add file filtering (show only C++ files: .cpp, .h, etc.)
3. Display file count and size statistics

**Files**: `Step1SourceSelection.tsx`
**Verify**: Selecting directory populates tree, only C++ files shown
**Estimate**: 1-2 hours

### 02-04: Tree View Tests
**Scope**: Unit and E2E tests for tree component
**Tasks**:
1. Unit tests for FileTreeView (expand/collapse, rendering)
2. E2E test for source selection flow
3. Performance test with large directory

**Files**: `FileTreeView.test.tsx`, `wizard-source-selection.spec.ts`
**Verify**: Tests pass, coverage >80%
**Estimate**: 1-2 hours

**Phase 2 Complete When**: Tree view works with large projects, source selection integrated

---

## Phase 3: Target Selection & Live Transpilation

**Goal**: Target directory selection + real-time transpilation with live tree highlighting

**Deliverables**:
- Target directory selection with permission checking
- Live tree view highlighting during transpilation
- Auto-scroll to keep current file visible
- Pause/resume transpilation
- Progress metrics (files/sec, ETA)

**Dependencies**: Phase 2 (tree view component must exist)

**Plans**:

### 03-01: Target Directory Selection
**Scope**: Step 2 with target directory picker
**Tasks**:
1. Implement `Step2TargetSelection.tsx` with directory picker
2. Add permission verification (can write to target)
3. Display target path and permission status

**Files**: `Step2TargetSelection.tsx`
**Verify**: Can select target directory, permission status shown
**Estimate**: 1 hour

### 03-02: Conflict Detection
**Scope**: Check for existing files in target directory
**Tasks**:
1. Add file conflict detection (compare source file names with target contents)
2. Display warning if files will be overwritten
3. Add option to proceed or choose different directory

**Files**: `Step2TargetSelection.tsx`
**Verify**: Conflicts detected and displayed, user can choose action
**Estimate**: 1-2 hours

### 03-03: Live Transpilation Controller
**Scope**: Step 3 with real-time transpilation
**Tasks**:
1. Create `TranspilationController.tsx` orchestrating WASM transpiler
2. Implement sequential file processing with progress updates
3. Emit events for current file (for tree highlighting)

**Files**: `TranspilationController.tsx`, `Step3Transpilation.tsx`
**Verify**: Transpiles files sequentially, emits progress events
**Estimate**: 2 hours

### 03-04: Live Tree Highlighting
**Scope**: Real-time tree updates during transpilation
**Tasks**:
1. Enhance FileTreeView to accept `currentFile` prop for highlighting
2. Implement auto-scroll logic to keep highlighted file visible
3. Add status icons (pending/in-progress/success/error) per file

**Files**: `FileTreeView.tsx`, `Step3Transpilation.tsx`
**Verify**: Current file highlighted in tree, auto-scrolls, status icons update
**Estimate**: 2-3 hours

### 03-05: Pause/Resume & Metrics
**Scope**: User controls and progress metrics
**Tasks**:
1. Add pause/resume buttons to Step 3
2. Implement abort controller logic for pausing
3. Calculate and display metrics (files/sec, ETA)

**Files**: `TranspilationController.tsx`, `Step3Transpilation.tsx`
**Verify**: Can pause and resume, metrics displayed and accurate
**Estimate**: 1-2 hours

### 03-06: Transpilation Flow Tests
**Scope**: E2E tests for full transpilation workflow
**Tasks**:
1. E2E test for Step 2 (target selection)
2. E2E test for Step 3 (transpilation with highlighting)
3. Test pause/resume functionality

**Files**: `wizard-transpilation.spec.ts`
**Verify**: All transpilation scenarios tested
**Estimate**: 2 hours

**Phase 3 Complete When**: Can transpile with live tree highlighting, pause/resume works

---

## Phase 4: Results Preview & Download

**Goal**: Dual-pane source/result viewer with syntax highlighting

**Deliverables**:
- Target directory tree view showing transpiled files
- Dual-pane file viewer (source | transpiled)
- Async syntax highlighting for both C++ and C
- Download options (individual files, ZIP)
- Success metrics and error summary

**Dependencies**: Phase 3 (transpilation must be complete)

**Plans**:

### 04-01: Dual-Pane Viewer Layout
**Scope**: Split-pane component with file content display
**Tasks**:
1. Create `DualPaneViewer.tsx` with left/right panes
2. Add `FileContentDisplay.tsx` for text rendering
3. Implement resizable split (CSS grid or react-split-pane)

**Files**: `DualPaneViewer.tsx`, `FileContentDisplay.tsx`
**Verify**: Dual panes render, can resize split
**Estimate**: 1-2 hours

### 04-02: Syntax Highlighting
**Scope**: Async syntax highlighting with Prism
**Tasks**:
1. Install `prism-react-renderer` or `react-syntax-highlighter`
2. Create `SyntaxHighlighter.tsx` with async loading
3. Support C++ and C languages

**Files**: `package.json`, `SyntaxHighlighter.tsx`
**Verify**: Code highlighted correctly, loads asynchronously
**Estimate**: 1-2 hours

### 04-03: Results Step Integration
**Scope**: Wire dual-pane viewer to Step 4
**Tasks**:
1. Implement `Step4Results.tsx` with target tree view and dual-pane viewer
2. Add file selection logic (click file in tree → load in viewer)
3. Load source and transpiled content for selected file

**Files**: `Step4Results.tsx`
**Verify**: Can click file in tree, both source and result displayed with highlighting
**Estimate**: 2 hours

### 04-04: Download Options & Polish
**Scope**: Final features and UI polish
**Tasks**:
1. Add download buttons (individual file, all as ZIP)
2. Display success metrics (files transpiled, bytes, time)
3. Error summary with links to problematic files in tree

**Files**: `Step4Results.tsx`, `DownloadOptions.tsx`
**Verify**: Can download files, metrics displayed, errors clickable
**Estimate**: 1-2 hours

### 04-05: Complete E2E Test Suite
**Scope**: Full wizard flow end-to-end tests
**Tasks**:
1. Create `wizard-complete-flow.spec.ts` testing all 4 steps
2. Test with small project (3 files) and larger project (50+ files)
3. Test error scenarios (invalid directory, transpilation errors)

**Files**: `wizard-complete-flow.spec.ts`
**Verify**: Full flow tested, all scenarios covered
**Estimate**: 2 hours

**Phase 4 Complete When**: Complete wizard functional, all tests pass, ready to ship

---

## Post-Launch (Future Phases - Out of Current Scope)

**Phase 5: Enhanced Features** (v1.1)
- Diff view between source and transpiled (side-by-side or inline)
- Dark mode support
- Advanced tree features (rename, delete files in results)
- Export configuration (remember settings)

**Phase 6: Performance & Polish** (v1.2)
- Web Worker for syntax highlighting (if needed)
- Progressive loading for very large projects (>5000 files)
- Advanced filtering (by file type, errors only, etc.)
- Keyboard shortcuts for power users

---

## Status Tracking

| Phase | Plan | Status | Completed |
|-------|------|--------|-----------|
| 1 | 01-01 | ⬜ Not Started | - |
| 1 | 01-02 | ⬜ Not Started | - |
| 1 | 01-03 | ⬜ Not Started | - |
| 2 | 02-01 | ⬜ Not Started | - |
| 2 | 02-02 | ⬜ Not Started | - |
| 2 | 02-03 | ⬜ Not Started | - |
| 2 | 02-04 | ⬜ Not Started | - |
| 3 | 03-01 | ⬜ Not Started | - |
| 3 | 03-02 | ⬜ Not Started | - |
| 3 | 03-03 | ⬜ Not Started | - |
| 3 | 03-04 | ⬜ Not Started | - |
| 3 | 03-05 | ⬜ Not Started | - |
| 3 | 03-06 | ⬜ Not Started | - |
| 4 | 04-01 | ⬜ Not Started | - |
| 4 | 04-02 | ⬜ Not Started | - |
| 4 | 04-03 | ⬜ Not Started | - |
| 4 | 04-04 | ⬜ Not Started | - |
| 4 | 04-05 | ⬜ Not Started | - |

**Legend**: ⬜ Not Started | 🔄 In Progress | ✅ Complete | ⚠️ Blocked

---

## Risk Management

| Risk | Phase | Mitigation Status |
|------|-------|-------------------|
| Tree view performance | 2 | ✅ Planned: react-window virtualization in 02-02 |
| Syntax highlighting blocks UI | 4 | ✅ Planned: Async loading in 04-02 |
| File System API permissions | 3 | ✅ Planned: Permission checking in 03-01 |
| State management complexity | 1 | ✅ Planned: Simple hooks in 01-02 |

---

**Created**: 2025-12-22
**Last Updated**: 2025-12-22
**Next Action**: Plan Phase 1, Plan 01-01 (Wizard Stepper Component)
