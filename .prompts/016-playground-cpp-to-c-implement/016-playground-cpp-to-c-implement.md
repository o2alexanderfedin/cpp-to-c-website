# C++ to C Playground Web Interface - Implementation

<objective>
Implement C++ to C transpilation playground using Test-Driven Development, following the architecture plan.

Purpose: Create production-ready web interface for whole-project C++ to C transpilation
Output: Complete implementation with 100% test coverage
Approach: TDD - write test first, implement to pass, refactor
</objective>

<context>
Architecture plan: @.prompts/015-playground-cpp-to-c-plan/playground-cpp-to-c-plan.md
Research findings: @.prompts/014-playground-cpp-to-c-research/playground-cpp-to-c-research.md

Existing implementations:
- @wasm/glue/src/index.ts
- @wasm/glue/src/types.ts
- @wasm/glue/src/headers/stdlib-provider.ts

Website structure:
- @src/pages/ (Astro)
- @src/components/ (React/Astro)

Test infrastructure:
- @wasm/glue/vitest.config.ts (reference configuration)
</context>

<tdd_requirements>
**CRITICAL: Follow TDD cycle for EVERY feature**:

1. **Red**: Write failing test first
2. **Green**: Write minimum code to pass test
3. **Refactor**: Improve code while keeping tests green

**No code without tests**:
- Write interface tests before implementations
- Write service tests before service code
- Write component tests before component code
- Target: 100% line coverage

**Test organization**:
```
src/
├── core/
│   ├── interfaces/
│   │   ├── IFileSystem.ts
│   │   └── IFileSystem.test.ts          # Interface contract tests
├── adapters/
│   ├── MockFileSystem.ts
│   └── MockFileSystem.test.ts           # Mock implementation tests
├── features/
│   ├── transpile/
│   │   ├── TranspileService.ts
│   │   └── TranspileService.test.ts     # Business logic tests
```

**Testing frameworks**:
- Vitest for unit/integration tests
- React Testing Library for components
- Playwright for E2E tests (if feasible)
</tdd_requirements>

<implementation_phases>
Execute phases sequentially from the plan:

**Phase 1: Foundation** (START HERE)
- Define core interfaces (IFileSystem, ITranspiler, IProgressReporter)
- Create MockFileSystem implementation
- Set up test infrastructure
- Deliverable: Testable foundation with 100% coverage

**Phase 2: WASM Integration**
- Create WasmTranspilerAdapter implementing ITranspiler
- Integrate HeaderProvider from @wasm/glue
- Test with mock WASM module
- Deliverable: Working transpiler adapter with tests

**Phase 3: File System Adapter**
- Implement FileSystemAccessAdapter
- Handle directory traversal and permissions
- Test with temporary directories
- Deliverable: File system integration with E2E tests

**Phase 4: Transpile Service**
- Implement TranspileService orchestration
- Add progress reporting and cancellation
- Test with MockFileSystem
- Deliverable: Core business logic with 100% coverage

**Phase 5: UI Components**
- Create DirectorySelector, ProgressIndicator, ErrorDisplay
- Test with React Testing Library
- Integrate with services
- Deliverable: Interactive UI components

**Phase 6: Integration**
- Create PlaygroundPage wiring all features
- End-to-end tests with synthetic projects
- Performance testing
- Deliverable: Complete working playground
</implementation_phases>

<requirements>
**Functional Requirements**:
1. Select source directory (C++ files)
2. Select target directory (C output)
3. Transpile entire project with one click
4. Show real-time progress (file count, percentage)
5. Display errors clearly (per-file, summary)
6. Preserve directory structure in output
7. Support cancellation of long operations
8. Generate compilable C99 code

**Quality Requirements**:
- 100% test coverage (unit tests)
- All services tested in isolation
- All adapters tested with real and mock dependencies
- E2E tests for critical user flows
- Type-safe throughout (TypeScript strict mode)
- SOLID principles (per architecture plan)
- Performance: <5s for 100 files

**Technical Requirements**:
- Use File System Access API (Chrome/Edge)
- Integrate existing WASM transpiler
- Support drag-drop and button selection
- Handle 500+ file projects
- Report progress every 100ms minimum
- Handle errors gracefully (continue processing)
</requirements>

<implementation_guidance>
**Vertical Slice Organization**:
```
src/
├── core/
│   ├── interfaces/
│   │   ├── IFileSystem.ts
│   │   ├── ITranspiler.ts
│   │   ├── IProgressReporter.ts
│   │   └── types.ts
├── adapters/
│   ├── MockFileSystem.ts
│   ├── MockFileSystem.test.ts
│   ├── FileSystemAccessAdapter.ts
│   ├── FileSystemAccessAdapter.test.ts
│   ├── WasmTranspilerAdapter.ts
│   └── WasmTranspilerAdapter.test.ts
├── features/
│   ├── transpile/
│   │   ├── TranspileService.ts
│   │   ├── TranspileService.test.ts
│   │   └── types.ts
│   ├── file-selection/
│   │   ├── FileSelectionService.ts
│   │   └── FileSelectionService.test.ts
│   └── progress/
│       ├── ProgressService.ts
│       └── ProgressService.test.ts
├── components/
│   ├── DirectorySelector.tsx
│   ├── DirectorySelector.test.tsx
│   ├── ProgressIndicator.tsx
│   ├── ProgressIndicator.test.tsx
│   ├── ErrorDisplay.tsx
│   └── ErrorDisplay.test.tsx
└── pages/
    └── playground.astro
```

**Dependency Injection Pattern**:
```typescript
// Interface
interface IFileSystem {
  readFile(path: string): Promise<string>;
  writeFile(path: string, content: string): Promise<void>;
  readDir(path: string): Promise<string[]>;
  exists(path: string): Promise<boolean>;
}

// Service with DI
class TranspileService {
  constructor(
    private fs: IFileSystem,
    private transpiler: ITranspiler,
    private progress: IProgressReporter
  ) {}

  async transpileProject(sourcePath: string, targetPath: string): Promise<void> {
    // Implementation
  }
}

// Test with mock
describe('TranspileService', () => {
  let service: TranspileService;
  let mockFs: MockFileSystem;
  let mockTranspiler: MockTranspiler;
  let mockProgress: MockProgressReporter;

  beforeEach(() => {
    mockFs = new MockFileSystem();
    mockTranspiler = new MockTranspiler();
    mockProgress = new MockProgressReporter();
    service = new TranspileService(mockFs, mockTranspiler, mockProgress);
  });

  it('should transpile all files in directory', async () => {
    // Arrange
    mockFs.addFile('/source/main.cpp', 'int main() {}');
    mockFs.addFile('/source/utils.cpp', 'void util() {}');

    // Act
    await service.transpileProject('/source', '/target');

    // Assert
    expect(mockFs.fileExists('/target/main.c')).toBe(true);
    expect(mockFs.fileExists('/target/utils.c')).toBe(true);
  });
});
```

**TDD Example Workflow** (Phase 1, Task 1: IFileSystem):

```typescript
// Step 1: Write test FIRST (Red)
// IFileSystem.test.ts
describe('IFileSystem contract', () => {
  it('should define readFile method', () => {
    const fs: IFileSystem = new MockFileSystem();
    expect(typeof fs.readFile).toBe('function');
  });

  it('should read file content', async () => {
    const fs = new MockFileSystem();
    await fs.writeFile('/test.txt', 'content');
    const result = await fs.readFile('/test.txt');
    expect(result).toBe('content');
  });
});

// Step 2: Define interface to pass test (Green)
// IFileSystem.ts
interface IFileSystem {
  readFile(path: string): Promise<string>;
  writeFile(path: string, content: string): Promise<void>;
  readDir(path: string): Promise<string[]>;
  exists(path: string): Promise<boolean>;
}

// Step 3: Implement MockFileSystem (Green)
// MockFileSystem.ts
class MockFileSystem implements IFileSystem {
  private files = new Map<string, string>();

  async readFile(path: string): Promise<string> {
    const content = this.files.get(path);
    if (!content) throw new Error(`File not found: ${path}`);
    return content;
  }

  async writeFile(path: string, content: string): Promise<void> {
    this.files.set(path, content);
  }

  // ... implement other methods
}

// Step 4: Run tests - they should pass
// Step 5: Refactor if needed (while keeping tests green)
```

**SOLID Principles Application**:
- **S**: Each service has one responsibility (TranspileService only orchestrates)
- **O**: New adapters extend via interfaces without modifying services
- **L**: All IFileSystem implementations are substitutable
- **I**: Interfaces are minimal (no bloated contracts)
- **D**: Services depend on interfaces, not implementations

**Avoid Anti-Patterns**:
- No concrete class dependencies (use interfaces)
- No static methods (hard to test)
- No global state (use dependency injection)
- No tight coupling (use adapters)
- No God objects (split responsibilities)
</implementation_guidance>

<phase_1_detailed_instructions>
**Phase 1: Foundation (Execute First)**

1. Create interface definitions (TDD):

```typescript
// Test first: core/interfaces/IFileSystem.test.ts
describe('IFileSystem', () => {
  describe('contract', () => {
    it('should have readFile method');
    it('should have writeFile method');
    it('should have readDir method');
    it('should have exists method');
  });

  describe('behavior', () => {
    let fs: IFileSystem;

    beforeEach(() => {
      fs = new MockFileSystem(); // Will create this next
    });

    it('should read file content', async () => {
      await fs.writeFile('/test.txt', 'hello');
      expect(await fs.readFile('/test.txt')).toBe('hello');
    });

    it('should throw if file not found', async () => {
      await expect(fs.readFile('/missing.txt')).rejects.toThrow();
    });

    it('should list directory contents', async () => {
      await fs.writeFile('/dir/file1.txt', '');
      await fs.writeFile('/dir/file2.txt', '');
      const files = await fs.readDir('/dir');
      expect(files).toContain('file1.txt');
      expect(files).toContain('file2.txt');
    });

    it('should check file existence', async () => {
      await fs.writeFile('/exists.txt', '');
      expect(await fs.exists('/exists.txt')).toBe(true);
      expect(await fs.exists('/missing.txt')).toBe(false);
    });
  });
});

// Then implement: core/interfaces/IFileSystem.ts
export interface IFileSystem {
  readFile(path: string): Promise<string>;
  writeFile(path: string, content: string): Promise<void>;
  readDir(path: string): Promise<string[]>;
  exists(path: string): Promise<boolean>;
}

// Then implement: adapters/MockFileSystem.ts (to pass tests)
export class MockFileSystem implements IFileSystem {
  private files = new Map<string, string>();

  async readFile(path: string): Promise<string> {
    if (!this.files.has(path)) {
      throw new Error(`File not found: ${path}`);
    }
    return this.files.get(path)!;
  }

  async writeFile(path: string, content: string): Promise<void> {
    this.files.set(path, content);
  }

  async readDir(path: string): Promise<string[]> {
    const dirPrefix = path.endsWith('/') ? path : `${path}/`;
    const files: string[] = [];
    for (const filePath of this.files.keys()) {
      if (filePath.startsWith(dirPrefix)) {
        const relativePath = filePath.substring(dirPrefix.length);
        if (!relativePath.includes('/')) {
          files.push(relativePath);
        }
      }
    }
    return files;
  }

  async exists(path: string): Promise<boolean> {
    return this.files.has(path);
  }

  // Test helper methods
  addFile(path: string, content: string): void {
    this.files.set(path, content);
  }

  clear(): void {
    this.files.clear();
  }
}
```

2. Create ITranspiler interface (same TDD pattern)
3. Create IProgressReporter interface (same TDD pattern)
4. Set up test infrastructure (vitest.config.ts)

**Deliverable for Phase 1**:
- All interfaces defined with tests
- MockFileSystem with 100% coverage
- Test infrastructure working
- All tests passing
</phase_1_detailed_instructions>

<verification>
Before declaring each phase complete:

**Phase 1**:
- [ ] All interfaces defined in core/interfaces/
- [ ] MockFileSystem passes all contract tests
- [ ] Test infrastructure configured (vitest.config.ts)
- [ ] `npm test` runs successfully
- [ ] 100% test coverage for foundation

**Phase 2**:
- [ ] WasmTranspilerAdapter implements ITranspiler
- [ ] Integration with @wasm/glue verified
- [ ] Unit tests with mocked WASM module passing
- [ ] Error handling tested
- [ ] 100% coverage for adapter

**Phase 3**:
- [ ] FileSystemAccessAdapter implements IFileSystem
- [ ] Directory traversal working
- [ ] Permissions handling tested
- [ ] Integration tests passing (or mocked if API unavailable)
- [ ] 100% coverage for adapter

**Phase 4**:
- [ ] TranspileService orchestrates file processing
- [ ] Progress reporting working
- [ ] Cancellation support working
- [ ] Error handling (continue on error) working
- [ ] Directory structure preserved
- [ ] 100% test coverage with mock dependencies

**Phase 5**:
- [ ] DirectorySelector component renders
- [ ] ProgressIndicator shows accurate progress
- [ ] ErrorDisplay shows error details
- [ ] All components have tests
- [ ] Accessibility tests passing

**Phase 6**:
- [ ] PlaygroundPage integrates all features
- [ ] E2E test with 10 file project passes
- [ ] E2E test with 100 file project passes
- [ ] Performance meets target (<5s for 100 files)
- [ ] Cross-browser testing (Chrome/Edge)

**Overall Quality**:
- [ ] TypeScript strict mode with no errors
- [ ] ESLint passing with no warnings
- [ ] 100% test coverage (unit tests)
- [ ] All critical paths covered (integration tests)
- [ ] E2E tests pass for core user flows
</verification>

<success_criteria>
- All 6 phases implemented following TDD
- 100% test coverage for services and adapters
- All tests passing (unit, integration, E2E)
- TypeScript strict mode with zero errors
- SOLID principles followed throughout
- Vertical slice organization implemented
- Dependency injection used consistently
- Performance target met (<5s for 100 files)
- Browser compatibility verified (Chrome/Edge)
- Production-ready code quality
- SUMMARY.md created for each phase completed
</success_criteria>

<output>
Create files in website repository:

**Core Interfaces** (Phase 1):
- `src/core/interfaces/IFileSystem.ts`
- `src/core/interfaces/IFileSystem.test.ts`
- `src/core/interfaces/ITranspiler.ts`
- `src/core/interfaces/ITranspiler.test.ts`
- `src/core/interfaces/IProgressReporter.ts`
- `src/core/interfaces/types.ts`

**Adapters** (Phases 1-3):
- `src/adapters/MockFileSystem.ts`
- `src/adapters/MockFileSystem.test.ts`
- `src/adapters/WasmTranspilerAdapter.ts`
- `src/adapters/WasmTranspilerAdapter.test.ts`
- `src/adapters/FileSystemAccessAdapter.ts`
- `src/adapters/FileSystemAccessAdapter.test.ts`

**Services** (Phase 4):
- `src/features/transpile/TranspileService.ts`
- `src/features/transpile/TranspileService.test.ts`
- `src/features/transpile/types.ts`

**Components** (Phase 5):
- `src/components/DirectorySelector.tsx`
- `src/components/DirectorySelector.test.tsx`
- `src/components/ProgressIndicator.tsx`
- `src/components/ProgressIndicator.test.tsx`
- `src/components/ErrorDisplay.tsx`
- `src/components/ErrorDisplay.test.tsx`

**Page** (Phase 6):
- `src/pages/playground.astro`

**Tests** (Phase 6):
- `tests/e2e/playground.spec.ts` (if Playwright feasible)
- `tests/performance/transpile-benchmark.test.ts`

**Configuration**:
- `vitest.config.ts` (extend from wasm/glue configuration)
</output>

<summary_requirements>
Create `.prompts/016-playground-cpp-to-c-implement/SUMMARY.md` after EACH phase:

```markdown
# C++ to C Playground Implementation - Phase {N} Summary

**{Substantive one-liner: what was built}**

## Version
v1 - Phase {N}/{6}

## Files Created
- `path/to/file.ts` - Description
- `path/to/file.test.ts` - Test coverage

## Test Coverage
- Unit tests: {N} passing
- Coverage: {percentage}%

## Decisions Needed
{Any implementation choices needing validation, or "None"}

## Blockers
{Issues preventing progress, or "None"}

## Next Step
{Next phase or specific action}

---
*Confidence: {High|Medium|Low}*
*Tests: {N passing/total}*
```

Create final SUMMARY.md after Phase 6 with overall results.
</summary_requirements>
