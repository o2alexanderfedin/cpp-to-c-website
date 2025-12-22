# Test Fixtures: Sample C++ Projects

This directory contains sample C++ projects used for E2E testing of the transpilation workflow.

## Directory Structure

```
sample-projects/
├── README.md (this file)
├── small-project/           # 2-3 simple C++ files
│   ├── main.cpp
│   ├── utils.h
│   └── utils.cpp
├── medium-project/          # 10-15 C++ files in various directories
│   ├── src/
│   │   ├── main.cpp
│   │   ├── calculator/
│   │   │   ├── calculator.h
│   │   │   └── calculator.cpp
│   │   └── utils/
│   │       ├── string_utils.h
│   │       └── string_utils.cpp
│   └── include/
│       └── config.h
├── large-project/           # 50+ C++ files for performance testing
│   ├── src/
│   ├── include/
│   └── lib/
└── error-project/           # Files with intentional transpilation errors
    ├── syntax_error.cpp
    ├── unsupported_feature.cpp
    └── missing_include.cpp
```

## Project Details

### small-project
**Purpose**: Basic transpilation tests
**Files**: 2-3 simple C++ files
**Use cases**:
- Basic transpilation flow
- Simple progress tracking
- File tree rendering

**Files**:
- `main.cpp` - Simple main function with basic I/O
- `utils.h` - Header with function declarations
- `utils.cpp` - Implementation of utility functions

### medium-project
**Purpose**: Multi-directory projects
**Files**: 10-15 C++ files in nested directories
**Use cases**:
- Directory structure handling
- Multiple file types (.cpp, .cc, .h, .hpp)
- Hierarchical file tree display

**Structure**:
- `src/main.cpp` - Entry point
- `src/calculator/` - Calculator module (2 files)
- `src/utils/` - Utility functions (2 files)
- `include/config.h` - Configuration header

### large-project
**Purpose**: Performance testing
**Files**: 50+ C++ files
**Use cases**:
- UI responsiveness with large file counts
- Progress update performance
- File tree virtualization
- Memory efficiency

**Structure**:
- Multiple modules with 10+ files each
- Deep directory nesting (4+ levels)
- Mix of small and large files

### error-project
**Purpose**: Error handling tests
**Files**: 3-5 files with intentional errors
**Use cases**:
- Transpilation error detection
- Error message display
- Partial success scenarios
- Error recovery

**Files**:
- `syntax_error.cpp` - Invalid C++ syntax
- `unsupported_feature.cpp` - C++ features not supported in C
- `missing_include.cpp` - Missing header files

## Creating Test Projects

### Automated Setup
Run the setup script to generate all test projects:

```bash
npm run test:fixtures:setup
```

### Manual Setup
For custom test projects:

1. Create project directory under `sample-projects/`
2. Add C++ source files (.cpp, .cc, .cxx)
3. Add header files (.h, .hpp)
4. Document the project structure in this README

## Using Fixtures in Tests

### Example: Small Project Test

```typescript
import { test, expect } from '@playwright/test';
import { WizardPage } from '../pages/WizardPage';
import path from 'path';

test('transpile small project', async ({ page }) => {
  const wizardPage = new WizardPage(page);
  await wizardPage.goto();

  // Mock directory selection with fixture path
  const fixturePath = path.join(__dirname, '../fixtures/sample-projects/small-project');
  // ... test implementation
});
```

### File System Access API Mocking

Since File System Access API cannot be fully automated in Playwright, tests can use:

1. **localStorage mocking**: Pre-populate selected directory handles
2. **Test-specific API**: Mock implementation for testing
3. **CDP (Chrome DevTools Protocol)**: Advanced automation

Example test setup with mocking:

```typescript
test.beforeEach(async ({ page }) => {
  // Inject mock File System Access API
  await page.addInitScript(() => {
    window.mockFileSystemAPI = {
      selectedSourceDir: '/fixtures/sample-projects/small-project',
      selectedTargetDir: '/tmp/test-output'
    };
  });
});
```

## Maintenance

### Adding New Fixtures

1. Create new project directory
2. Add representative C++ files
3. Update this README with project details
4. Add corresponding E2E tests

### Updating Existing Fixtures

- Keep files simple and focused on specific test scenarios
- Avoid external dependencies
- Use standard C++ features (C++11/14)
- Document any special characteristics

## Notes

- Fixtures should be self-contained (no external dependencies)
- Keep file sizes reasonable (< 1MB per file)
- Use realistic but simple C++ code
- Include comments explaining test-specific aspects
- Follow consistent coding style across fixtures

## Related Documentation

- [E2E Tests README](../README.md)
- [Wizard Test Specs](../specs/)
- [Testing Guide](../../../../docs/testing.md)
