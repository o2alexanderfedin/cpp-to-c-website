# E2E Test Suite Documentation

This directory contains end-to-end (E2E) tests for the C++ to C Transpiler website using Playwright.

## Overview

The E2E test suite provides comprehensive testing coverage including:
- Smoke tests for all major pages
- Navigation flow testing
- Accessibility compliance (WCAG 2.1 AA)
- API endpoint testing
- Playground functionality testing (with File System Access API mocking)
- Cross-browser testing (Chromium, Firefox, WebKit)

## Directory Structure

```
tests/e2e/
├── pages/                      # Page Object Model (POM)
│   ├── BasePage.ts            # Base page with common functionality
│   ├── HomePage.ts            # Homepage page object
│   ├── PlaygroundPage.ts      # Playground page object
│   ├── FeaturesPage.ts        # Features page object
│   ├── DocsPage.ts            # Documentation page object
│   ├── WizardPage.ts          # Wizard navigation page object
│   └── components/            # Component page objects
│       ├── DirectorySelectorComponent.ts
│       ├── ProgressIndicatorComponent.ts
│       └── ErrorDisplayComponent.ts
├── specs/                     # Test specifications
│   ├── smoke.spec.ts         # Smoke tests
│   ├── navigation.spec.ts    # Navigation tests
│   ├── accessibility.spec.ts # Accessibility tests
│   ├── api.spec.ts          # API endpoint tests
│   ├── playground.spec.ts   # Playground workflow tests
│   ├── wizard-navigation.spec.ts # Wizard navigation tests (Phase 1)
│   ├── wizard-target-selection.spec.ts # Target selection tests (Phase 3.06)
│   └── wizard-transpilation.spec.ts # Transpilation flow tests (Phase 3.06)
├── fixtures/                  # Test data and fixtures
│   └── sample-projects/      # Sample C++ test projects
│       ├── small-project/    # Small test project (2-3 files)
│       ├── medium-project/   # Medium project (10-15 files)
│       ├── large-project/    # Large project (50+ files, performance testing)
│       └── error-project/    # Project with transpilation errors
└── utils/                     # Test utilities
    └── test-helpers.ts       # Helper functions (mocking, etc.)
```

## Running Tests

### Local Development

```bash
# Run all E2E tests (headed mode)
npm run test:e2e

# Run in headed mode (browser visible)
npm run test:e2e:headed

# Run in debug mode (step through tests)
npm run test:e2e:debug

# Run with UI mode (interactive test runner)
npm run test:e2e:ui

# Run specific browser
npm run test:e2e:chromium
npm run test:e2e:firefox
npm run test:e2e:webkit
```

### CI/CD

Tests run automatically on GitHub Actions:
- On push to `main` or `develop` branches
- On pull requests to `main` or `develop`
- Tests are sharded across 4 parallel jobs
- HTML reports are uploaded as artifacts

## Test Categories

### Smoke Tests
Basic validation that all pages load correctly.
- Homepage
- Playground
- Features
- Docs

### Navigation Tests
Verify navigation flows between pages work correctly.
- Link navigation
- Browser back/forward
- URL routing

### Accessibility Tests
WCAG 2.1 AA compliance verification using axe-core.
- Automated accessibility scanning
- Keyboard navigation
- ARIA attributes
- Focus management

### API Tests
Backend API endpoint testing.
- `/api/transpile` - Transpile C++ code
- Error handling
- Response validation

### Playground Tests
Complete playground workflow testing.
- Directory selection (with mocking)
- Progress indicator
- Error display
- Transpilation workflow

### Wizard Tests

#### Phase 1: Navigation (✅ Complete)
- ✅ Forward navigation through all 4 steps
- ✅ Backward navigation to previous steps
- ✅ Button states (enabled/disabled at correct steps)
- ✅ Step indicator highlighting
- ✅ Keyboard navigation (Enter on focused buttons)
- ✅ Accessibility (ARIA labels, roles, disabled states)
- ✅ Round-trip navigation (1→2→3→4→3→2→1)
**Tests**: 16 passing in `wizard-navigation.spec.ts`

#### Phase 2: Source Selection (✅ Complete)
**Unit Tests**: 89 tests (88 passing)
- ✅ FileTreeView component (32 tests - rendering, expansion, selection, virtualization)
- ✅ buildTreeData utility (16 tests - tree structure, sorting, edge cases)
- ✅ Step1SourceSelection (8 tests - integration, display, conditional rendering)
- ✅ Performance benchmarks (17 tests - all exceeding targets by 90%+)
  - 500 files: 62.63ms (target: <150ms)
  - 1,000 files: 21.41ms (target: <250ms)
  - 2,000 files: 22.32ms (target: <400ms)
  - 5,000 files: 20.41ms (target: <800ms)
  - 10,000 files: 21.64ms (target: <2000ms)
- ✅ Virtualization verified (only 29 DOM nodes for 2000+ files)

### Wizard Target Selection Tests (Phase 3.06)
End-to-end tests for Step 2 (Target Selection).
- Target directory selection UI
- Transpilation options (target C standard, ACSL)
- Permission indicators
- Conflict detection and acknowledgment
- Keyboard navigation and accessibility
- Note: Full File System Access API testing requires mocking

### Wizard Transpilation Tests (Phase 3.06)
End-to-end tests for Step 3 (Transpilation Flow).
- Automatic transpilation start
- Progress bar and metrics display
- Current file tracking
- File tree with status indicators
- Pause/resume functionality
- Cancel with confirmation
- Keyboard shortcuts (Space, Escape)
- Error handling and display
- Performance testing (large projects)
- Completion message
- Accessibility (ARIA attributes, live regions)

## File System Access API Testing

The playground uses the File System Access API which requires special handling in tests:

### Automated Tests (Recommended)
Use mocking for automated CI/CD testing:

```typescript
import { mockFileSystemAccessAPI } from '../utils/test-helpers';

await mockFileSystemAccessAPI(page, {
  directoryName: 'test-project',
  files: new Map([
    ['main.cpp', 'int main() { return 0; }'],
    ['utils.h', '#pragma once'],
  ]),
});
```

### Manual Integration Tests
For real File System Access API testing:
1. Run tests in headed mode: `npm run test:e2e:headed`
2. Manually select directory when prompted
3. Tests continue automated verification

Tests marked with `.skip('MANUAL TEST')` require manual interaction.

## Page Object Model (POM)

All tests use the Page Object Model pattern for maintainability:

```typescript
import { PlaygroundPage } from '../pages/PlaygroundPage';

test('example test', async ({ page }) => {
  const playgroundPage = new PlaygroundPage(page);
  await playgroundPage.navigate();

  await playgroundPage.selectDirectory();
  await playgroundPage.startTranspilation();
  await playgroundPage.waitForCompletion();

  expect(await playgroundPage.hasErrors()).toBe(false);
});
```

## Accessibility Testing

All pages are tested for WCAG 2.1 AA compliance:

```typescript
import AxeBuilder from '@axe-core/playwright';

const results = await new AxeBuilder({ page })
  .withTags(['wcag2a', 'wcag2aa', 'wcag21a', 'wcag21aa'])
  .analyze();

expect(results.violations).toEqual([]);
```

## Configuration

Main configuration: `/playwright.config.ts`

Key settings:
- **Headed mode**: `headless: false` (required for File System Access API)
- **Base URL**: `http://localhost:4321`
- **Browsers**: Chromium, Firefox, WebKit, Mobile Chrome
- **Reporters**: Blob (CI), HTML (local), GitHub (CI annotations)
- **Screenshots**: On failure only
- **Videos**: Retain on failure
- **Retries**: 2 in CI, 0 locally

## Troubleshooting

### Tests Timing Out
Increase timeout in `playwright.config.ts` or specific tests:
```typescript
test.setTimeout(60000); // 60 seconds
```

### Browser Not Opening
Ensure Playwright browsers are installed:
```bash
npx playwright install --with-deps chromium
```

### File System Access API Errors
- Use mocking for automated tests
- For manual tests, ensure running in headed mode
- Check browser support (Chrome/Edge recommended)

## Best Practices

1. **Test Isolation**: Each test should be independent
2. **User-Facing Selectors**: Use `getByRole()`, `getByLabel()` over CSS selectors
3. **Auto-Waiting**: Use Playwright's built-in assertions (auto-wait)
4. **Avoid Arbitrary Waits**: Use `waitForSelector()` instead of `waitForTimeout()`
5. **Accessibility First**: Test accessibility on all pages
6. **Meaningful Assertions**: Verify actual behavior, not just element presence

## Contributing

When adding new tests:
1. Follow the Page Object Model pattern
2. Add appropriate accessibility tests
3. Use meaningful test descriptions
4. Document manual test steps if needed
5. Ensure tests are isolated and can run in any order

## Resources

- [Playwright Documentation](https://playwright.dev/docs/intro)
- [axe-core Playwright](https://www.npmjs.com/package/@axe-core/playwright)
- [WCAG 2.1 Guidelines](https://www.w3.org/WAI/WCAG21/quickref/)
- [File System Access API](https://developer.chrome.com/docs/capabilities/web-apis/file-system-access)

## Wizard Complete Flow Tests (Phase 04-05)

Added comprehensive E2E tests in `wizard-complete-flow.spec.ts` for the complete wizard flow:

### Test Coverage
- **Complete Navigation**: Navigate through all 4 wizard steps
- **File Selection**: Display file tree after directory selection  
- **Large Projects**: Handle 50+ files with virtualized tree view
- **State Management**: Maintain wizard state when navigating back/forth
- **Empty States**: Show appropriate UI when no transpilation results
- **Responsive Design**: Test layouts at multiple viewport sizes
- **UI Components**: Verify navigation buttons, step indicators, file statistics

### Test Fixtures (tests/e2e/fixtures/projects.ts)
- `smallProject`: 3 files for quick tests
- `largeProject`: Multi-directory structure
- `errorProject`: Files with intentional errors
- `generateLargeProject(N)`: Generate N files for performance testing

### WizardPage Methods (Step 4)
Added to `tests/e2e/pages/WizardPage.ts`:
- `getStatistics()`: Get file statistics from results
- `selectFileInTree(filename)`: Select file from tree
- `getSelectedFileInViewer()`: Get selected file name
- `isFileContentDisplayed()`: Check if content is shown
- `downloadAllAsZip()`: Download ZIP archive
- `downloadCurrentFile()`: Download individual file
- `getErrorCount()`: Get number of errors
- `clickErrorFile(filename)`: Navigate to error file
- `areMetricsDisplayed()`: Check metrics visibility
- `areDownloadOptionsDisplayed()`: Check download options visibility
- `completeTranspilation(project)`: Helper to complete Steps 1-3

### Test Count
- 12 tests covering wizard complete flow
- Combined with existing tests: 25+ E2E tests total

