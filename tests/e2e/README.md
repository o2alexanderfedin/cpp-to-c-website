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
│   └── components/            # Component page objects
│       ├── DirectorySelectorComponent.ts
│       ├── ProgressIndicatorComponent.ts
│       └── ErrorDisplayComponent.ts
├── specs/                     # Test specifications
│   ├── smoke.spec.ts         # Smoke tests
│   ├── navigation.spec.ts    # Navigation tests
│   ├── accessibility.spec.ts # Accessibility tests
│   ├── api.spec.ts          # API endpoint tests
│   └── playground.spec.ts   # Playground workflow tests
├── fixtures/                  # Test data and fixtures
│   └── cpp-projects/         # Synthetic C++ test projects
│       └── small-project/    # Small test project (3 files)
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
