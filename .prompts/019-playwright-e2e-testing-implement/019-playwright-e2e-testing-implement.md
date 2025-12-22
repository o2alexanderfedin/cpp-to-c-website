# Playwright E2E Testing Implementation - Meta-Prompt

<objective>
Implement comprehensive E2E testing for the C++ to C transpiler website using Playwright in HEADED mode.

Purpose: Create production-ready E2E test suite with 100% critical path coverage
Output: Complete Playwright test implementation with all tests passing
Approach: TDD where possible, following the test plan from Phase 018
Dependencies: Requires completion of 018-playwright-e2e-testing-plan
</objective>

<context>
Test plan: @.prompts/018-playwright-e2e-testing-plan/playwright-e2e-testing-plan.md
Research: @.prompts/017-playwright-e2e-testing-research/playwright-e2e-testing-research.md
Website project: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/website
Current state: No E2E tests, 314 unit tests (93.6% passing)
Execution mode: HEADED browser (headless: false)
</context>

<implementation_requirements>
**CRITICAL: Execute all 5 phases sequentially following the plan**

## Phase 1: Foundation Setup (EXECUTE FIRST)
**Duration**: 2-3 hours
**Priority**: Critical (P0)

### Tasks:
1. **Install Playwright**
   ```bash
   npm install -D @playwright/test
   npx playwright install --with-deps chromium firefox webkit
   ```

2. **Create Configuration**
   - `playwright.config.ts` - Main configuration
   - `playwright.headed.config.ts` - Headed mode overrides (optional)
   - Configure for HEADED mode (headless: false)
   - Set base URL to http://localhost:4321
   - Configure screenshot/video on failure
   - Set up parallel execution
   - Configure retries and timeouts

3. **Create Directory Structure**
   ```
   tests/
   ├── e2e/
   │   ├── fixtures/
   │   │   └── cpp-projects/
   │   ├── pages/
   │   │   └── BasePage.ts
   │   ├── specs/
   │   │   └── smoke.spec.ts
   │   └── utils/
   │       └── test-helpers.ts
   ```

4. **Create Base Page Object**
   - `tests/e2e/pages/BasePage.ts`
   - Common methods (navigate, waitForLoad, etc.)
   - Accessibility check helper
   - Screenshot helper

5. **Create First Smoke Test**
   - `tests/e2e/specs/smoke.spec.ts`
   - Verify homepage loads
   - Verify basic navigation works
   - Run in headed mode

6. **Add NPM Scripts**
   ```json
   "test:e2e": "playwright test",
   "test:e2e:headed": "playwright test --headed",
   "test:e2e:debug": "playwright test --debug",
   "test:e2e:ui": "playwright test --ui"
   ```

### Deliverables:
- ✅ Playwright installed and configured
- ✅ Directory structure created
- ✅ Base page object implemented
- ✅ First smoke test passing
- ✅ Headed mode confirmed working

### Verification:
```bash
npm run test:e2e:headed
```
Should open browser and pass smoke test.

---

## Phase 2: Playground Tests (EXECUTE SECOND)
**Duration**: 4-6 hours
**Priority**: Critical (P0)

### Tasks:

1. **Create Synthetic Test Projects**
   - `tests/e2e/fixtures/cpp-projects/small-project/`
     - main.cpp (simple main function)
     - utils.h, utils.cpp
     - math.h, math.cpp
   - Create expected C output files for validation
   - Document project structure in README.md

2. **Create Component Page Objects**
   - `tests/e2e/pages/components/DirectorySelectorComponent.ts`
     - Methods: clickSelectButton(), getSelectedPath(), isDragEnabled()
   - `tests/e2e/pages/components/ProgressIndicatorComponent.ts`
     - Methods: getPercentage(), getFileCount(), getCurrentFile(), isVisible()
   - `tests/e2e/pages/components/ErrorDisplayComponent.ts`
     - Methods: getErrors(), hasErrors(), getErrorCount()

3. **Create PlaygroundPage**
   - `tests/e2e/pages/PlaygroundPage.ts`
   - Compose component objects
   - High-level workflow methods:
     - selectDirectory(path: string)
     - startTranspilation()
     - waitForCompletion(timeout?)
     - verifyDownload()
     - cancelTranspilation()

4. **Implement File System Access Automation**
   - Research CDP approach for automating showDirectoryPicker()
   - OR create pre-authorized test directory approach
   - Document the approach chosen

5. **Create Playground Test Suite**
   - `tests/e2e/specs/playground.spec.ts`
   - Test 1: Complete transpilation workflow (happy path)
   - Test 2: Directory selection validation
   - Test 3: Progress indicator accuracy
   - Test 4: Error display for invalid C++
   - Test 5: Cancellation workflow
   - Test 6: Large project (100 files)

6. **Create API Test Suite**
   - `tests/e2e/specs/api.spec.ts`
   - Test /api/transpile endpoint
   - Test /api/validate endpoint
   - Test error handling (400, 500, timeout)
   - Test various C++ inputs

### Deliverables:
- ✅ Synthetic C++ test projects created
- ✅ Component page objects implemented
- ✅ PlaygroundPage implemented
- ✅ File System Access automation working
- ✅ 6 playground tests passing
- ✅ API tests passing

### Verification:
```bash
npm run test:e2e:headed -- playground.spec.ts
```
All playground tests should pass in headed mode.

---

## Phase 3: Navigation & Content Tests (EXECUTE THIRD)
**Duration**: 3-4 hours
**Priority**: High (P1)

### Tasks:

1. **Create Page Objects**
   - `tests/e2e/pages/HomePage.ts`
   - `tests/e2e/pages/FeaturesPage.ts`
   - `tests/e2e/pages/DocsPage.ts`
   - `tests/e2e/pages/ArchitecturePage.ts`
   - Each with relevant selectors and methods

2. **Create Navigation Test Suite**
   - `tests/e2e/specs/navigation.spec.ts`
   - Test all main navigation links
   - Test tab navigation (Astro tabs)
   - Test breadcrumbs (if applicable)
   - Test 404 page

3. **Create Content Test Suite**
   - `tests/e2e/specs/content.spec.ts`
   - Verify key content present on each page
   - Test interactive elements (accordions, tabs, etc.)
   - Test code examples (if present)

4. **Create Mobile Responsive Tests**
   - `tests/e2e/specs/mobile.spec.ts`
   - Test mobile viewport (375x667)
   - Test tablet viewport (768x1024)
   - Verify responsive navigation (hamburger menu?)
   - Test touch interactions

### Deliverables:
- ✅ Page objects for all major pages
- ✅ Navigation tests passing
- ✅ Content tests passing
- ✅ Mobile responsive tests passing

### Verification:
```bash
npm run test:e2e:headed -- navigation.spec.ts content.spec.ts mobile.spec.ts
```

---

## Phase 4: Accessibility & Performance (EXECUTE FOURTH)
**Duration**: 2-3 hours
**Priority**: High (P1)

### Tasks:

1. **Install Accessibility Tools**
   ```bash
   npm install -D @axe-core/playwright
   ```

2. **Create Accessibility Test Suite**
   - `tests/e2e/specs/accessibility.spec.ts`
   - Automated scans on all pages (axe-core)
   - Keyboard navigation tests
   - Focus management tests
   - ARIA label verification
   - Color contrast checks (if possible)

3. **Create Accessibility Helpers**
   - `tests/e2e/utils/accessibility-helpers.ts`
   - runAccessibilityScan(page, options)
   - testKeyboardNavigation(page, route)
   - verifyFocusVisible(page)

4. **Create Performance Test Suite**
   - `tests/e2e/specs/performance.spec.ts`
   - Measure page load times
   - Track Core Web Vitals (if possible with Playwright)
   - Test API response times
   - Verify no performance regressions

5. **Optional: Lighthouse CI**
   - Install @lhci/cli
   - Create lighthouserc.json
   - Run Lighthouse audits
   - Set performance budgets

### Deliverables:
- ✅ Accessibility tests passing (0 critical violations)
- ✅ Keyboard navigation verified
- ✅ Performance benchmarks established
- ✅ Lighthouse integration (optional)

### Verification:
```bash
npm run test:e2e:headed -- accessibility.spec.ts performance.spec.ts
```

---

## Phase 5: CI/CD Integration (EXECUTE FIFTH)
**Duration**: 2-3 hours
**Priority**: Medium (P2)

### Tasks:

1. **Create GitHub Actions Workflow**
   - `.github/workflows/playwright.yml`
   - Install dependencies
   - Install Playwright browsers
   - Build Astro site
   - Start dev server
   - Run Playwright tests (headed with xvfb)
   - Upload artifacts on failure

2. **Configure xvfb for Headed Mode**
   ```yaml
   - name: Run Playwright tests
     run: xvfb-run --auto-servernum --server-args="-screen 0 1280x960x24" npm run test:e2e
   ```

3. **Set Up Artifact Upload**
   - Upload test-results/ on failure
   - Upload videos on failure
   - Upload traces on failure
   - Retention: 30 days

4. **Configure Test Reporting**
   - Use Playwright HTML reporter
   - Publish test results to GitHub Pages (optional)
   - Or use third-party service (Currents, Sorry Cypress, etc.)

5. **Add Status Badge**
   - Add Playwright test badge to README.md
   - Link to latest test results

### Deliverables:
- ✅ GitHub Actions workflow created
- ✅ Headed mode working in CI (with xvfb)
- ✅ Artifacts uploading on failure
- ✅ Test reporting configured
- ✅ Badge added to README

### Verification:
- Push to GitHub
- Verify workflow runs
- Verify tests pass in CI
- Verify artifacts uploaded on failure

---

</implementation_requirements>

<test_specifications>
Based on the test plan, implement these critical test specs:

### playground.spec.ts

```typescript
import { test, expect } from '@playwright/test';
import { PlaygroundPage } from '../pages/PlaygroundPage';

test.describe('Playground - Complete Workflow', () => {
  let playgroundPage: PlaygroundPage;

  test.beforeEach(async ({ page }) => {
    playgroundPage = new PlaygroundPage(page);
    await playgroundPage.navigate();
  });

  test('should transpile small C++ project successfully', async ({ page }) => {
    // 1. Select directory
    await playgroundPage.selectDirectory('./tests/e2e/fixtures/cpp-projects/small-project');

    // 2. Verify directory selected
    const selectedPath = await playgroundPage.getSelectedPath();
    expect(selectedPath).toContain('small-project');

    // 3. Start transpilation
    await playgroundPage.startTranspilation();

    // 4. Verify progress indicator
    await expect(playgroundPage.progressIndicator.element).toBeVisible();

    // 5. Wait for completion
    await playgroundPage.waitForCompletion(30000);

    // 6. Verify 100% progress
    const progress = await playgroundPage.progressIndicator.getPercentage();
    expect(progress).toBe(100);

    // 7. Verify no errors
    const hasErrors = await playgroundPage.errorDisplay.hasErrors();
    expect(hasErrors).toBe(false);

    // 8. Verify download triggered (check downloads or network)
    // Implementation depends on download verification strategy
  });

  test('should show errors for invalid C++', async ({ page }) => {
    // Create project with invalid C++
    // Select directory
    // Start transpilation
    // Verify error display shows errors
    // Verify error messages are descriptive
  });

  test('should support cancellation', async ({ page }) => {
    // Select large project
    // Start transpilation
    // Click cancel after 2 seconds
    // Verify transpilation stopped
    // Verify partial progress saved or discarded
  });
});
```

### api.spec.ts

```typescript
import { test, expect } from '@playwright/test';

test.describe('API Endpoints', () => {
  test('POST /api/transpile - valid C++', async ({ request }) => {
    const response = await request.post('/api/transpile', {
      data: {
        source: 'int main() { return 0; }',
        options: { targetStandard: 'c99' }
      }
    });

    expect(response.status()).toBe(200);
    const json = await response.json();
    expect(json.success).toBe(true);
    expect(json.cCode).toContain('int main');
  });

  test('POST /api/transpile - invalid C++', async ({ request }) => {
    const response = await request.post('/api/transpile', {
      data: {
        source: 'invalid C++ code',
      }
    });

    expect(response.status()).toBe(500);
    const json = await response.json();
    expect(json.success).toBe(false);
    expect(json.error).toBeTruthy();
  });
});
```

### accessibility.spec.ts

```typescript
import { test, expect } from '@playwright/test';
import AxeBuilder from '@axe-core/playwright';

test.describe('Accessibility', () => {
  test('homepage should have no accessibility violations', async ({ page }) => {
    await page.goto('/');

    const accessibilityScanResults = await new AxeBuilder({ page }).analyze();

    expect(accessibilityScanResults.violations).toEqual([]);
  });

  test('playground should have no accessibility violations', async ({ page }) => {
    await page.goto('/playground');

    const accessibilityScanResults = await new AxeBuilder({ page }).analyze();

    expect(accessibilityScanResults.violations).toEqual([]);
  });

  test('keyboard navigation should work on homepage', async ({ page }) => {
    await page.goto('/');

    // Tab through focusable elements
    await page.keyboard.press('Tab');
    let focusedElement = await page.evaluate(() => document.activeElement?.tagName);
    expect(focusedElement).toBeTruthy();

    // Continue tabbing and verify focus moves
    await page.keyboard.press('Tab');
    await page.keyboard.press('Tab');

    // Verify focus visible indicator present
    const hasFocusVisible = await page.evaluate(() => {
      const el = document.activeElement;
      const styles = window.getComputedStyle(el!);
      return styles.outline !== 'none';
    });
    expect(hasFocusVisible).toBe(true);
  });
});
```

</test_specifications>

<page_object_examples>
Implement page objects following this pattern:

```typescript
// tests/e2e/pages/BasePage.ts
import { Page, Locator } from '@playwright/test';

export class BasePage {
  constructor(protected page: Page) {}

  async navigate(path: string = '/') {
    await this.page.goto(path);
    await this.waitForLoad();
  }

  async waitForLoad() {
    await this.page.waitForLoadState('networkidle');
  }

  async takeScreenshot(name: string) {
    await this.page.screenshot({ path: `screenshots/${name}.png`, fullPage: true });
  }

  async checkAccessibility() {
    // Import AxeBuilder and run scan
    // Return violations
  }
}

// tests/e2e/pages/PlaygroundPage.ts
import { Page, Locator } from '@playwright/test';
import { BasePage } from './BasePage';
import { DirectorySelectorComponent } from './components/DirectorySelectorComponent';
import { ProgressIndicatorComponent } from './components/ProgressIndicatorComponent';
import { ErrorDisplayComponent } from './components/ErrorDisplayComponent';

export class PlaygroundPage extends BasePage {
  readonly directorySelector: DirectorySelectorComponent;
  readonly progressIndicator: ProgressIndicatorComponent;
  readonly errorDisplay: ErrorDisplayComponent;
  readonly transpileButton: Locator;

  constructor(page: Page) {
    super(page);
    this.directorySelector = new DirectorySelectorComponent(page);
    this.progressIndicator = new ProgressIndicatorComponent(page);
    this.errorDisplay = new ErrorDisplayComponent(page);
    this.transpileButton = page.getByRole('button', { name: /transpile/i });
  }

  async navigate() {
    await super.navigate('/playground');
  }

  async selectDirectory(path: string) {
    // Implement File System Access API automation
    // This is the tricky part - may require CDP
    await this.directorySelector.selectDirectory(path);
  }

  async getSelectedPath(): Promise<string> {
    return await this.directorySelector.getSelectedPath();
  }

  async startTranspilation() {
    await this.transpileButton.click();
  }

  async waitForCompletion(timeout: number = 30000) {
    await this.progressIndicator.waitForComplete(timeout);
  }

  async cancelTranspilation() {
    await this.progressIndicator.clickCancel();
  }
}

// tests/e2e/pages/components/DirectorySelectorComponent.ts
import { Page, Locator } from '@playwright/test';

export class DirectorySelectorComponent {
  readonly selectButton: Locator;
  readonly selectedPathElement: Locator;
  readonly dropZone: Locator;

  constructor(private page: Page) {
    this.selectButton = page.getByRole('button', { name: /select directory/i });
    this.selectedPathElement = page.getByTestId('selected-path');
    this.dropZone = page.getByTestId('drop-zone');
  }

  async selectDirectory(path: string) {
    // THIS IS THE KEY CHALLENGE: Automating File System Access API

    // Option 1: CDP approach (if implemented)
    // await this.page.context().grantPermissions(['local-files']);
    // await this.selectButton.click();
    // Use CDP to provide directory handle

    // Option 2: Pre-authorized directory (if implemented)
    // await this.selectButton.click();
    // Directory picker opens and auto-selects pre-configured test directory

    // For now, document this as TODO
    throw new Error('File System Access API automation not yet implemented');
  }

  async getSelectedPath(): Promise<string> {
    return await this.selectedPathElement.textContent() || '';
  }

  async isDragEnabled(): Promise<boolean> {
    const classList = await this.dropZone.getAttribute('class');
    return !classList?.includes('disabled');
  }
}
```
</page_object_examples>

<headed_mode_configuration>
Critical configuration for headed mode:

```typescript
// playwright.config.ts
import { defineConfig, devices } from '@playwright/test';

export default defineConfig({
  testDir: './tests/e2e',
  fullyParallel: true,
  forbidOnly: !!process.env.CI,
  retries: process.env.CI ? 2 : 0,
  workers: process.env.CI ? 1 : undefined,
  reporter: [
    ['html'],
    ['list'],
    ['junit', { outputFile: 'test-results/junit.xml' }]
  ],

  use: {
    baseURL: 'http://localhost:4321',

    // CRITICAL: Headed mode for File System Access API
    headless: false,

    trace: 'on-first-retry',
    screenshot: 'only-on-failure',
    video: 'retain-on-failure',

    // Permissions for File System Access
    permissions: ['local-files'],
  },

  projects: [
    {
      name: 'chromium',
      use: {
        ...devices['Desktop Chrome'],
        // Additional Chromium-specific options
      },
    },
    // Firefox and WebKit for broader coverage
    {
      name: 'firefox',
      use: { ...devices['Desktop Firefox'] },
    },
    {
      name: 'webkit',
      use: { ...devices['Desktop Safari'] },
    },
  ],

  // Dev server
  webServer: {
    command: 'npm run dev',
    url: 'http://localhost:4321',
    reuseExistingServer: !process.env.CI,
    timeout: 120000,
  },
});
```

For CI with xvfb:
```yaml
# .github/workflows/playwright.yml
name: Playwright Tests

on:
  push:
    branches: [main, develop]
  pull_request:
    branches: [main, develop]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Setup Node.js
        uses: actions/setup-node@v4
        with:
          node-version: '20'

      - name: Install dependencies
        run: npm ci

      - name: Install Playwright browsers
        run: npx playwright install --with-deps

      - name: Build site
        run: npm run build

      - name: Run Playwright tests (headed mode with xvfb)
        run: xvfb-run --auto-servernum --server-args="-screen 0 1280x960x24" npm run test:e2e

      - name: Upload test results
        if: failure()
        uses: actions/upload-artifact@v4
        with:
          name: playwright-results
          path: |
            test-results/
            playwright-report/
          retention-days: 30
```
</headed_mode_configuration>

<success_criteria>
Before marking each phase complete:

**Phase 1**:
- [ ] Playwright installed
- [ ] Configuration created (headed mode)
- [ ] Directory structure created
- [ ] BasePage implemented
- [ ] Smoke test passing
- [ ] `npm run test:e2e:headed` works

**Phase 2**:
- [ ] Synthetic C++ projects created (small, medium, large)
- [ ] Component page objects implemented
- [ ] PlaygroundPage implemented
- [ ] File System Access automation working (or documented workaround)
- [ ] 6 playground tests passing
- [ ] API tests passing

**Phase 3**:
- [ ] Page objects for all major pages
- [ ] Navigation tests passing
- [ ] Content tests passing
- [ ] Mobile responsive tests passing

**Phase 4**:
- [ ] Accessibility tests passing (0 critical violations)
- [ ] Keyboard navigation verified
- [ ] Performance benchmarks established
- [ ] All accessibility checks passing

**Phase 5**:
- [ ] GitHub Actions workflow created
- [ ] Tests passing in CI (headed mode with xvfb)
- [ ] Artifacts uploading on failure
- [ ] Test reporting configured
- [ ] README badge added

**Overall**:
- [ ] All P0 tests passing (critical path)
- [ ] All P1 tests passing (high priority)
- [ ] Test execution time < 5 minutes (local)
- [ ] Test execution time < 10 minutes (CI)
- [ ] 0% flaky tests
- [ ] Documentation complete
- [ ] TypeScript types correct
- [ ] No linting errors
</success_criteria>

<file_system_access_automation>
**CRITICAL CHALLENGE**: Automating File System Access API in Playwright

### Approaches to Research and Implement:

**Option 1: CDP (Chrome DevTools Protocol)**
```typescript
// Use CDP to intercept and automate file picker
const client = await page.context().newCDPSession(page);

await client.send('Browser.grantPermissions', {
  permissions: ['fileSystem'],
  origin: 'http://localhost:4321'
});

// Provide file handles via CDP
// This is complex and may require custom implementation
```

**Option 2: Pre-Authorized Test Directories**
```typescript
// Use IndexedDB or localStorage to pre-authorize test directories
await page.evaluate((testDirPath) => {
  localStorage.setItem('test-directory-handle', testDirPath);
}, TEST_DIR_PATH);

// Modify DirectorySelector component to check for test mode
// If in test mode, skip picker and use pre-authorized directory
```

**Option 3: Manual Interaction (Semi-Automated)**
```typescript
// For headed mode, pause test and let user manually select directory
await page.pause(); // Playwright Inspector opens
// User manually selects directory
// Test continues after selection
```

**Recommended**: Start with Option 2 (pre-authorized directories) as it's most reliable for automated testing. Document Option 3 as fallback for complex scenarios.
</file_system_access_automation>

<output>
Create the following in `.prompts/019-playwright-e2e-testing-implement/`:

**Implementation Files**:
- `tests/playwright.config.ts`
- `tests/e2e/pages/BasePage.ts`
- `tests/e2e/pages/PlaygroundPage.ts`
- `tests/e2e/pages/HomePage.ts`
- `tests/e2e/pages/components/DirectorySelectorComponent.ts`
- `tests/e2e/pages/components/ProgressIndicatorComponent.ts`
- `tests/e2e/pages/components/ErrorDisplayComponent.ts`
- `tests/e2e/specs/smoke.spec.ts`
- `tests/e2e/specs/playground.spec.ts`
- `tests/e2e/specs/api.spec.ts`
- `tests/e2e/specs/navigation.spec.ts`
- `tests/e2e/specs/accessibility.spec.ts`
- `tests/e2e/specs/performance.spec.ts`
- `tests/e2e/fixtures/cpp-projects/small-project/` (with C++ files)
- `tests/e2e/utils/test-helpers.ts`
- `.github/workflows/playwright.yml`

**Documentation**:
- `tests/e2e/README.md` - Test suite documentation
- `.prompts/019-playwright-e2e-testing-implement/Phase-1-SUMMARY.md`
- `.prompts/019-playwright-e2e-testing-implement/Phase-2-SUMMARY.md`
- `.prompts/019-playwright-e2e-testing-implement/Phase-3-SUMMARY.md`
- `.prompts/019-playwright-e2e-testing-implement/Phase-4-SUMMARY.md`
- `.prompts/019-playwright-e2e-testing-implement/Phase-5-SUMMARY.md`
- `.prompts/019-playwright-e2e-testing-implement/SUMMARY.md` (final)

**Updates**:
- `package.json` - Add test:e2e scripts
- `README.md` - Add Playwright badge and testing section
</output>

<notes>
- Execute phases sequentially (1 → 2 → 3 → 4 → 5)
- Create SUMMARY.md after each phase
- File System Access API automation is the hardest part - allocate extra time
- Headed mode is mandatory - ensure headless: false throughout
- Test with real browser interactions, not just assertions
- Document any workarounds or limitations
- If File System Access automation proves too difficult, document manual steps
- Keep tests maintainable and stable (avoid flaky tests)
- Use Playwright best practices (auto-waiting, stable selectors, etc.)
</notes>
