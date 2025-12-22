# Playwright E2E Testing Research - Comprehensive Analysis

```xml
<research>
  <meta>
    <date>2025-12-21</date>
    <version>1.0</version>
    <confidence>High</confidence>
    <conducted_by>Claude Sonnet 4.5</conducted_by>
    <project>C++ to C Transpiler Website</project>
    <project_path>/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/website</project_path>
  </meta>

  <executive_summary>
    This research provides comprehensive analysis for implementing Playwright E2E testing for the C++ to C Transpiler website, with specific focus on HEADED browser mode testing. Key findings include:

    1. **Current State**: Playwright 1.57.0 is already installed with basic configuration. Two E2E tests exist (debug.spec.ts, mobile-navigation.spec.ts) with 314 Vitest unit tests achieving 93.6% pass rate.

    2. **Critical Challenge**: File System Access API (showDirectoryPicker) testing requires headed mode and presents significant automation challenges. Playwright lacks native support for automating File System Access API permission dialogs.

    3. **Recommended Approach**: Hybrid testing strategy combining automated E2E tests for standard flows with manual/semi-automated testing for File System Access API features. Use mocking (fsa-mock library) for automated tests and headed mode with manual intervention for integration tests.

    4. **Technology Stack**: Astro SSG + React + TypeScript with existing mobile navigation tests demonstrating best practices (accessibility, responsive design, keyboard navigation).

    5. **High-Value Test Coverage**: Priority focus on critical flows (homepage navigation, documentation, features), accessibility compliance (WCAG 2.1 AA), performance metrics (Core Web Vitals), and cross-browser compatibility (Chromium, Firefox, WebKit).

    6. **CI/CD Integration**: GitHub Actions workflow exists for deployment. Playwright integration requires adding test job with sharding for parallel execution and artifact management for test reports.

    **Confidence Level**: High (85%) - Research is comprehensive with validated sources from official Playwright documentation, GitHub issues, and recent 2024-2025 articles. Primary uncertainty is around File System Access API automation feasibility.
  </executive_summary>

  <findings>
    <finding id="1" category="Infrastructure">
      <title>Current Test Setup Analysis</title>
      <description>
        Analysis of existing test infrastructure reveals a partially configured Playwright setup with strong Vitest unit testing foundation.
      </description>

      <current_state>
        **Package Dependencies** (package.json):
        - @playwright/test: ^1.57.0 (latest version as of Dec 2024)
        - Vitest: ^3.2.4 with coverage (v8), UI, and jsdom/happy-dom
        - @testing-library/react: ^16.3.1
        - TypeScript: ^5.9.3

        **Existing Playwright Configuration** (playwright.config.ts):
        - Test directory: ./tests
        - Parallel execution: fullyParallel: true
        - CI optimizations: retries (2), workers (1)
        - Base URL: http://localhost:4322/cpp-to-c-website
        - Trace: on-first-retry
        - Single project: Chromium (Desktop Chrome)
        - Reporter: HTML

        **Existing E2E Tests** (2 tests):
        1. tests/debug.spec.ts - Basic page structure verification
        2. tests/mobile-navigation.spec.ts - Comprehensive mobile navigation tests (22 test cases)
           - Responsive behavior (desktop/mobile viewports)
           - Accessibility (ARIA attributes, WCAG AAA touch targets 44px)
           - Keyboard navigation and focus management
           - User interactions (open/close, overlay, escape key)

        **Vitest Unit Tests**:
        - 314 tests total (93.6% passing - 294 passed, 20 failed)
        - Coverage: v8 provider with HTML/JSON/text reports
        - Test files: src/**/*.test.ts, src/**/*.test.tsx
        - Environment: jsdom
        - Component tests for Playground (DirectorySelector, ErrorDisplay, PlaygroundController, ProgressIndicator)

        **CI/CD** (.github/workflows/deploy.yml):
        - Trigger: Push to main, release/** branches + manual dispatch
        - Platform: GitHub Actions (ubuntu-latest, Node.js 20)
        - Build: Astro build → GitHub Pages deployment
        - No test execution in current CI workflow
      </current_state>

      <gaps>
        1. **No E2E Test Execution in CI**: Playwright tests not integrated into CI/CD pipeline
        2. **Limited Browser Coverage**: Only Chromium configured, missing Firefox and WebKit
        3. **No Accessibility Testing**: No axe-core or accessibility test integration
        4. **No Performance Testing**: No Lighthouse or Core Web Vitals measurement
        5. **Missing Test Fixtures**: No structured test data or fixtures setup
        6. **No API Testing**: Backend API endpoints (/api/transpile, /api/validate) not tested
        7. **Limited Coverage**: Only 2 E2E tests (mobile navigation focus)
        8. **No Visual Regression**: No screenshot comparison or visual testing
        9. **Missing Headed Mode Config**: No headless: false configuration for File System Access API
        10. **No Test Data**: No synthetic C++ projects for playground testing
      </gaps>

      <recommendations>
        **Immediate Actions**:
        1. Add Firefox and WebKit projects to playwright.config.ts
        2. Create headed mode configuration for File System Access API tests
        3. Integrate Playwright tests into GitHub Actions CI workflow
        4. Install @axe-core/playwright for accessibility testing
        5. Create test fixtures directory structure (tests/fixtures/)

        **Short-Term Actions**:
        1. Expand test coverage to all pages (homepage, features, docs, etc.)
        2. Implement API testing for /api/transpile and /api/validate
        3. Add performance testing with Lighthouse integration
        4. Create synthetic C++ test projects (small, medium, large)
        5. Implement visual regression testing with screenshot comparison

        **Long-Term Actions**:
        1. Establish baseline accessibility compliance (WCAG 2.1 AA)
        2. Create comprehensive test documentation
        3. Implement test data management strategy
        4. Add flaky test detection and reporting
        5. Consider Playwright MCP server integration for AI-assisted testing
      </recommendations>

      <priority>Critical</priority>

      <sources>
        - /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/website/package.json
        - /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/website/playwright.config.ts
        - /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/website/vitest.config.ts
        - /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/website/.github/workflows/deploy.yml
      </sources>
    </finding>

    <finding id="2" category="Best Practices">
      <title>Playwright 2025 Best Practices</title>
      <description>
        Latest Playwright features, best practices, and recommended patterns for 2025 based on official documentation and community resources.
      </description>

      <key_practices>
        **Version 1.57+ Features** (Latest as of Dec 2024):
        - Chrome for Testing builds (replacing Chromium for headed/headless)
        - Playwright Agents (planner, generator, healer for LLM-guided test building)
        - Automatic toBeVisible() assertions in Codegen
        - Test step timeout option for granular control
        - Cookie partitioning support (partitionKey property)
        - failOnStatusCode for APIRequestContext (strict API testing)
        - failOnFlakyTests config option for CI/CD stability

        **Core Best Practices**:
        1. **User-Facing Locators**: Use page.getByRole('button', { name: 'submit' }) instead of CSS selectors
        2. **Test Isolation**: Each test independent with own storage, cookies, data
        3. **Parallel Execution**: fullyParallel: true with multiple workers
        4. **Cross-Browser Testing**: Run same tests on Chromium, Firefox, WebKit
        5. **CI/CD Integration**: Test on each commit and pull request
        6. **Retry Strategy**: Configure retries for flaky tests (2x in CI recommended)
        7. **Trace Collection**: Use trace: 'on-first-retry' for debugging
        8. **Project Sharding**: Distribute tests across multiple machines for speed

        **Locator Strategy** (Priority Order):
        1. getByRole() - Accessibility-based (highest priority)
        2. getByLabel() - Form elements with labels
        3. getByPlaceholder() - Form inputs with placeholders
        4. getByText() - Non-interactive text matching
        5. getByTestId() - data-testid attributes (last resort)

        **Test Organization**:
        - Group related tests with test.describe()
        - Use test.beforeEach() for common setup
        - Leverage fixtures for reusable components
        - Keep tests focused and atomic (single assertion focus)

        **Performance Optimization**:
        - Use page.waitForLoadState('networkidle') sparingly
        - Prefer explicit assertions over arbitrary waits
        - Enable parallel execution at test and project level
        - Use worker-scoped fixtures for expensive setup

        **Debugging**:
        - Run with --headed flag for visual debugging
        - Use --debug flag for step-through debugging
        - Leverage UI mode with --ui flag for interactive testing
        - Collect traces and screenshots on failure
      </key_practices>

      <code_examples>
        **Example: Recommended Locator Pattern**
        ```typescript
        // ✅ Good - User-facing, accessibility-friendly
        await page.getByRole('button', { name: 'Transpile Project' }).click();
        await page.getByLabel('Directory path').fill('/path/to/project');

        // ❌ Avoid - Fragile, implementation-dependent
        await page.locator('.transpile-button').click();
        await page.locator('#directory-input').fill('/path/to/project');
        ```

        **Example: Test Isolation Pattern**
        ```typescript
        test.describe('Playground Workflow', () => {
          test.beforeEach(async ({ page }) => {
            await page.goto('/playground');
          });

          test('should transpile small project', async ({ page }) => {
            // Each test is independent - manages own setup/teardown
            await selectTestDirectory(page, 'small-project');
            await transpileProject(page);
            await expectSuccessfulTranspilation(page);
          });
        });
        ```

        **Example: Parallel Project Configuration**
        ```typescript
        // playwright.config.ts
        export default defineConfig({
          fullyParallel: true,
          projects: [
            { name: 'chromium', use: { ...devices['Desktop Chrome'] } },
            { name: 'firefox', use: { ...devices['Desktop Firefox'] } },
            { name: 'webkit', use: { ...devices['Desktop Safari'] } },
            { name: 'mobile-chrome', use: { ...devices['Pixel 5'] } },
          ],
        });
        ```

        **Example: API Testing with Strict Mode**
        ```typescript
        test('API transpile endpoint', async ({ request }) => {
          const response = await request.post('/api/transpile', {
            data: { code: 'int main() { return 0; }' },
            failOnStatusCode: true, // Throw on non-2xx/3xx
          });

          expect(response.ok()).toBeTruthy();
          const json = await response.json();
          expect(json.success).toBe(true);
        });
        ```
      </code_examples>

      <priority>High</priority>

      <sources>
        - https://playwright.dev/docs/release-notes
        - https://playwright.dev/docs/best-practices
        - https://medium.com/@szaranger/playwright-1-57-the-must-use-update-for-web-test-automation-in-2025-b194df6c9e03
        - https://thinksys.com/qa-testing/playwright-features/
      </sources>
    </finding>

    <finding id="3" category="Integration">
      <title>Astro + Playwright Integration Patterns</title>
      <description>
        Comprehensive guide to integrating Playwright E2E testing with Astro SSG framework for optimal developer experience and test reliability.
      </description>

      <integration_approach>
        **Setup Requirements**:
        1. Install Playwright: `npm install -D @playwright/test`
        2. Initialize config: `npx playwright install`
        3. Configure webServer in playwright.config.ts
        4. Add test scripts to package.json

        **Astro-Specific Configuration**:
        ```typescript
        // playwright.config.ts
        export default defineConfig({
          testDir: './tests',
          use: {
            baseURL: 'http://localhost:4321', // Astro default dev port
          },
          webServer: {
            command: 'npm run preview', // Use preview for production build
            port: 4321,
            reuseExistingServer: !process.env.CI,
            timeout: 120000, // 2 minutes for build + server startup
          },
        });
        ```

        **SSG-Specific Considerations**:
        - **Static Generation**: Test against production build (npm run preview)
        - **Build Time**: Allow adequate timeout for full site generation
        - **Client Hydration**: Wait for React hydration in interactive components
        - **Base Path**: Configure base URL to match deployment path
        - **Asset Loading**: Account for static asset loading delays

        **Testing React Islands** (client:only, client:load):
        ```typescript
        test('React component hydration', async ({ page }) => {
          await page.goto('/playground');

          // Wait for React hydration marker
          await page.waitForSelector('[data-hydrated="true"]', {
            state: 'attached',
            timeout: 5000
          });

          // Now safe to interact with React component
          await page.getByRole('button', { name: 'Select Directory' }).click();
        });
        ```

        **Workflow**:
        1. Run `npm run build` - Generate static site
        2. Run `npm run preview` - Start preview server
        3. Run `npx playwright test` - Execute E2E tests
        4. Or use webServer to automate build + preview

        **Component Testing Limitation**:
        - Astro components: Require E2E tests (no isolated component testing)
        - React components: Can use Vitest + @testing-library/react (current setup)
        - Recommendation: E2E for integration, unit tests for component logic
      </integration_approach>

      <challenges>
        1. **Build Performance**: Full Astro build can be slow - use webServer caching
        2. **Hydration Timing**: React components may not be immediately interactive
        3. **Route Handling**: SSG generates static HTML files - ensure proper routing
        4. **Base Path**: GitHub Pages uses /cpp-to-c-website - must match in tests
        5. **Asset References**: Static assets must resolve correctly in test environment
      </challenges>

      <solutions>
        1. Use `reuseExistingServer: !process.env.CI` to speed up local development
        2. Add explicit hydration checks before interacting with React components
        3. Test against preview server (mirrors production environment)
        4. Configure baseURL to match deployment base path
        5. Verify asset loading with network idle checks when needed
      </solutions>

      <priority>High</priority>

      <sources>
        - https://docs.astro.build/en/guides/testing/
        - https://github.com/QwikDev/astro/blob/main/playwright.config.ts
        - https://www.frontendmentor.io/solutions/ssr-astro-solution-with-e2e-playwright-tests-and-native-html-forms-QOB2JYeeG6
      </sources>
    </finding>

    <finding id="4" category="File System Access API">
      <title>File System Access API Testing Challenges and Solutions</title>
      <description>
        Critical analysis of testing File System Access API (showDirectoryPicker) with Playwright in headed mode, including limitations, workarounds, and recommended strategies.
      </description>

      <current_limitations>
        **Playwright Limitations** (as of Dec 2024):
        - ❌ No native support for File System Access API permission dialogs
        - ❌ Cannot programmatically accept "View files"/"Edit files" permissions
        - ❌ GitHub Issue #18267 (Oct 2022) - Still open, no resolution
        - ❌ GitHub Issue #11288 - Feature request for Native File System automation
        - ❌ showDirectoryPicker() dialog blocks test execution
        - ❌ CDP (Chrome DevTools Protocol) cannot interact with native file pickers

        **API Characteristics**:
        - Requires user interaction (security feature)
        - Browser permission dialog is native OS-level (not DOM element)
        - Only works in secure contexts (HTTPS or localhost)
        - Chromium 86+ (Chrome, Edge) - Full support
        - Firefox/Safari - Partial support with webkitdirectory fallback
        - Mobile browsers - No support
      </current_limitations>

      <headed_mode_requirements>
        **Why Headed Mode is Required**:
        1. File System Access API disabled in headless mode (security)
        2. Permission dialogs require visible browser window
        3. User interaction is mandatory security feature
        4. showDirectoryPicker() throws in headless context

        **Configuration for Headed Mode**:
        ```typescript
        // playwright.config.ts
        export default defineConfig({
          use: {
            headless: false, // CRITICAL for File System Access API
            launchOptions: {
              slowMo: 500, // Slow down for manual intervention
            },
          },
          projects: [
            {
              name: 'chromium-headed',
              use: {
                ...devices['Desktop Chrome'],
                headless: false,
                channel: 'chrome', // Use actual Chrome (not Chromium)
              },
            },
          ],
        });
        ```
      </headed_mode_requirements>

      <workaround_strategies>
        **Strategy 1: Mocking with fsa-mock Library**
        - Library: https://github.com/alxcube/fsa-mock
        - Approach: Replace File System Access API with mock implementation
        - Use Case: Automated CI/CD testing without user interaction
        - Implementation:
          ```typescript
          // Test setup
          import { createMockFileSystem } from 'fsa-mock';

          test.beforeEach(async ({ page }) => {
            // Inject mock File System Access API
            await page.addInitScript(() => {
              const mockFS = createMockFileSystem({
                '/test-project': {
                  'main.cpp': 'int main() { return 0; }',
                  'utils.h': '#pragma once',
                },
              });
              window.showDirectoryPicker = async () => mockFS.getRoot();
            });
          });
          ```

        **Strategy 2: Manual/Semi-Automated Testing**
        - Run tests in headed mode with manual intervention
        - Use test.setTimeout(60000) to allow manual picker selection
        - Document expected manual steps in test comments
        - Use for integration/smoke tests (not CI)
        - Implementation:
          ```typescript
          test('Playground directory selection (MANUAL)', async ({ page }) => {
            test.setTimeout(60000); // 60 seconds for manual intervention

            await page.goto('/playground');

            // Trigger picker - MANUAL: Select test-project directory
            await page.getByRole('button', { name: 'Select Directory' }).click();

            // Wait for manual selection (up to 30 seconds)
            await page.waitForSelector('[data-directory-selected="true"]', {
              timeout: 30000,
            });

            // Continue automated testing
            await expect(page.getByText('test-project')).toBeVisible();
          });
          ```

        **Strategy 3: Pre-Granted Permissions (Experimental)**
        - Use CDP to grant persistent permissions
        - Requires custom permission handling
        - Not officially supported for File System Access API
        - May not work for showDirectoryPicker (native dialog)

        **Strategy 4: Alternative Input Methods**
        - Fallback to webkitdirectory for automated testing
        - Test non-File System Access API code path
        - Use input[type="file"][webkitdirectory] for automation
        - Implementation:
          ```typescript
          test('Directory upload fallback', async ({ page }) => {
            await page.goto('/playground');

            // Use webkitdirectory input (automatable)
            const fileInput = page.locator('input[type="file"][webkitdirectory]');
            await fileInput.setInputFiles([
              './tests/fixtures/test-project/main.cpp',
              './tests/fixtures/test-project/utils.h',
            ]);

            await expect(page.getByText('2 files selected')).toBeVisible();
          });
          ```
      </workaround_strategies>

      <recommended_approach>
        **Hybrid Testing Strategy**:

        1. **Automated Tests (CI/CD)** - 80% coverage:
           - Use fsa-mock for File System Access API mocking
           - Test all logic independent of real file system
           - Test API endpoints with mock data
           - Test UI components with mocked dependencies
           - Test error handling and edge cases

        2. **Manual Integration Tests** - 15% coverage:
           - Run locally in headed mode with manual picker selection
           - Verify real File System Access API integration
           - Test actual directory traversal and file reading
           - Validate real browser behavior
           - Document as "smoke tests" or "integration tests"

        3. **Fallback Path Tests** - 5% coverage:
           - Test webkitdirectory code path (fully automated)
           - Verify Firefox/Safari compatibility
           - Test mobile browser graceful degradation

        **Test Organization**:
        ```
        tests/
          ├── e2e/               # Standard E2E tests (headless OK)
          │   ├── homepage.spec.ts
          │   ├── features.spec.ts
          │   └── docs.spec.ts
          ├── playground/        # Playground tests
          │   ├── mocked/        # Automated with fsa-mock (headless OK)
          │   │   ├── directory-selection.spec.ts
          │   │   ├── transpilation.spec.ts
          │   │   └── error-handling.spec.ts
          │   ├── integration/   # Manual headed mode (tagged @manual)
          │   │   └── real-filesystem.spec.ts
          │   └── fallback/      # webkitdirectory tests (headless OK)
          │       └── fallback-upload.spec.ts
          └── fixtures/          # Test data
              └── test-projects/
                  ├── small/
                  ├── medium/
                  └── large/
        ```
      </recommended_approach>

      <impact>High</impact>

      <priority>Critical</priority>

      <sources>
        - https://github.com/microsoft/playwright/issues/18267
        - https://github.com/microsoft/playwright/issues/11288
        - https://developer.chrome.com/docs/capabilities/web-apis/file-system-access
        - https://github.com/alxcube/fsa-mock
        - https://developer.mozilla.org/en-US/docs/Web/API/File_System_API
      </sources>
    </finding>

    <finding id="5" category="Accessibility">
      <title>Accessibility Testing with Playwright and axe-core</title>
      <description>
        Comprehensive approach to automated accessibility testing using Playwright with axe-core integration for WCAG 2.1 AA compliance verification.
      </description>

      <implementation>
        **Installation**:
        ```bash
        npm install -D @axe-core/playwright
        ```

        **Basic Usage**:
        ```typescript
        import { test, expect } from '@playwright/test';
        import AxeBuilder from '@axe-core/playwright';

        test('Homepage accessibility', async ({ page }) => {
          await page.goto('/');

          const accessibilityScanResults = await new AxeBuilder({ page })
            .withTags(['wcag2a', 'wcag2aa', 'wcag21a', 'wcag21aa'])
            .analyze();

          expect(accessibilityScanResults.violations).toEqual([]);
        });
        ```

        **WCAG 2.1 AA Configuration**:
        ```typescript
        // tests/accessibility/config.ts
        export const WCAG_AA_TAGS = [
          'wcag2a',      // WCAG 2.0 Level A
          'wcag2aa',     // WCAG 2.0 Level AA
          'wcag21a',     // WCAG 2.1 Level A
          'wcag21aa',    // WCAG 2.1 Level AA
        ];

        export const createAccessibilityTest = (pageName: string, path: string) => {
          test(`${pageName} - WCAG 2.1 AA compliance`, async ({ page }) => {
            await page.goto(path);

            const results = await new AxeBuilder({ page })
              .withTags(WCAG_AA_TAGS)
              .analyze();

            // Log violations for debugging
            if (results.violations.length > 0) {
              console.log(`Accessibility violations on ${pageName}:`);
              results.violations.forEach(violation => {
                console.log(`- ${violation.id}: ${violation.description}`);
                console.log(`  Impact: ${violation.impact}`);
                console.log(`  Elements: ${violation.nodes.length}`);
              });
            }

            expect(results.violations).toEqual([]);
          });
        };
        ```

        **Selective Testing** (Exclude Known Issues):
        ```typescript
        const results = await new AxeBuilder({ page })
          .withTags(WCAG_AA_TAGS)
          .exclude('#third-party-widget') // Exclude elements outside control
          .disableRules(['color-contrast']) // Temporarily disable specific rules
          .analyze();
        ```

        **Component-Level Testing**:
        ```typescript
        test('Playground controller accessibility', async ({ page }) => {
          await page.goto('/playground');

          // Test specific component
          const results = await new AxeBuilder({ page })
            .include('.playground-container')
            .withTags(WCAG_AA_TAGS)
            .analyze();

          expect(results.violations).toEqual([]);
        });
        ```
      </implementation>

      <coverage_areas>
        **Automatic Checks** (axe-core):
        1. Color contrast (WCAG AA: 4.5:1 for normal text, 3:1 for large text)
        2. Form labels and ARIA attributes
        3. Heading hierarchy (h1 → h2 → h3)
        4. Alt text for images
        5. Link text (no "click here")
        6. Keyboard accessibility (tab order, focus indicators)
        7. ARIA roles and states
        8. HTML structure and semantics

        **Manual Checks** (Recommended):
        1. Screen reader testing (NVDA, JAWS, VoiceOver)
        2. Keyboard-only navigation
        3. Zoom testing (200%, 400%)
        4. Touch target sizes (44x44px minimum - WCAG AAA)
        5. Focus management in dynamic content
        6. Error message clarity

        **Existing Implementation** (mobile-navigation.spec.ts):
        - ✅ Touch target size verification (44px WCAG AAA)
        - ✅ ARIA attributes (aria-expanded, aria-hidden, aria-current)
        - ✅ Focus management and focus trap
        - ✅ Keyboard navigation (Tab, Escape)
        - ✅ Focus restoration on close

        **Coverage Plan**:
        ```
        tests/accessibility/
          ├── pages/
          │   ├── homepage.spec.ts
          │   ├── playground.spec.ts
          │   ├── features.spec.ts
          │   ├── docs.spec.ts
          │   └── architecture.spec.ts
          ├── components/
          │   ├── navigation.spec.ts
          │   ├── forms.spec.ts
          │   └── modals.spec.ts
          └── keyboard/
              ├── tab-navigation.spec.ts
              └── shortcuts.spec.ts
        ```
      </coverage_areas>

      <wcag_criteria>
        **WCAG 2.1 Level AA Success Criteria** (50 criteria):

        **Perceivable**:
        - 1.1.1 Non-text Content
        - 1.2.1-1.2.5 Time-based Media
        - 1.3.1-1.3.5 Adaptable
        - 1.4.1-1.4.5, 1.4.10-1.4.13 Distinguishable

        **Operable**:
        - 2.1.1-2.1.4 Keyboard Accessible
        - 2.2.1-2.2.2 Enough Time
        - 2.3.1 Seizures
        - 2.4.1-2.4.7 Navigable
        - 2.5.1-2.5.4 Input Modalities

        **Understandable**:
        - 3.1.1-3.1.2 Readable
        - 3.2.1-3.2.4 Predictable
        - 3.3.1-3.3.4 Input Assistance

        **Robust**:
        - 4.1.1-4.1.3 Compatible

        **Priority Focus** (High-Impact Criteria):
        - 1.4.3 Contrast (Minimum) - Color contrast ratios
        - 2.1.1 Keyboard - All functionality keyboard accessible
        - 2.4.7 Focus Visible - Focus indicators visible
        - 4.1.2 Name, Role, Value - ARIA implementation
      </wcag_criteria>

      <best_practices>
        1. **Run on every page**: Include accessibility tests for all routes
        2. **Test interactive states**: Modal open, menu expanded, form errors
        3. **Mobile accessibility**: Touch targets, zoom, orientation
        4. **Dynamic content**: ARIA live regions, focus management
        5. **CI integration**: Fail builds on accessibility violations
        6. **Baseline establishment**: Document and track violation remediation
        7. **Manual testing**: Complement automated tests with screen reader testing
      </best_practices>

      <priority>High</priority>

      <sources>
        - https://playwright.dev/docs/accessibility-testing
        - https://dev.to/subito/how-we-automate-accessibility-testing-with-playwright-and-axe-3ok5
        - https://medium.com/@shukla.akhilesh1311/accessibility-unleashed-automate-wcag-checks-with-playwright-and-axe-core-842c80ec4fd1
        - https://medium.com/@merisstupar11/achieving-wcag-standard-with-playwright-accessibility-tests-f634b6f9e51d
      </sources>
    </finding>

    <finding id="6" category="Performance">
      <title>Performance Testing with Playwright and Lighthouse</title>
      <description>
        Strategies for measuring and validating web performance using Playwright, including Core Web Vitals tracking and Lighthouse integration.
      </description>

      <core_web_vitals>
        **Three Key Metrics**:

        1. **Largest Contentful Paint (LCP)**
           - Measures: Loading performance
           - Target: < 2.5 seconds
           - Method: PerformanceObserver with 'largest-contentful-paint' type

        2. **First Input Delay (FID)** / Interaction to Next Paint (INP)
           - Measures: Interactivity responsiveness
           - Target: < 100ms (FID), < 200ms (INP)
           - Method: PerformanceObserver with 'first-input' type

        3. **Cumulative Layout Shift (CLS)**
           - Measures: Visual stability
           - Target: < 0.1
           - Method: Layout Instability API

        **Implementation**:
        ```typescript
        import { test, expect } from '@playwright/test';

        test('Core Web Vitals - Homepage', async ({ page }) => {
          await page.goto('/');

          // Measure Core Web Vitals
          const metrics = await page.evaluate(() => {
            return new Promise((resolve) => {
              const vitals: any = {};

              // LCP
              new PerformanceObserver((list) => {
                const entries = list.getEntries();
                const lastEntry = entries[entries.length - 1];
                vitals.lcp = lastEntry.renderTime || lastEntry.loadTime;
              }).observe({ type: 'largest-contentful-paint', buffered: true });

              // FID
              new PerformanceObserver((list) => {
                const entries = list.getEntries();
                vitals.fid = entries[0].processingStart - entries[0].startTime;
              }).observe({ type: 'first-input', buffered: true });

              // CLS
              let cls = 0;
              new PerformanceObserver((list) => {
                for (const entry of list.getEntries() as any[]) {
                  if (!entry.hadRecentInput) {
                    cls += entry.value;
                  }
                }
                vitals.cls = cls;
              }).observe({ type: 'layout-shift', buffered: true });

              // Wait for metrics to be collected
              setTimeout(() => resolve(vitals), 3000);
            });
          });

          // Assertions
          expect(metrics.lcp).toBeLessThan(2500); // 2.5 seconds
          expect(metrics.cls).toBeLessThan(0.1);  // 0.1 max
          console.log('Core Web Vitals:', metrics);
        });
        ```
      </core_web_vitals>

      <lighthouse_integration>
        **Installation**:
        ```bash
        npm install -D lighthouse playwright-lighthouse
        ```

        **Usage**:
        ```typescript
        import { test } from '@playwright/test';
        import { playAudit } from 'playwright-lighthouse';

        test('Lighthouse audit - Homepage', async ({ page }) => {
          await page.goto('/');

          await playAudit({
            page,
            thresholds: {
              performance: 90,
              accessibility: 95,
              'best-practices': 90,
              seo: 90,
            },
            reports: {
              formats: { html: true, json: true },
              directory: './lighthouse-reports',
            },
          });
        });
        ```

        **Key Metrics**:
        - Performance Score (0-100)
        - First Contentful Paint (FCP)
        - Time to Interactive (TTI)
        - Speed Index
        - Total Blocking Time (TBT)
        - Largest Contentful Paint (LCP)
      </lighthouse_integration>

      <performance_testing_strategy>
        **1. Page Load Performance**:
        ```typescript
        test('Page load time - Playground', async ({ page }) => {
          const startTime = Date.now();

          await page.goto('/playground', { waitUntil: 'load' });

          const loadTime = Date.now() - startTime;
          expect(loadTime).toBeLessThan(3000); // 3 seconds max

          console.log(`Playground loaded in ${loadTime}ms`);
        });
        ```

        **2. Network Performance**:
        ```typescript
        test('Bundle size and requests', async ({ page }) => {
          const requests: any[] = [];

          page.on('request', (request) => {
            requests.push({
              url: request.url(),
              resourceType: request.resourceType(),
            });
          });

          await page.goto('/');
          await page.waitForLoadState('networkidle');

          const jsRequests = requests.filter(r => r.resourceType === 'script');
          const cssRequests = requests.filter(r => r.resourceType === 'stylesheet');

          console.log(`JavaScript files: ${jsRequests.length}`);
          console.log(`CSS files: ${cssRequests.length}`);
          console.log(`Total requests: ${requests.length}`);

          expect(jsRequests.length).toBeLessThan(10); // Reasonable limit
        });
        ```

        **3. API Performance**:
        ```typescript
        test('Transpile API response time', async ({ request }) => {
          const startTime = Date.now();

          const response = await request.post('/api/transpile', {
            data: { code: 'int main() { return 0; }' },
          });

          const responseTime = Date.now() - startTime;

          expect(response.ok()).toBeTruthy();
          expect(responseTime).toBeLessThan(1000); // 1 second max

          console.log(`API response time: ${responseTime}ms`);
        });
        ```

        **4. Throttling Tests**:
        ```typescript
        test('Performance on slow 3G', async ({ page, context }) => {
          // Simulate slow network
          await context.route('**/*', (route) => {
            route.continue({
              // Slow 3G: 400kbps down, 400kbps up, 400ms RTT
            });
          });

          const startTime = Date.now();
          await page.goto('/');
          const loadTime = Date.now() - startTime;

          console.log(`Load time on slow 3G: ${loadTime}ms`);
          expect(loadTime).toBeLessThan(10000); // 10 seconds max on slow network
        });
        ```
      </performance_testing_strategy>

      <recommendations>
        1. **Baseline Establishment**: Run performance tests to establish baseline metrics
        2. **CI Monitoring**: Track performance over time, fail on significant regressions
        3. **Real User Conditions**: Test with network throttling (3G, 4G, WiFi)
        4. **Critical Paths**: Focus on high-traffic pages (homepage, playground)
        5. **Budget Enforcement**: Set performance budgets (JS size, load time, CWV)
        6. **Lighthouse CI**: Integrate Lighthouse CI for automated performance checks
      </recommendations>

      <priority>Medium</priority>

      <sources>
        - https://www.checklyhq.com/docs/learn/playwright/performance/
        - https://focusreactive.com/testing-web-application-performance-with-playwright/
        - https://www.thegreenreport.blog/articles/frontend-performance-testing-with-playwright-and-lighthouse/frontend-performance-testing-with-playwright-and-lighthouse.html
        - https://testingplus.me/how-to-integrate-lighthouse-playwright-performance-testing-2025-guide/
      </sources>
    </finding>

    <finding id="7" category="Cross-Browser">
      <title>Cross-Browser Testing Strategy</title>
      <description>
        Comprehensive approach to testing across Chromium, Firefox, and WebKit browser engines with Playwright's unified API.
      </description>

      <browser_coverage>
        **Supported Browsers** (Playwright 1.57+):

        1. **Chromium** (Chrome/Edge):
           - Engine: Blink + V8
           - Market Share: ~65%
           - Features: Full File System Access API support
           - Testing Priority: High

        2. **Firefox**:
           - Engine: Gecko + SpiderMonkey
           - Market Share: ~3%
           - Features: Partial File System Access (webkitdirectory)
           - Testing Priority: Medium

        3. **WebKit** (Safari):
           - Engine: WebKit + JavaScriptCore
           - Market Share: ~20%
           - Features: Limited File System Access
           - Testing Priority: High (iOS dominance)

        **Configuration**:
        ```typescript
        // playwright.config.ts
        export default defineConfig({
          projects: [
            {
              name: 'chromium',
              use: { ...devices['Desktop Chrome'] },
            },
            {
              name: 'firefox',
              use: { ...devices['Desktop Firefox'] },
            },
            {
              name: 'webkit',
              use: { ...devices['Desktop Safari'] },
            },
            // Mobile browsers
            {
              name: 'mobile-chrome',
              use: { ...devices['Pixel 5'] },
            },
            {
              name: 'mobile-safari',
              use: { ...devices['iPhone 13'] },
            },
          ],
        });
        ```
      </browser_coverage>

      <browser_specific_testing>
        **File System Access API Compatibility**:
        ```typescript
        test.describe('Directory selection - Browser compatibility', () => {
          test('Chromium - File System Access API', async ({ page, browserName }) => {
            test.skip(browserName !== 'chromium', 'File System Access API Chromium-only');

            await page.goto('/playground');

            // Verify API availability
            const hasAPI = await page.evaluate(() => 'showDirectoryPicker' in window);
            expect(hasAPI).toBeTruthy();

            // Test Chromium-specific path
          });

          test('Firefox/WebKit - Fallback to webkitdirectory', async ({ page, browserName }) => {
            test.skip(browserName === 'chromium', 'Testing fallback path');

            await page.goto('/playground');

            // Verify fallback UI
            const fileInput = page.locator('input[type="file"][webkitdirectory]');
            await expect(fileInput).toBeVisible();

            // Test fallback path
          });
        });
        ```

        **CSS and Layout Testing**:
        ```typescript
        test('Responsive layout - All browsers', async ({ page, browserName }) => {
          await page.goto('/');

          // Mobile viewport
          await page.setViewportSize({ width: 375, height: 667 });
          const mobileMenu = page.locator('.mobile-menu-button');
          await expect(mobileMenu).toBeVisible();

          // Desktop viewport
          await page.setViewportSize({ width: 1920, height: 1080 });
          const desktopNav = page.locator('.tab-nav-desktop');
          await expect(desktopNav).toBeVisible();

          console.log(`Layout test passed on ${browserName}`);
        });
        ```

        **JavaScript Compatibility**:
        ```typescript
        test('Modern JavaScript features', async ({ page, browserName }) => {
          await page.goto('/playground');

          const supportsFeatures = await page.evaluate(() => {
            return {
              optionalChaining: true, // a?.b
              nullishCoalescing: true, // a ?? b
              asyncAwait: true,
              promises: typeof Promise !== 'undefined',
              fetch: typeof fetch !== 'undefined',
            };
          });

          expect(supportsFeatures.promises).toBeTruthy();
          expect(supportsFeatures.fetch).toBeTruthy();

          console.log(`${browserName} feature support:`, supportsFeatures);
        });
        ```
      </browser_specific_testing>

      <execution_strategy>
        **Local Development**:
        - Default: Run on Chromium only (fastest)
        - Pre-commit: Run on all browsers for critical changes
        - Command: `npx playwright test --project=chromium`

        **CI/CD**:
        - Run all browser projects in parallel
        - Use sharding for speed: `--shard=1/3`, `--shard=2/3`, `--shard=3/3`
        - Fail fast on first browser failure (optional)

        **Parallel Execution**:
        ```yaml
        # .github/workflows/test.yml
        strategy:
          matrix:
            browser: [chromium, firefox, webkit]
        steps:
          - run: npx playwright test --project=${{ matrix.browser }}
        ```
      </execution_strategy>

      <challenges_and_solutions>
        **Common Cross-Browser Issues**:

        1. **Timing Differences**:
           - Issue: Firefox slower than Chromium
           - Solution: Use waitFor with increased timeout

        2. **Font Rendering**:
           - Issue: Text layout differs slightly
           - Solution: Use flexible assertions (contains vs exact match)

        3. **Feature Detection**:
           - Issue: API availability varies
           - Solution: Test both feature paths (modern + fallback)

        4. **CSS Prefixes**:
           - Issue: Vendor-specific CSS
           - Solution: Use autoprefixer in build process

        5. **Date/Time Formatting**:
           - Issue: Different locale defaults
           - Solution: Explicitly set locale in tests
      </challenges_and_solutions>

      <priority>High</priority>

      <sources>
        - https://playwright.dev/docs/browsers
        - https://thinksys.com/qa-testing/cross-browser-testing-with-playwright/
        - https://github.com/microsoft/playwright
        - https://testrig.medium.com/how-to-run-playwright-tests-across-browsers-and-devices-chromium-firefox-webkit-7809691b7454
      </sources>
    </finding>

    <finding id="8" category="CI/CD">
      <title>GitHub Actions Integration with Playwright</title>
      <description>
        Best practices for integrating Playwright E2E tests into GitHub Actions CI/CD pipeline with parallel execution, artifact management, and optimal performance.
      </description>

      <workflow_configuration>
        **Recommended GitHub Actions Workflow**:
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
            name: Playwright Tests
            timeout-minutes: 60
            runs-on: ubuntu-latest

            strategy:
              fail-fast: false
              matrix:
                shardIndex: [1, 2, 3, 4]
                shardTotal: [4]

            steps:
              - name: Checkout
                uses: actions/checkout@v4

              - name: Setup Node.js
                uses: actions/setup-node@v4
                with:
                  node-version: 20
                  cache: 'npm'

              - name: Install dependencies
                run: npm ci

              - name: Install Playwright browsers
                run: npx playwright install --with-deps

              - name: Build Astro site
                run: npm run build

              - name: Run Playwright tests
                run: npx playwright test --shard=${{ matrix.shardIndex }}/${{ matrix.shardTotal }}

              - name: Upload blob report
                if: always()
                uses: actions/upload-artifact@v4
                with:
                  name: blob-report-${{ matrix.shardIndex }}
                  path: blob-report
                  retention-days: 1

          merge-reports:
            name: Merge Reports
            if: always()
            needs: [test]
            runs-on: ubuntu-latest

            steps:
              - uses: actions/checkout@v4
              - uses: actions/setup-node@v4
                with:
                  node-version: 20

              - name: Download blob reports
                uses: actions/download-artifact@v4
                with:
                  path: all-blob-reports
                  pattern: blob-report-*
                  merge-multiple: true

              - name: Merge into HTML Report
                run: npx playwright merge-reports --reporter html ./all-blob-reports

              - name: Upload HTML report
                uses: actions/upload-artifact@v4
                with:
                  name: playwright-report
                  path: playwright-report
                  retention-days: 30
        ```
      </workflow_configuration>

      <parallel_execution>
        **Sharding Strategy**:
        - 4 shards recommended for medium-sized test suites
        - Each shard runs subset of tests in parallel
        - Even distribution with fullyParallel: true
        - Reduces total CI time by ~75%

        **Configuration**:
        ```typescript
        // playwright.config.ts
        export default defineConfig({
          fullyParallel: true, // Enable parallel execution
          workers: process.env.CI ? 1 : undefined, // 1 worker per shard in CI
          retries: process.env.CI ? 2 : 0, // Retry flaky tests in CI
          reporter: process.env.CI
            ? [['blob'], ['github']] // Blob for merging, GitHub for annotations
            : [['html'], ['list']], // HTML + list for local
        });
        ```

        **Benefits**:
        - Faster feedback (parallel execution)
        - Better resource utilization
        - Scalable to large test suites
        - Cost-effective (less CI time)
      </parallel_execution>

      <artifact_management>
        **Artifacts to Collect**:

        1. **HTML Report**:
           - Test results visualization
           - Retention: 30 days
           - Always upload (even on success)

        2. **Screenshots**:
           - On failure: automatic
           - On success: optional (for visual regression)

        3. **Videos**:
           - On failure: automatic (retain-on-failure)
           - High storage cost - use sparingly

        4. **Traces**:
           - On first retry: trace: 'on-first-retry'
           - Includes network, console, DOM snapshots
           - Best for debugging flaky tests

        5. **Coverage Reports**:
           - Code coverage (if using @playwright/experimental-ct-react)

        **Storage Optimization**:
        ```typescript
        use: {
          screenshot: 'only-on-failure',
          video: 'retain-on-failure',
          trace: 'on-first-retry',
        },
        ```
      </artifact_management>

      <best_practices>
        1. **Fast Feedback**: Run critical tests first (smoke tests)
        2. **Fail Fast**: Use fail-fast: false to see all failures
        3. **Retry Strategy**: 2 retries in CI for network flakiness
        4. **Browser Installation**: Use --with-deps for system dependencies
        5. **Caching**: Cache npm dependencies and Playwright browsers
        6. **Timeout**: Set reasonable timeout (60 minutes for full suite)
        7. **Annotations**: Use GitHub reporter for PR annotations
        8. **Status Checks**: Require Playwright tests to pass for merges
        9. **Scheduled Runs**: Nightly full suite run (all browsers)
        10. **Flaky Test Detection**: Enable failOnFlakyTests in CI

        **Flaky Test Handling**:
        ```typescript
        export default defineConfig({
          failOnFlakyTests: process.env.CI ? true : false,
          retries: 2,
        });
        ```
      </best_practices>

      <integration_with_existing_workflow>
        **Current Workflow** (.github/workflows/deploy.yml):
        - Trigger: Push to main, release/**
        - Jobs: build → deploy
        - Platform: ubuntu-latest, Node.js 20

        **Recommended Changes**:
        1. Add test job before deploy
        2. Deploy only if tests pass
        3. Run tests on pull requests (not just main)

        **Updated Workflow**:
        ```yaml
        jobs:
          test:
            name: Test
            runs-on: ubuntu-latest
            steps:
              - uses: actions/checkout@v4
              - uses: actions/setup-node@v4
                with:
                  node-version: 20
                  cache: npm
              - run: npm ci
              - run: npm run test # Vitest
              - run: npx playwright install --with-deps
              - run: npm run build
              - run: npx playwright test
              - uses: actions/upload-artifact@v4
                if: always()
                with:
                  name: playwright-report
                  path: playwright-report

          build:
            name: Build
            needs: [test] # Only build if tests pass
            runs-on: ubuntu-latest
            # ... existing build steps

          deploy:
            name: Deploy
            needs: [build]
            # ... existing deploy steps
        ```
      </integration_with_existing_workflow>

      <priority>High</priority>

      <sources>
        - https://playwright.dev/docs/ci-intro
        - https://playwright.dev/docs/test-sharding
        - https://www.browsercat.com/post/playwright-github-actions-cicd-guide
        - https://testrig.medium.com/integrating-playwright-with-ci-cd-pipelines-github-actions-gitlab-ci-and-jenkins-8033faf342bd
        - https://dzone.com/articles/seamless-ci-cd-integration-playwright-and-github-actions
      </sources>
    </finding>

    <finding id="9" category="Test Data">
      <title>Test Data and Fixtures Strategy</title>
      <description>
        Comprehensive approach to managing test data, fixtures, and synthetic C++ test projects for reliable and maintainable E2E testing.
      </description>

      <fixture_architecture>
        **Playwright Fixtures Overview**:
        - On-demand setup/teardown
        - Composable and reusable
        - Type-safe with TypeScript
        - Worker-scoped or test-scoped
        - Automatic cleanup

        **Custom Fixture Implementation**:
        ```typescript
        // tests/fixtures/index.ts
        import { test as base, expect } from '@playwright/test';
        import type { Page } from '@playwright/test';

        type TestFixtures = {
          playgroundPage: Page;
          testProject: {
            name: string;
            files: Map<string, string>;
            size: 'small' | 'medium' | 'large';
          };
        };

        export const test = base.extend<TestFixtures>({
          playgroundPage: async ({ page }, use) => {
            await page.goto('/playground');
            await page.waitForLoadState('networkidle');
            await use(page);
          },

          testProject: async ({}, use, testInfo) => {
            const project = {
              name: 'test-project',
              files: new Map([
                ['main.cpp', 'int main() { return 0; }'],
                ['utils.h', '#pragma once\nvoid helper();'],
                ['utils.cpp', '#include "utils.h"\nvoid helper() {}'],
              ]),
              size: 'small' as const,
            };

            await use(project);

            // Cleanup if needed
          },
        });

        export { expect };
        ```

        **Usage**:
        ```typescript
        import { test, expect } from './fixtures';

        test('Transpile small project', async ({ playgroundPage, testProject }) => {
          // Page already navigated to /playground
          // testProject ready to use

          await expect(playgroundPage.getByText('Select Directory')).toBeVisible();
        });
        ```
      </fixture_architecture>

      <synthetic_test_projects>
        **Test Project Structure**:
        ```
        tests/fixtures/test-projects/
        ├── small-project/           # 3-5 files, ~200 LOC
        │   ├── main.cpp
        │   ├── utils.h
        │   └── utils.cpp
        ├── medium-project/          # 10-20 files, ~1000 LOC
        │   ├── src/
        │   │   ├── main.cpp
        │   │   ├── calculator.cpp
        │   │   └── calculator.h
        │   └── include/
        │       └── common.h
        ├── large-project/           # 50-100 files, ~5000 LOC
        │   ├── src/
        │   ├── include/
        │   └── tests/
        ├── edge-cases/
        │   ├── empty-files/
        │   ├── unicode-names/
        │   ├── deep-nesting/
        │   └── mixed-extensions/
        └── error-cases/
            ├── syntax-errors/
            ├── invalid-cpp/
            └── unsupported-features/
        ```

        **Project Characteristics**:

        1. **Small Project** (Quick smoke tests):
           - 3 files: main.cpp, utils.h, utils.cpp
           - Basic C++ features (functions, headers)
           - Expected transpile time: < 2 seconds

        2. **Medium Project** (Realistic scenario):
           - 15 files: multiple directories
           - Classes, namespaces, includes
           - Expected transpile time: < 5 seconds

        3. **Large Project** (Stress test):
           - 75 files: complex directory structure
           - Templates, inheritance, STL usage
           - Expected transpile time: < 60 seconds

        4. **Edge Cases**:
           - Empty files
           - Unicode filenames (测试.cpp)
           - Deep directory nesting (10+ levels)
           - Mixed extensions (.cpp, .cc, .cxx, .hpp, .hxx)

        5. **Error Cases**:
           - Syntax errors (missing semicolons)
           - Invalid C++ (unrecognized keywords)
           - Unsupported features (concepts, modules)

        **Expected Outputs**:
        ```typescript
        // tests/fixtures/expected-outputs/small-project.ts
        export const expectedOutputs = {
          'main.c': '/* Transpiled from main.cpp */\nint main() { return 0; }',
          'utils.c': '/* Transpiled from utils.cpp */\n#include "utils.h"\nvoid helper() {}',
          'utils.h': '#pragma once\nvoid helper();', // Headers unchanged
        };
        ```
      </synthetic_test_projects>

      <data_management_patterns>
        **1. JSON Test Data**:
        ```typescript
        // tests/data/test-cases.json
        {
          "transpilation_scenarios": [
            {
              "name": "Simple main function",
              "input": "int main() { return 0; }",
              "expectedOutput": "int main() { return 0; }",
              "shouldSucceed": true
            },
            {
              "name": "Class definition",
              "input": "class MyClass { public: void method(); };",
              "expectedOutput": "/* Class transpiled to struct */",
              "shouldSucceed": true
            }
          ]
        }
        ```

        **2. Dynamic Test Generation**:
        ```typescript
        import testCases from './data/test-cases.json';

        for (const testCase of testCases.transpilation_scenarios) {
          test(testCase.name, async ({ request }) => {
            const response = await request.post('/api/transpile', {
              data: { code: testCase.input },
            });

            const result = await response.json();
            expect(result.success).toBe(testCase.shouldSucceed);
          });
        }
        ```

        **3. Faker for Realistic Data** (if needed):
        ```typescript
        import { faker } from '@faker-js/faker';

        test.beforeEach(async ({ page }) => {
          const projectName = faker.system.fileName();
          const fileContent = faker.lorem.paragraphs(3);
          // Use for testing UI with varied data
        });
        ```

        **4. Worker-Scoped Fixtures** (Expensive setup):
        ```typescript
        export const test = base.extend<{}, { largeTestProject: TestProject }>({
          largeTestProject: [async ({}, use) => {
            // Setup once per worker (expensive)
            const project = await generateLargeProject();
            await use(project);
            // Cleanup once per worker
          }, { scope: 'worker' }],
        });
        ```
      </data_management_patterns>

      <best_practices>
        1. **Version Control**: Commit test data to repository
        2. **Minimal Data**: Use smallest data needed for test
        3. **Realistic Data**: Mirror production scenarios
        4. **Isolation**: Each test manages own data
        5. **Cleanup**: Automatic cleanup with fixtures
        6. **Documentation**: Comment test data purpose
        7. **Reusability**: Share fixtures across tests
        8. **Type Safety**: Use TypeScript interfaces
        9. **Validation**: Validate test data structure
        10. **Separation**: Keep test data separate from test logic
      </best_practices>

      <priority>High</priority>

      <sources>
        - https://playwright.dev/docs/test-fixtures
        - https://www.checklyhq.com/blog/how-to-implement-custom-test-fixtures-in-playwright/
        - https://www.semantive.com/blog/best-practices-for-using-playwright-fixtures-in-end-to-end-testing
        - https://medium.com/@divyakandpal93/managing-test-data-in-playwright-fixtures-json-and-dynamic-values-f69934cdbb3e
      </sources>
    </finding>

    <finding id="10" category="Implementation">
      <title>Recommended Testing Scope and Priorities</title>
      <description>
        Pragmatic test coverage plan prioritizing high-value tests over exhaustive coverage, balancing maintenance burden with quality assurance.
      </description>

      <critical_flows>
        **Priority 1: Critical User Journeys** (Must Have):

        1. **Homepage Navigation** (Complexity: Low):
           - Load homepage successfully
           - Navigate to all main sections (Playground, Features, Docs)
           - Mobile navigation (hamburger menu) - ✅ Already implemented
           - Footer links functional
           - Expected duration: 5 minutes

        2. **Documentation Access** (Complexity: Low):
           - Load documentation page
           - Navigation between doc sections
           - Code examples render correctly
           - Search functionality (if exists)
           - Expected duration: 10 minutes

        3. **Features Page Display** (Complexity: Low):
           - Load features page
           - All feature cards visible
           - Links functional
           - Responsive layout
           - Expected duration: 5 minutes

        4. **API Endpoints** (Complexity: Medium):
           - POST /api/transpile with valid code
           - POST /api/transpile with invalid code
           - POST /api/validate endpoint
           - Error handling and response format
           - Rate limiting (if exists)
           - Expected duration: 20 minutes

        5. **Playground - Mocked Path** (Complexity: High):
           - Load playground page
           - Mock File System Access API with fsa-mock
           - Select directory (mocked)
           - Transpile project (mocked file system)
           - Display progress correctly
           - Show errors appropriately
           - Download ZIP (verify blob creation)
           - Expected duration: 40 minutes
      </critical_flows>

      <page_coverage>
        **All Pages** (11 pages identified):

        | Page | Path | Priority | Test Complexity | Notes |
        |------|------|----------|----------------|-------|
        | Homepage | / | Critical | Low | Entry point, navigation hub |
        | Playground | /playground | Critical | High | Core functionality, File System API |
        | Features | /features | High | Low | Marketing content |
        | Documentation | /docs | High | Medium | User guides, code examples |
        | Architecture | /architecture | Medium | Low | Technical diagrams |
        | Getting Started | /getting-started | High | Medium | Onboarding flow |
        | Examples | /examples | Medium | Medium | Code samples |
        | Benchmarks | /benchmarks | Low | Low | Performance data |
        | Metrics | /metrics | Low | Low | Analytics display |
        | FAQ | /faq | Medium | Low | Common questions |
        | About | /about | Low | Low | Project information |

        **API Endpoints** (3 identified):
        - /api/transpile (POST) - Critical
        - /api/validate (POST) - High
        - /api/__test-transpile - Low (test endpoint)
      </page_coverage>

      <test_coverage_plan>
        **Phase 1: Foundation** (Week 1) - 60% value, 20% effort:
        1. Homepage navigation (5 tests)
        2. Features page (3 tests)
        3. Docs page (5 tests)
        4. API endpoints (8 tests)
        5. Basic accessibility (5 tests per page = 55 tests)
        6. Mobile responsiveness (existing + 5 more)
        Total: ~80 tests

        **Phase 2: Playground** (Week 2) - 30% value, 60% effort:
        1. Playground UI (10 tests)
        2. Mocked File System Access (15 tests)
        3. Transpilation workflow (10 tests)
        4. Error handling (8 tests)
        5. Progress indicators (5 tests)
        6. Download functionality (5 tests)
        Total: ~50 tests

        **Phase 3: Quality** (Week 3) - 10% value, 20% effort:
        1. Performance tests (8 tests)
        2. Cross-browser (run existing on Firefox/WebKit)
        3. Visual regression (5 key pages)
        4. Advanced accessibility (10 tests)
        5. Edge cases (10 tests)
        Total: ~30 tests

        **Total: ~160 E2E tests** (estimated)
      </test_coverage_plan>

      <maintenance_strategy>
        **Sustainable Testing**:
        - **Target**: 90% critical flow coverage (not 100% code coverage)
        - **Speed**: Full suite < 10 minutes (with sharding)
        - **Reliability**: < 1% flaky test rate
        - **Maintenance**: < 10% tests modified per feature change

        **Test Organization**:
        ```
        tests/
        ├── e2e/
        │   ├── critical/        # Must-pass tests (smoke tests)
        │   │   ├── homepage.spec.ts
        │   │   ├── api.spec.ts
        │   │   └── navigation.spec.ts
        │   ├── features/        # Feature-specific tests
        │   │   ├── features-page.spec.ts
        │   │   ├── docs-page.spec.ts
        │   │   └── examples-page.spec.ts
        │   └── playground/      # Playground tests
        │       ├── mocked/
        │       └── integration/
        ├── accessibility/       # WCAG compliance
        │   └── wcag-aa.spec.ts
        ├── performance/         # Core Web Vitals
        │   └── vitals.spec.ts
        └── visual/              # Visual regression
            └── screenshots.spec.ts
        ```

        **CI/CD Strategy**:
        - **PR**: Run critical tests only (~30 tests, 2 minutes)
        - **Main**: Run all tests (160 tests, 8 minutes with sharding)
        - **Nightly**: Full suite + all browsers (30 minutes)
        - **Release**: Full suite + performance + visual
      </maintenance_strategy>

      <priority>Critical</priority>
    </finding>
  </findings>

  <technical_approach>
    <configuration>
      <playwright_config>
        **Recommended playwright.config.ts**:
        ```typescript
        import { defineConfig, devices } from '@playwright/test';

        export default defineConfig({
          testDir: './tests',
          fullyParallel: true,
          forbidOnly: !!process.env.CI,
          retries: process.env.CI ? 2 : 0,
          workers: process.env.CI ? 1 : undefined,

          reporter: process.env.CI
            ? [['blob'], ['github']]
            : [['html'], ['list']],

          use: {
            baseURL: 'http://localhost:4321',
            trace: 'on-first-retry',
            screenshot: 'only-on-failure',
            video: 'retain-on-failure',
          },

          projects: [
            {
              name: 'chromium',
              use: { ...devices['Desktop Chrome'] },
            },
            {
              name: 'firefox',
              use: { ...devices['Desktop Firefox'] },
            },
            {
              name: 'webkit',
              use: { ...devices['Desktop Safari'] },
            },
            {
              name: 'chromium-headed',
              use: {
                ...devices['Desktop Chrome'],
                headless: false,
                channel: 'chrome',
                launchOptions: {
                  slowMo: 500,
                },
              },
              testMatch: /.*\.headed\.spec\.ts/,
            },
            {
              name: 'mobile-chrome',
              use: { ...devices['Pixel 5'] },
            },
            {
              name: 'mobile-safari',
              use: { ...devices['iPhone 13'] },
            },
          ],

          webServer: {
            command: 'npm run preview',
            port: 4321,
            reuseExistingServer: !process.env.CI,
            timeout: 120000,
          },
        });
        ```
      </playwright_config>

      <typescript_setup>
        **TypeScript Configuration**:
        - Use existing tsconfig.json
        - Playwright types auto-detected from @playwright/test
        - Custom fixtures with type safety
        - Test-specific types in tests/types.ts

        **Example Custom Types**:
        ```typescript
        // tests/types.ts
        export interface TestProject {
          name: string;
          files: Map<string, string>;
          size: 'small' | 'medium' | 'large';
          expectedOutputs?: Map<string, string>;
        }

        export interface TranspileResult {
          success: boolean;
          cCode?: string;
          error?: string;
          warnings?: string[];
        }
        ```
      </typescript_setup>

      <test_organization>
        **Directory Structure**:
        ```
        website/
        ├── tests/
        │   ├── e2e/
        │   │   ├── critical/
        │   │   ├── features/
        │   │   └── playground/
        │   ├── accessibility/
        │   ├── performance/
        │   ├── visual/
        │   ├── fixtures/
        │   │   ├── index.ts
        │   │   ├── test-projects/
        │   │   └── expected-outputs/
        │   ├── helpers/
        │   │   ├── mock-filesystem.ts
        │   │   ├── assertions.ts
        │   │   └── setup.ts
        │   └── types.ts
        ├── playwright.config.ts
        └── package.json
        ```
      </test_organization>
    </configuration>

    <mocking_strategy>
      <file_system_access>
        **Mock Implementation with fsa-mock**:
        ```typescript
        // tests/helpers/mock-filesystem.ts
        import { test as base } from '@playwright/test';

        export const test = base.extend({
          page: async ({ page }, use) => {
            // Inject File System Access API mock
            await page.addInitScript(() => {
              // Mock showDirectoryPicker
              (window as any).showDirectoryPicker = async () => {
                // Return mock FileSystemDirectoryHandle
                return {
                  kind: 'directory',
                  name: 'test-project',
                  async getFileHandle(name: string) {
                    return {
                      kind: 'file',
                      name,
                      async getFile() {
                        return new File(['mock content'], name);
                      },
                    };
                  },
                  async *values() {
                    yield { kind: 'file', name: 'main.cpp' };
                    yield { kind: 'file', name: 'utils.h' };
                  },
                };
              };
            });

            await use(page);
          },
        });
        ```

        **Usage**:
        ```typescript
        import { test, expect } from '../helpers/mock-filesystem';

        test('Select directory with mocked API', async ({ page }) => {
          await page.goto('/playground');
          await page.getByRole('button', { name: 'Select Directory' }).click();

          // Mock automatically returns test-project
          await expect(page.getByText('test-project')).toBeVisible();
        });
        ```
      </file_system_access>

      <backend_api>
        **API Mocking with Playwright**:
        ```typescript
        test('Mock API transpile endpoint', async ({ page }) => {
          await page.route('/api/transpile', async (route) => {
            const request = route.request();
            const postData = request.postDataJSON();

            // Mock successful response
            await route.fulfill({
              status: 200,
              contentType: 'application/json',
              body: JSON.stringify({
                success: true,
                cCode: '/* Transpiled C code */',
              }),
            });
          });

          await page.goto('/playground');
          // Interact with UI - API calls will be mocked
        });
        ```
      </backend_api>

      <browser_features>
        **Feature Detection Mocking**:
        ```typescript
        test('Mock browser feature detection', async ({ page }) => {
          await page.addInitScript(() => {
            // Force specific browser tier
            Object.defineProperty(window, 'showDirectoryPicker', {
              value: undefined, // Simulate unsupported browser
              writable: false,
            });
          });

          await page.goto('/playground');

          // Should show fallback UI
          await expect(page.getByText('Limited support')).toBeVisible();
        });
        ```
      </browser_features>
    </mocking_strategy>

    <test_data>
      <synthetic_projects>
        **Small Project Structure**:
        ```
        tests/fixtures/test-projects/small-project/
        ├── main.cpp          # 10 lines
        ├── utils.h           # 5 lines
        └── utils.cpp         # 8 lines
        ```

        **Project Generator**:
        ```typescript
        // tests/helpers/project-generator.ts
        export function generateTestProject(size: 'small' | 'medium' | 'large') {
          const files = new Map<string, string>();

          if (size === 'small') {
            files.set('main.cpp', 'int main() { return 0; }');
            files.set('utils.h', '#pragma once\nvoid helper();');
            files.set('utils.cpp', '#include "utils.h"\nvoid helper() {}');
          } else if (size === 'medium') {
            // Generate 15 files...
          } else {
            // Generate 75 files...
          }

          return { name: `${size}-project`, files, size };
        }
        ```
      </synthetic_projects>

      <fixtures>
        **Reusable Fixtures**:
        ```typescript
        // tests/fixtures/index.ts
        export const test = base.extend<{
          playgroundPage: Page;
          smallProject: TestProject;
          mediumProject: TestProject;
          largeProject: TestProject;
        }>({
          playgroundPage: async ({ page }, use) => {
            await page.goto('/playground');
            await use(page);
          },

          smallProject: async ({}, use) => {
            await use(generateTestProject('small'));
          },

          mediumProject: async ({}, use) => {
            await use(generateTestProject('medium'));
          },

          largeProject: async ({}, use) => {
            await use(generateTestProject('large'));
          },
        });
        ```
      </fixtures>
    </test_data>
  </technical_approach>

  <tools_and_libraries>
    <playwright_plugins>
      **Recommended Plugins**:

      1. **@axe-core/playwright** (Accessibility):
         - Purpose: WCAG compliance testing
         - Installation: `npm install -D @axe-core/playwright`
         - Priority: High

      2. **playwright-lighthouse** (Performance):
         - Purpose: Lighthouse audits in Playwright
         - Installation: `npm install -D playwright-lighthouse`
         - Priority: Medium

      3. **@playwright/experimental-ct-react** (Component Testing):
         - Purpose: Isolated React component testing
         - Installation: `npm install -D @playwright/experimental-ct-react`
         - Priority: Low (already using Vitest)

      4. **fsa-mock** (File System Access API Mocking):
         - Purpose: Mock File System Access API
         - Installation: `npm install -D fsa-mock`
         - Priority: Critical (for playground tests)
    </playwright_plugins>

    <testing_utilities>
      **Additional Tools**:

      1. **@faker-js/faker** (Test Data Generation):
         - Purpose: Generate realistic test data
         - Priority: Low (minimal need for random data)

      2. **pixelmatch** (Visual Regression):
         - Purpose: Pixel-by-pixel screenshot comparison
         - Installation: `npm install -D pixelmatch`
         - Priority: Medium

      3. **playwright-docker** (Containerized Testing):
         - Purpose: Consistent test environment
         - Priority: Low (GitHub Actions sufficient)
    </testing_utilities>

    <reporting_tools>
      **Test Reporters**:

      1. **HTML Reporter** (Built-in):
         - Best for: Local development
         - Configuration: `reporter: 'html'`

      2. **GitHub Reporter** (Built-in):
         - Best for: CI/CD with GitHub Actions
         - Shows test failures as PR annotations
         - Configuration: `reporter: 'github'`

      3. **Blob Reporter** (Built-in):
         - Best for: Sharded tests in CI
         - Merge multiple shard reports
         - Configuration: `reporter: 'blob'`

      4. **Allure Reporter** (Third-party):
         - Installation: `npm install -D allure-playwright`
         - Best for: Enterprise reporting needs
         - Priority: Low (HTML reporter sufficient)
    </reporting_tools>
  </tools_and_libraries>

  <challenges>
    <challenge id="1">
      <description>File System Access API requires headed browser mode and cannot be fully automated</description>
      <impact>High</impact>
      <affected_areas>
        - Playground directory selection
        - End-to-end workflow testing
        - CI/CD automation
      </affected_areas>
      <mitigation>
        **Primary Strategy**: Use fsa-mock library to mock File System Access API for automated tests

        **Implementation**:
        1. Install fsa-mock: `npm install -D fsa-mock`
        2. Create mock initialization script in tests/helpers/mock-filesystem.ts
        3. Inject mock via page.addInitScript() in test setup
        4. Create realistic mock directory structure matching test projects
        5. Test all playground logic with mocked API

        **Secondary Strategy**: Manual integration testing
        1. Create separate test suite with @manual tag
        2. Run in headed mode locally before releases
        3. Document manual steps required
        4. Use for smoke testing only (not CI)

        **Tertiary Strategy**: Test fallback path
        1. Test webkitdirectory input path (fully automatable)
        2. Verify graceful degradation
        3. Ensure Firefox/Safari compatibility

        **Success Criteria**:
        - 80% of playground tests automated with mocks
        - 15% manual integration tests
        - 5% fallback path tests
      </mitigation>
      <priority>Critical</priority>
    </challenge>

    <challenge id="2">
      <description>React hydration timing in Astro SSG - components may not be immediately interactive</description>
      <impact>Medium</impact>
      <affected_areas>
        - Playground page (PlaygroundController React component)
        - Interactive UI elements
        - Client-side state management
      </affected_areas>
      <mitigation>
        **Strategy**: Add explicit hydration checks before interaction

        **Implementation**:
        ```typescript
        test('Wait for React hydration', async ({ page }) => {
          await page.goto('/playground');

          // Option 1: Wait for data attribute
          await page.waitForSelector('[data-hydrated="true"]');

          // Option 2: Wait for network idle
          await page.waitForLoadState('networkidle');

          // Option 3: Wait for specific interactive element
          await page.waitForSelector('button:not([disabled])');

          // Now safe to interact
          await page.getByRole('button', { name: 'Select Directory' }).click();
        });
        ```

        **Code Change** (Optional):
        Add data-hydrated attribute to React components:
        ```tsx
        useEffect(() => {
          document.querySelector('.playground-container')
            ?.setAttribute('data-hydrated', 'true');
        }, []);
        ```
      </mitigation>
      <priority>Medium</priority>
    </challenge>

    <challenge id="3">
      <description>GitHub Pages base path (/cpp-to-c-website) must match in test configuration</description>
      <impact>Low</impact>
      <affected_areas>
        - Navigation links
        - Asset loading
        - API endpoints
      </affected_areas>
      <mitigation>
        **Strategy**: Configure baseURL to match deployment environment

        **Implementation**:
        ```typescript
        // playwright.config.ts
        export default defineConfig({
          use: {
            // Local preview matches production base path
            baseURL: process.env.CI
              ? 'http://localhost:4321/cpp-to-c-website'
              : 'http://localhost:4321/cpp-to-c-website',
          },
        });
        ```

        **Astro Config**:
        Ensure astro.config.mjs has correct base:
        ```javascript
        export default defineConfig({
          base: '/cpp-to-c-website',
          // ...
        });
        ```
      </mitigation>
      <priority>Low</priority>
    </challenge>

    <challenge id="4">
      <description>Test execution time with large test suite</description>
      <impact>Medium</impact>
      <affected_areas>
        - CI/CD pipeline duration
        - Developer feedback loop
        - Resource costs
      </affected_areas>
      <mitigation>
        **Strategy**: Implement test sharding and selective execution

        **Implementation**:
        1. Use sharding in CI (4 shards recommended):
           ```yaml
           strategy:
             matrix:
               shardIndex: [1, 2, 3, 4]
               shardTotal: [4]
           ```

        2. Tag tests for selective execution:
           ```typescript
           test('Homepage loads', { tag: '@smoke' }, async ({ page }) => {
             // Critical test
           });
           ```

        3. Run smoke tests on PR, full suite on main:
           ```bash
           # PR
           npx playwright test --grep @smoke

           # Main
           npx playwright test
           ```

        4. Parallel execution:
           ```typescript
           fullyParallel: true,
           workers: process.env.CI ? 1 : 4,
           ```

        **Expected Performance**:
        - Smoke tests (30 tests): 2 minutes
        - Full suite (160 tests): 8 minutes (with sharding)
        - Full suite + all browsers: 15 minutes
      </mitigation>
      <priority>Medium</priority>
    </challenge>

    <challenge id="5">
      <description>Flaky tests due to network timing, animations, or async operations</description>
      <impact>Medium</impact>
      <affected_areas>
        - CI reliability
        - Developer confidence
        - Test maintenance burden
      </affected_areas>
      <mitigation>
        **Strategy**: Implement robust waiting strategies and retry logic

        **Best Practices**:
        1. Use built-in assertions with auto-waiting:
           ```typescript
           // ✅ Good - auto-waits
           await expect(page.getByText('Success')).toBeVisible();

           // ❌ Bad - no waiting
           expect(await page.getByText('Success').isVisible()).toBe(true);
           ```

        2. Configure retries in CI:
           ```typescript
           retries: process.env.CI ? 2 : 0,
           ```

        3. Enable flaky test detection:
           ```typescript
           failOnFlakyTests: process.env.CI ? true : false,
           ```

        4. Avoid arbitrary timeouts:
           ```typescript
           // ❌ Bad
           await page.waitForTimeout(5000);

           // ✅ Good
           await page.waitForSelector('.result', { state: 'visible' });
           ```

        5. Handle animations:
           ```typescript
           await page.getByRole('button').click();
           await page.waitForLoadState('networkidle');
           await expect(page.getByText('Result')).toBeVisible();
           ```
      </mitigation>
      <priority>High</priority>
    </challenge>
  </challenges>

  <recommendations>
    <immediate>
      **Actions for Week 1** (Foundation Setup):

      1. **Update playwright.config.ts**:
         - Add Firefox and WebKit projects
         - Configure webServer for Astro preview
         - Set up proper baseURL with base path
         - Enable blob reporter for CI
         - Estimated time: 30 minutes

      2. **Install Dependencies**:
         ```bash
         npm install -D @axe-core/playwright fsa-mock
         ```
         - Estimated time: 5 minutes

      3. **Create Fixture Structure**:
         - Create tests/fixtures/ directory
         - Create tests/helpers/ directory
         - Set up basic custom fixtures (playgroundPage, testProject)
         - Estimated time: 1 hour

      4. **Implement Critical Tests**:
         - Homepage navigation (5 tests)
         - API endpoint tests (8 tests)
         - Basic accessibility tests (10 tests)
         - Estimated time: 4 hours

      5. **Create Test Projects**:
         - Small project (3 files)
         - Expected outputs
         - Mock filesystem helper
         - Estimated time: 2 hours

      **Total Week 1 Effort**: ~8 hours
      **Deliverable**: 23 new tests, fixtures infrastructure
    </immediate>

    <short_term>
      **Actions for Weeks 2-3** (Expand Coverage):

      1. **Page Coverage**:
         - Features page tests (3 tests)
         - Docs page tests (5 tests)
         - Getting Started page (5 tests)
         - Examples page (3 tests)
         - Estimated time: 6 hours

      2. **Playground Testing**:
         - Mock File System Access API (3 hours setup)
         - Directory selection tests (5 tests)
         - Transpilation workflow (10 tests)
         - Error handling (8 tests)
         - Progress indicators (5 tests)
         - Download functionality (5 tests)
         - Estimated time: 12 hours

      3. **Accessibility Suite**:
         - WCAG 2.1 AA tests for all pages (30 tests)
         - Keyboard navigation (10 tests)
         - Focus management (5 tests)
         - Estimated time: 8 hours

      4. **CI/CD Integration**:
         - Create .github/workflows/playwright.yml
         - Configure sharding (4 shards)
         - Set up artifact upload
         - Add test job to deploy workflow
         - Estimated time: 3 hours

      **Total Weeks 2-3 Effort**: ~29 hours
      **Deliverable**: ~110 additional tests, CI integration
    </short_term>

    <long_term>
      **Actions for Month 2+** (Quality & Optimization):

      1. **Performance Testing**:
         - Core Web Vitals tests (8 tests)
         - Lighthouse integration (5 pages)
         - API performance benchmarks (5 tests)
         - Estimated time: 6 hours

      2. **Visual Regression**:
         - Screenshot baseline for 5 key pages
         - Comparison logic
         - CI integration for visual changes
         - Estimated time: 4 hours

      3. **Cross-Browser Refinement**:
         - Fix Firefox/WebKit-specific issues
         - Browser-specific tests (10 tests)
         - Mobile testing (10 tests)
         - Estimated time: 6 hours

      4. **Test Maintenance**:
         - Refactor flaky tests
         - Optimize slow tests
         - Improve test documentation
         - Create contribution guide
         - Estimated time: 4 hours

      5. **Advanced Features**:
         - Test data factory functions
         - Custom assertions library
         - Page object model (if needed)
         - Estimated time: 6 hours

      **Total Month 2+ Effort**: ~26 hours
      **Deliverable**: Performance suite, visual regression, documentation
    </long_term>

    <total_investment>
      **Summary**:
      - Week 1 (Foundation): 8 hours → 23 tests
      - Weeks 2-3 (Coverage): 29 hours → 110 tests
      - Month 2+ (Quality): 26 hours → 30 tests + tooling

      **Total**: ~63 hours → ~163 E2E tests

      **Expected Outcomes**:
      - 90% critical flow coverage
      - WCAG 2.1 AA compliance verification
      - Cross-browser testing (3 engines)
      - CI/CD integration with GitHub Actions
      - Performance monitoring
      - Sustainable test maintenance
    </total_investment>
  </recommendations>

  <resources>
    <documentation>
      **Official Documentation**:
      1. Playwright Docs: https://playwright.dev/docs/intro
      2. Playwright Best Practices: https://playwright.dev/docs/best-practices
      3. Playwright CI: https://playwright.dev/docs/ci-intro
      4. Astro Testing Guide: https://docs.astro.build/en/guides/testing/
      5. File System Access API: https://developer.chrome.com/docs/capabilities/web-apis/file-system-access
      6. WCAG 2.1 Guidelines: https://www.w3.org/WAI/WCAG21/quickref/
      7. Core Web Vitals: https://web.dev/vitals/

      **Playwright GitHub**:
      - Repository: https://github.com/microsoft/playwright
      - Issue #18267 (File System Access): https://github.com/microsoft/playwright/issues/18267
      - Issue #11288 (Native File System): https://github.com/microsoft/playwright/issues/11288
      - Release Notes: https://playwright.dev/docs/release-notes

      **Tutorials and Guides**:
      1. Playwright 1.57 Guide: https://medium.com/@szaranger/playwright-1-57-the-must-use-update-for-web-test-automation-in-2025-b194df6c9e03
      2. Accessibility Testing: https://dev.to/subito/how-we-automate-accessibility-testing-with-playwright-and-axe-3ok5
      3. Performance Testing: https://www.checklyhq.com/docs/learn/playwright/performance/
      4. Custom Fixtures: https://www.checklyhq.com/blog/how-to-implement-custom-test-fixtures-in-playwright/
      5. CI/CD Integration: https://www.browsercat.com/post/playwright-github-actions-cicd-guide
    </documentation>

    <examples>
      **Reference Implementations**:

      1. **Astro + Playwright Example**:
         - Repository: https://github.com/QwikDev/astro
         - File: playwright.config.ts
         - Shows: Astro SSG + Playwright integration

      2. **fsa-mock Library**:
         - Repository: https://github.com/alxcube/fsa-mock
         - Shows: File System Access API mocking

      3. **Playwright Examples (Microsoft)**:
         - Repository: https://github.com/microsoft/playwright/tree/main/examples
         - Shows: Official Playwright patterns

      4. **Accessibility Testing Example**:
         - Guide: https://medium.com/@merisstupar11/achieving-wcag-standard-with-playwright-accessibility-tests-f634b6f9e51d
         - Shows: WCAG 2.1 AA testing with axe-core

      5. **Performance Testing Example**:
         - Guide: https://focusreactive.com/testing-web-application-performance-with-playwright/
         - Shows: Core Web Vitals measurement

      **Similar Projects**:
      1. Frontend Mentor Astro Solution: https://www.frontendmentor.io/solutions/ssr-astro-solution-with-e2e-playwright-tests-and-native-html-forms-QOB2JYeeG6
      2. Next.js + Playwright: https://strapi.io/blog/nextjs-testing-guide-unit-and-e2e-tests-with-vitest-and-playwright
    </examples>

    <community>
      **Community Resources**:
      1. Playwright Discord: https://discord.com/invite/playwright-807756831384403968
      2. Stack Overflow: https://stackoverflow.com/questions/tagged/playwright
      3. Playwright Slack: Via official website

      **Blogs and Articles**:
      1. ThinkSys Playwright Guide 2025: https://thinksys.com/qa-testing/playwright-automation-testing-guide/
      2. Checkly Playwright Docs: https://www.checklyhq.com/docs/learn/playwright/
      3. Semantic Playwright Fixtures: https://www.semantive.com/blog/best-practices-for-using-playwright-fixtures-in-end-to-end-testing
    </community>
  </resources>

  <conclusion>
    <summary>
      This comprehensive research provides a complete roadmap for implementing Playwright E2E testing for the C++ to C Transpiler website with specific focus on HEADED browser mode for File System Access API testing.

      **Key Takeaways**:
      1. Playwright 1.57.0 is already installed - foundation exists
      2. File System Access API testing requires hybrid approach (mocking + manual)
      3. Prioritize high-value tests (critical flows, accessibility, API) over 100% coverage
      4. CI/CD integration with GitHub Actions using sharding for performance
      5. WCAG 2.1 AA compliance achievable with @axe-core/playwright
      6. Estimated 63 hours total effort for comprehensive test suite (~163 tests)

      **Success Metrics**:
      - 90% critical flow coverage (not 100% code coverage)
      - WCAG 2.1 AA compliant (automated + manual verification)
      - < 10 minute test execution (with sharding)
      - < 1% flaky test rate
      - All browsers tested (Chromium, Firefox, WebKit)

      **Next Steps**:
      1. Review and approve this research document
      2. Execute Week 1 immediate actions (8 hours)
      3. Implement foundation tests and fixtures
      4. Integrate into CI/CD pipeline
      5. Expand coverage in Weeks 2-3
      6. Iterate based on learnings
    </summary>

    <confidence_assessment>
      **Confidence Level: High (85%)**

      **Strengths**:
      - Extensive research from official Playwright documentation
      - Multiple verified sources from 2024-2025 timeframe
      - Existing codebase analysis completed
      - Clear technical constraints identified
      - Pragmatic approach with proven patterns

      **Uncertainties** (15%):
      1. File System Access API mocking effectiveness (10%)
         - fsa-mock library exists but integration complexity unknown
         - May require custom implementation for complex scenarios

      2. Astro hydration timing edge cases (3%)
         - React hydration patterns well-documented but edge cases may exist

      3. CI execution time accuracy (2%)
         - Estimates based on typical projects, actual may vary

      **Risk Mitigation**:
      - Start with small proof-of-concept for File System Access API mocking
      - Iterate based on real-world findings
      - Adjust timelines and scope as needed
      - Maintain flexibility in approach
    </confidence_assessment>
  </conclusion>
</research>
```
