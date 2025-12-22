# Playwright E2E Testing Plan - Meta-Prompt

<objective>
Design comprehensive E2E testing architecture for the C++ to C transpiler website using Playwright in HEADED mode.

Purpose: Create detailed test architecture and implementation plan
Output: Architecture diagrams, test specifications, and execution plan
Approach: Based on research findings, design test suite following best practices
Dependencies: Requires completion of 017-playwright-e2e-testing-research
</objective>

<context>
Research findings: @.prompts/017-playwright-e2e-testing-research/playwright-e2e-testing-research.md
Website project: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/website
Current state: 314 unit tests (93.6% passing), no E2E tests yet
Technology: Astro + React + TypeScript, Playwright for E2E
Mode: HEADED browser execution (headless: false)
</context>

<planning_requirements>
Create a comprehensive test architecture plan covering:

## 1. Test Organization Architecture
Design the directory structure and test organization:
- Where tests should live (tests/e2e/, e2e/, playwright/)
- Test file naming conventions
- Fixture organization
- Page Object Model (POM) structure
- Shared utilities and helpers
- Configuration file organization

## 2. Test Scope Definition
Clearly define what will be tested:

### Critical Path Tests (P0 - Must Have)
- Homepage navigation and hero interactions
- Playground complete workflow (directory → transpile → download)
- API endpoints (/api/transpile, /api/validate)
- Mobile responsive layouts
- Accessibility compliance (WCAG 2.1 AA)

### High Priority Tests (P1 - Should Have)
- All page navigation (docs, features, architecture, etc.)
- Error handling flows
- Browser compatibility (Chrome, Firefox, Safari)
- Progress indicator accuracy
- Error display functionality

### Medium Priority Tests (P2 - Nice to Have)
- Performance benchmarks
- Visual regression testing
- Cross-device testing
- Network resilience (slow 3G, offline)

### Low Priority Tests (P3 - Future)
- Advanced accessibility features
- Internationalization (if applicable)
- Edge case scenarios

## 3. Test Data Strategy
Design test data architecture:
- Synthetic C++ project structures (small, medium, large)
- Expected transpilation outputs
- API mock responses
- Error scenarios
- Edge cases
- Fixture file organization
- Data generation approach (static vs dynamic)

## 4. Configuration Architecture
Design Playwright configuration:
- playwright.config.ts structure
- Browser configurations (Chromium, Firefox, WebKit)
- HEADED mode setup (headless: false)
- Viewport sizes and device emulation
- Timeout configurations
- Retry strategies
- Parallel execution settings
- Base URL configuration
- Environment-specific configs (dev, staging, prod)

## 5. Page Object Model Design
Design POM architecture for maintainability:
- Base page class structure
- Page-specific classes (HomePage, PlaygroundPage, etc.)
- Component wrappers (DirectorySelector, ProgressIndicator, ErrorDisplay)
- Reusable selectors and locators
- Action methods vs assertion methods
- Type-safe page objects with TypeScript

## 6. Headed Browser Workflow
Design headed mode execution strategy:
- Local development execution (with visible browser)
- CI/CD execution (xvfb or headed with video)
- File System Access API automation (CDP or manual interaction)
- Directory picker automation strategies
- Download verification in headed mode
- Screenshot/video capture configuration

## 7. CI/CD Integration Plan
Design GitHub Actions workflow:
- Playwright installation step
- Browser installation
- Test execution (headed mode with xvfb)
- Artifact storage (videos, screenshots, traces)
- Test reporting
- Failure notification
- Parallel execution matrix

## 8. Accessibility Testing Plan
Design a11y testing approach:
- Automated accessibility scans (axe-core integration)
- Keyboard navigation tests
- Screen reader compatibility tests
- Color contrast validation
- ARIA attribute verification
- Focus management testing

## 9. Performance Testing Plan
Design performance validation:
- Page load time thresholds
- Core Web Vitals tracking (LCP, FID, CLS)
- Lighthouse CI integration
- API response time validation
- Bundle size impact measurement

## 10. Maintenance Strategy
Design for long-term maintainability:
- Test isolation principles
- Flake reduction strategies
- Test data refresh approach
- Documentation requirements
- Debugging strategies
- Update and migration plan
</planning_requirements>

<deliverables>
Create a comprehensive planning document with the following structure:

```xml
<test_plan>
  <meta>
    <date>YYYY-MM-DD</date>
    <version>1.0</version>
    <based_on>017-playwright-e2e-testing-research</based_on>
    <execution_mode>Headed Browser (headless: false)</execution_mode>
  </meta>

  <executive_summary>
    Brief overview of test strategy, scope, and priorities
  </executive_summary>

  <architecture>
    <directory_structure>
      ```
      tests/
      ├── e2e/
      │   ├── fixtures/
      │   │   ├── cpp-projects/
      │   │   │   ├── small-project/
      │   │   │   ├── medium-project/
      │   │   │   └── large-project/
      │   │   └── expected-outputs/
      │   ├── pages/
      │   │   ├── BasePage.ts
      │   │   ├── HomePage.ts
      │   │   ├── PlaygroundPage.ts
      │   │   └── components/
      │   │       ├── DirectorySelector.ts
      │   │       ├── ProgressIndicator.ts
      │   │       └── ErrorDisplay.ts
      │   ├── specs/
      │   │   ├── homepage.spec.ts
      │   │   ├── playground.spec.ts
      │   │   ├── navigation.spec.ts
      │   │   ├── accessibility.spec.ts
      │   │   └── api.spec.ts
      │   └── utils/
      │       ├── test-helpers.ts
      │       ├── file-system-helpers.ts
      │       └── api-helpers.ts
      ├── playwright.config.ts
      └── playwright.headed.config.ts (headed-specific overrides)
      ```
    </directory_structure>

    <page_objects>
      <base_page>
        <description>Base class with common functionality</description>
        <methods>
          - navigate(path)
          - waitForLoad()
          - takeScreenshot()
          - checkAccessibility()
        </methods>
      </base_page>

      <playground_page>
        <description>Playground-specific page object</description>
        <components>
          - directorySelector: DirectorySelectorComponent
          - progressIndicator: ProgressIndicatorComponent
          - errorDisplay: ErrorDisplayComponent
        </components>
        <methods>
          - selectDirectory(path)
          - startTranspilation()
          - waitForCompletion()
          - downloadResults()
          - cancelTranspilation()
        </methods>
      </playground_page>
    </page_objects>

    <configuration>
      ```typescript
      // playwright.config.ts excerpt
      export default defineConfig({
        testDir: './tests/e2e',
        fullyParallel: true,
        forbidOnly: !!process.env.CI,
        retries: process.env.CI ? 2 : 0,
        workers: process.env.CI ? 1 : undefined,
        use: {
          baseURL: 'http://localhost:4321',
          headless: false,  // CRITICAL: Headed mode for File System Access API
          trace: 'on-first-retry',
          screenshot: 'only-on-failure',
          video: 'retain-on-failure',
        },
        projects: [
          {
            name: 'chromium',
            use: { ...devices['Desktop Chrome'] },
          },
          // ... more browsers
        ],
      });
      ```
    </configuration>
  </architecture>

  <test_specifications>
    <spec id="1" priority="P0">
      <name>Playground Complete Workflow</name>
      <file>playground.spec.ts</file>
      <description>End-to-end playground transpilation test</description>
      <steps>
        1. Navigate to /playground
        2. Click "Select Directory" button
        3. Select test C++ project directory (via File System Access API)
        4. Verify directory path displayed
        5. Click "Transpile Project"
        6. Verify progress indicator shows 0% → 100%
        7. Verify file count updates (0/N → N/N)
        8. Verify transpilation completes successfully
        9. Verify ZIP download triggered
        10. Verify no errors displayed
      </steps>
      <assertions>
        - Directory path matches selected path
        - Progress reaches 100%
        - Download file is valid ZIP
        - ZIP contains expected .c files
        - Directory structure preserved
      </assertions>
      <test_data>Small C++ project (5 files)</test_data>
      <estimated_duration>30-45 seconds</estimated_duration>
    </spec>

    <spec id="2" priority="P0">
      <name>API Transpilation Endpoint</name>
      <file>api.spec.ts</file>
      <description>Test /api/transpile endpoint</description>
      <steps>
        1. POST to /api/transpile with valid C++ code
        2. Verify 200 status code
        3. Verify response contains cCode field
        4. Verify transpiled code is valid C
        5. Test error handling with invalid C++
        6. Verify timeout handling
      </steps>
    </spec>

    <!-- Additional test specifications for each critical flow -->
  </test_specifications>

  <test_data>
    <synthetic_projects>
      <project name="small-project" size="5 files">
        <files>
          - main.cpp (simple main function)
          - utils.h (header file)
          - utils.cpp (utility functions)
          - math.h (math utilities)
          - math.cpp (math implementations)
        </files>
        <expected_output>
          - main.c
          - utils.h
          - utils.c
          - math.h
          - math.c
        </expected_output>
      </project>

      <project name="medium-project" size="20 files">
        <structure>
          - src/ (10 .cpp files)
          - include/ (10 .h files)
        </structure>
      </project>

      <project name="large-project" size="100 files">
        <structure>Nested directories with realistic C++ project</structure>
      </project>
    </synthetic_projects>

    <error_scenarios>
      - Invalid C++ syntax
      - Empty files
      - Large files (>1MB)
      - Special characters in filenames
      - Very deep directory nesting
    </error_scenarios>
  </test_data>

  <headed_mode_strategy>
    <local_execution>
      <description>Developer running tests locally</description>
      <approach>
        - Run with headless: false (browser visible)
        - Manual directory selection possible
        - Use pre-created test directories in known locations
        - Watch mode for rapid development
      </approach>
    </local_execution>

    <ci_execution>
      <description>GitHub Actions CI/CD</description>
      <approach>
        - Use xvfb for virtual display
        - Headed mode enabled but virtualized
        - Or use Chromium headed with --disable-gpu
        - Record videos for debugging
        - Upload artifacts on failure
      </approach>
      <example>
        ```yaml
        - name: Run Playwright tests
          run: |
            xvfb-run --auto-servernum --server-args="-screen 0 1280x960x24" \
            npm run test:e2e
        ```
      </example>
    </ci_execution>

    <file_picker_automation>
      <approach>CDP (Chrome DevTools Protocol)</approach>
      <description>
        Use CDP to intercept file picker dialogs and provide predefined paths.
        This allows automated testing of File System Access API without manual interaction.
      </description>
      <code_example>
        ```typescript
        // Intercept file picker and provide test directory
        await page.evaluate(async (testDirPath) => {
          const originalShowDirectoryPicker = window.showDirectoryPicker;
          window.showDirectoryPicker = async () => {
            // Return handle to test directory
            return await originalShowDirectoryPicker({ id: 'test', startIn: testDirPath });
          };
        }, TEST_DIR_PATH);
        ```
      </code_example>
    </file_picker_automation>
  </headed_mode_strategy>

  <ci_cd_integration>
    <github_actions>
      <workflow_file>.github/workflows/playwright.yml</workflow_file>
      <steps>
        1. Checkout code
        2. Setup Node.js
        3. Install dependencies
        4. Install Playwright browsers
        5. Build Astro site
        6. Start dev server
        7. Run Playwright tests (headed mode with xvfb)
        8. Upload artifacts (videos, screenshots, traces)
        9. Publish test results
      </steps>
      <parallelization>
        - Matrix strategy for multiple browsers
        - Shard tests across workers
        - 4-8 parallel workers recommended
      </parallelization>
    </github_actions>
  </ci_cd_integration>

  <accessibility_testing>
    <approach>axe-core integration via @axe-core/playwright</approach>
    <tests>
      - Automated accessibility scans on all pages
      - Keyboard navigation (Tab, Enter, Escape)
      - Focus visible indicators
      - ARIA labels present
      - Color contrast meets WCAG AA
      - Screen reader announcements (aria-live)
    </tests>
    <thresholds>
      - 0 violations for critical issues
      - &lt;5 violations for minor issues
      - 100% keyboard accessible
    </thresholds>
  </accessibility_testing>

  <performance_testing>
    <metrics>
      - Page load time &lt; 2s
      - LCP &lt; 2.5s
      - FID &lt; 100ms
      - CLS &lt; 0.1
      - API response time &lt; 500ms
    </metrics>
    <tools>
      - Lighthouse CI
      - Playwright performance API
      - Custom timing measurements
    </tools>
  </performance_testing>

  <maintenance>
    <best_practices>
      - Test isolation (no shared state)
      - Stable locators (data-testid attributes)
      - Reusable page objects
      - Clear test naming
      - Comprehensive assertions
      - Video recording for failures
    </best_practices>

    <debugging>
      - Playwright Inspector (headed mode)
      - Trace viewer for detailed timelines
      - Video recordings
      - Screenshots on failure
      - Console log capture
    </debugging>

    <updates>
      - Keep Playwright updated (monthly)
      - Review and update test data quarterly
      - Refactor flaky tests immediately
      - Document breaking changes
    </updates>
  </maintenance>

  <implementation_phases>
    <phase number="1" priority="Critical">
      <name>Foundation Setup</name>
      <deliverables>
        - Install Playwright
        - Create playwright.config.ts
        - Set up directory structure
        - Create base page object
        - Configure headed mode
        - Create first smoke test
      </deliverables>
      <duration>2-3 hours</duration>
    </phase>

    <phase number="2" priority="Critical">
      <name>Playground Tests</name>
      <deliverables>
        - PlaygroundPage page object
        - Component wrappers
        - Synthetic C++ test projects
        - Complete workflow test
        - Error handling tests
        - API integration tests
      </deliverables>
      <duration>4-6 hours</duration>
    </phase>

    <phase number="3" priority="High">
      <name>Navigation & Content Tests</name>
      <deliverables>
        - HomePage tests
        - Navigation tests
        - Documentation page tests
        - Mobile responsive tests
      </deliverables>
      <duration>3-4 hours</duration>
    </phase>

    <phase number="4" priority="High">
      <name>Accessibility & Performance</name>
      <deliverables>
        - Accessibility test suite
        - Performance benchmarks
        - Lighthouse CI integration
      </deliverables>
      <duration>2-3 hours</duration>
    </phase>

    <phase number="5" priority="Medium">
      <name>CI/CD Integration</name>
      <deliverables>
        - GitHub Actions workflow
        - Artifact upload
        - Test reporting
        - Notification setup
      </deliverables>
      <duration>2-3 hours</duration>
    </phase>
  </implementation_phases>

  <success_criteria>
    <criteria>
      - All P0 tests implemented and passing
      - All P1 tests implemented and passing
      - Test execution time &lt; 5 minutes (local)
      - Test execution time &lt; 10 minutes (CI)
      - 0% flaky tests
      - Headed mode working in both local and CI
      - Documentation complete
      - CI/CD pipeline green
    </criteria>
  </success_criteria>

  <risks_and_mitigations>
    <risk id="1">
      <description>File System Access API automation in CI</description>
      <likelihood>High</likelihood>
      <impact>High</impact>
      <mitigation>Use CDP to automate file picker, or create pre-authorized test directories</mitigation>
    </risk>

    <risk id="2">
      <description>Flaky tests due to timing issues</description>
      <likelihood>Medium</likelihood>
      <impact>Medium</impact>
      <mitigation>Use Playwright auto-waiting, increase timeouts for slow operations, retry failed tests</mitigation>
    </risk>

    <risk id="3">
      <description>Long CI execution time</description>
      <likelihood>Medium</likelihood>
      <impact>Low</impact>
      <mitigation>Parallel execution, test sharding, optimize test suite</mitigation>
    </risk>
  </risks_and_mitigations>
</test_plan>
```

Include 6 Mermaid diagrams:
1. **Test Architecture Diagram** - Overall structure
2. **Page Object Model** - Class hierarchy
3. **Playwright Workflow** - Test execution flow
4. **CI/CD Pipeline** - GitHub Actions workflow
5. **Test Data Flow** - How test data moves through tests
6. **Headed Mode Execution** - Local vs CI execution paths
</deliverables>

<success_criteria>
- [ ] Complete test architecture designed
- [ ] All test specifications documented
- [ ] Page Object Model designed
- [ ] Test data strategy defined
- [ ] CI/CD integration planned
- [ ] Headed mode strategy documented
- [ ] 6 Mermaid diagrams created
- [ ] Implementation phases clearly defined
- [ ] Risks identified with mitigations
- [ ] Based on research findings from Phase 017
</success_criteria>

<output>
Create the following files in `.prompts/018-playwright-e2e-testing-plan/`:
- `playwright-e2e-testing-plan.md` - Complete test plan (XML format with Mermaid diagrams)
- `SUMMARY.md` - Executive summary with architecture overview and implementation roadmap
</output>
