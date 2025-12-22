# Playwright E2E Testing Research - Meta-Prompt

<objective>
Research and analyze Playwright E2E testing requirements for the C++ to C transpiler website.

Purpose: Gather comprehensive information for testing strategy with HEADED browser execution
Output: Detailed research findings in XML format
Approach: Investigate existing patterns, best practices, and requirements for headed browser testing

**IMPORTANT**: All tests will run in HEADED mode (with visible browser), not headless. This is critical for:
- File System Access API (requires user interaction)
- Visual verification of UI components
- Interactive debugging capabilities
- Real browser behavior validation
</objective>

<context>
Website project: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/website
Recent work: Completed playground implementation (Phases 1-6)
Technology stack: Astro + React + TypeScript
Existing tests: Vitest unit tests (314 tests, 93.6% passing)
Current pages: index, playground, features, architecture, docs, examples, etc.
</context>

<research_requirements>
Investigate the following areas comprehensively:

## 1. Existing Test Infrastructure
- [ ] Check for existing Playwright configuration
- [ ] Examine current test setup (vitest.config.ts, package.json)
- [ ] Identify existing E2E or integration tests
- [ ] Review test scripts and CI/CD integration
- [ ] Check for test fixtures or helpers

## 2. Playwright Best Practices (2025)
- [ ] Latest Playwright version and features
- [ ] Recommended project structure for E2E tests
- [ ] Configuration best practices (playwright.config.ts)
- [ ] Parallel execution strategies
- [ ] Test isolation and state management
- [ ] Visual regression testing capabilities
- [ ] Accessibility testing with Playwright
- [ ] Mobile/responsive testing approaches

## 3. Website Testing Requirements
- [ ] Identify all pages requiring testing (scan src/pages/)
- [ ] Identify critical user flows:
  - Homepage navigation
  - Playground workflow (directory selection, transpilation, download)
  - Documentation navigation
  - Feature demonstrations
  - Example interactions
- [ ] API testing requirements (/api/transpile, /api/validate)
- [ ] Mobile responsiveness testing needs
- [ ] Browser compatibility testing matrix
- [ ] Performance testing requirements

## 4. Playground-Specific Testing (HEADED BROWSER)
- [ ] File System Access API in headed mode (user interaction required)
- [ ] Real directory selection with showDirectoryPicker()
- [ ] Progress indicator validation with real file processing
- [ ] Error display verification
- [ ] ZIP download testing (actual file download)
- [ ] Backend API integration testing with real server
- [ ] Cancellation workflow testing
- [ ] Test data: Create real temporary C++ project directories for testing

## 5. Technical Integration
- [ ] Astro + Playwright integration patterns
- [ ] React component testing in E2E context
- [ ] TypeScript setup for Playwright
- [ ] Test data management (synthetic C++ projects)
- [ ] Environment variable configuration
- [ ] Base URL and routing considerations
- [ ] SSG vs SSR testing differences

## 6. CI/CD Integration
- [ ] GitHub Actions Playwright integration
- [ ] Test execution in CI environment
- [ ] Artifact storage (screenshots, videos, traces)
- [ ] Parallel execution in CI
- [ ] Browser installation in CI
- [ ] Test reporting and dashboards

## 7. Accessibility Testing
- [ ] Playwright accessibility testing tools
- [ ] WCAG 2.1 AA compliance verification
- [ ] Keyboard navigation testing
- [ ] Screen reader compatibility testing
- [ ] ARIA attribute validation
- [ ] Color contrast checking

## 8. Performance Testing
- [ ] Page load time measurement
- [ ] Core Web Vitals tracking (LCP, FID, CLS)
- [ ] Lighthouse integration
- [ ] Network throttling scenarios
- [ ] Bundle size impact on performance
- [ ] API response time validation

## 9. Test Data Strategy
- [ ] Synthetic C++ test projects (small, medium, large)
- [ ] Expected transpilation outputs
- [ ] Error case test data
- [ ] Edge case scenarios
- [ ] Mock API responses
- [ ] Fixture organization

## 10. Cross-Browser Testing
- [ ] Chromium, Firefox, WebKit support
- [ ] Browser-specific feature testing
- [ ] File System Access API fallbacks
- [ ] Mobile browser testing (if applicable)
- [ ] Browser version matrix
</research_requirements>

<deliverables>
Create a comprehensive research document with the following structure:

```xml
<research>
  <meta>
    <date>YYYY-MM-DD</date>
    <version>1.0</version>
    <confidence>High|Medium|Low</confidence>
  </meta>

  <executive_summary>
    Brief overview of key findings and recommendations
  </executive_summary>

  <findings>
    <finding id="1" category="Infrastructure">
      <title>Current Test Setup Analysis</title>
      <description>Detailed analysis of existing test infrastructure</description>
      <current_state>What exists today</current_state>
      <gaps>What's missing</gaps>
      <recommendations>What should be done</recommendations>
      <priority>Critical|High|Medium|Low</priority>
    </finding>

    <finding id="2" category="Best Practices">
      <title>Playwright 2025 Best Practices</title>
      <description>Latest patterns and recommendations</description>
      <key_practices>
        - Practice 1
        - Practice 2
      </key_practices>
      <code_examples>Relevant snippets</code_examples>
    </finding>

    <!-- Additional findings for each research area -->
  </findings>

  <test_scope>
    <critical_flows>
      <flow id="1">
        <name>Playground Transpilation Workflow</name>
        <steps>Detailed step list</steps>
        <acceptance_criteria>What constitutes success</acceptance_criteria>
        <complexity>High|Medium|Low</complexity>
      </flow>
      <!-- Additional flows -->
    </critical_flows>

    <pages>
      <page path="/" priority="Critical">
        <tests>List of required tests</tests>
      </page>
      <!-- Additional pages -->
    </pages>
  </test_scope>

  <technical_approach>
    <configuration>
      <playwright_config>Recommended playwright.config.ts structure</playwright_config>
      <typescript_setup>Type definitions and tsconfig</typescript_setup>
      <test_organization>Directory structure</test_organization>
    </configuration>

    <mocking_strategy>
      <file_system_access>How to mock File System Access API</file_system_access>
      <backend_api>API mocking approach</backend_api>
      <browser_features>Feature detection mocking</browser_features>
    </mocking_strategy>

    <test_data>
      <synthetic_projects>Structure and content</synthetic_projects>
      <fixtures>Reusable test fixtures</fixtures>
    </test_data>
  </technical_approach>

  <tools_and_libraries>
    <playwright_plugins>Recommended plugins and extensions</playwright_plugins>
    <testing_utilities>Additional tools (faker, test-data-bot, etc.)</testing_utilities>
    <reporting_tools>Test reporters and dashboards</reporting_tools>
  </tools_and_libraries>

  <challenges>
    <challenge id="1">
      <description>File System Access API requires headed browser mode</description>
      <impact>Medium</impact>
      <mitigation>Run all tests in headed mode with headless: false in config</mitigation>
    </challenge>
    <challenge id="2">
      <description>User interaction required for directory picker</description>
      <impact>High</impact>
      <mitigation>Use CDP (Chrome DevTools Protocol) to automate file picker, or create pre-selected test directories</mitigation>
    </challenge>
    <!-- Additional challenges -->
  </challenges>

  <recommendations>
    <immediate>
      - Action 1
      - Action 2
    </immediate>
    <short_term>
      - Action 1
      - Action 2
    </short_term>
    <long_term>
      - Action 1
      - Action 2
    </long_term>
  </recommendations>

  <resources>
    <documentation>
      - Playwright docs
      - Astro testing guides
      - React Testing Library E2E patterns
    </documentation>
    <examples>
      - Similar project examples
      - Reference implementations
    </examples>
  </resources>
</research>
```
</deliverables>

<execution_instructions>
1. **Survey Current State**:
   - Read package.json, vitest.config.ts, tsconfig.json
   - Check for existing Playwright setup
   - Examine test directory structure
   - Review CI/CD configuration (.github/workflows/)

2. **Research Playwright 2025**:
   - Use WebSearch for latest Playwright documentation
   - Search for Astro + Playwright integration guides
   - Find best practices for testing SSG sites
   - Research File System Access API testing strategies

3. **Analyze Website Structure**:
   - List all pages in src/pages/
   - Map out critical user flows
   - Identify interactive components
   - Document API endpoints

4. **Identify Testing Challenges**:
   - File System Access API (non-standard, difficult to mock)
   - React hydration in Astro SSG
   - Backend API integration
   - ZIP download verification
   - Progress indicator timing

5. **Compile Recommendations**:
   - Prioritize test coverage (critical flows first)
   - Suggest pragmatic approach (MVP vs comprehensive)
   - Balance test coverage with maintenance burden
   - Consider CI/CD execution time

6. **Create Deliverable**:
   - Write comprehensive XML research document
   - Include code examples and configurations
   - Provide clear recommendations
   - Document risks and mitigations
</execution_instructions>

<success_criteria>
- [ ] All research areas investigated
- [ ] Current state thoroughly analyzed
- [ ] Playwright best practices documented
- [ ] Critical user flows identified
- [ ] Testing challenges documented with mitigations
- [ ] Technical approach clearly defined
- [ ] Recommendations prioritized (immediate, short-term, long-term)
- [ ] XML research document created
- [ ] High confidence in findings (>80%)
</success_criteria>

<output>
Create the following files in `.prompts/017-playwright-e2e-testing-research/`:
- `playwright-e2e-testing-research.md` - Main research document (XML format)
- `SUMMARY.md` - Executive summary with key findings and recommendations
</output>

<notes>
- Use WebSearch extensively for latest Playwright documentation (2025)
- Examine existing codebase thoroughly before making recommendations
- Be pragmatic - focus on high-value tests, not 100% coverage
- Consider maintenance burden and CI execution time
- File System Access API testing is a known challenge - research workarounds
- Playwright has MCP server integration - check if available
</notes>
