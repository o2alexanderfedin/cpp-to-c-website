# Playwright E2E Testing - Verification Guide

## Quick Verification Checklist

Use this guide to verify the Playwright E2E testing implementation is working correctly.

---

## Pre-Verification Setup

### 1. Install Dependencies

```bash
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/website
npm ci
```

### 2. Install Playwright Browsers

```bash
npx playwright install --with-deps
```

Expected output: Chromium, Firefox, and WebKit browsers installed.

---

## Phase 1 Verification: Foundation Setup

### Check Configuration

```bash
# Verify playwright.config.ts exists and is valid
cat playwright.config.ts | grep "headless: false"
```

Expected: Should see `headless: false` configuration.

### Check Directory Structure

```bash
ls -R tests/e2e/
```

Expected directories:
- tests/e2e/pages/
- tests/e2e/pages/components/
- tests/e2e/specs/
- tests/e2e/fixtures/
- tests/e2e/utils/

### Run Smoke Tests

```bash
npm run test:e2e:chromium -- smoke.spec.ts
```

Expected: 5 tests pass (homepage, playground, features, docs loads).

---

## Phase 2 Verification: Playground Tests

### Check Test Project Exists

```bash
ls -la tests/e2e/fixtures/cpp-projects/small-project/
```

Expected files:
- main.cpp
- utils.h
- utils.cpp
- README.md

### Run Playground Tests

```bash
npm run test:e2e:chromium -- playground.spec.ts
```

Expected: 6 tests pass, 1 skipped (manual test).

### Run API Tests

```bash
npm run test:e2e:chromium -- api.spec.ts
```

Expected: 5 tests pass (API endpoint validation).

---

## Phase 3 Verification: Navigation Tests

### Check Page Objects

```bash
ls -la tests/e2e/pages/
```

Expected files:
- BasePage.ts
- HomePage.ts
- FeaturesPage.ts
- DocsPage.ts
- PlaygroundPage.ts

### Run Navigation Tests

```bash
npm run test:e2e:chromium -- navigation.spec.ts
```

Expected: 5 tests pass (navigation flows).

---

## Phase 4 Verification: Accessibility Tests

### Check axe-core Installation

```bash
npm list @axe-core/playwright
```

Expected: @axe-core/playwright@4.11.0 installed.

### Run Accessibility Tests

```bash
npm run test:e2e:chromium -- accessibility.spec.ts
```

Expected: 7 tests pass (0 accessibility violations).

---

## Phase 5 Verification: CI/CD Integration

### Check GitHub Actions Workflow

```bash
cat .github/workflows/playwright.yml | grep "playwright test"
```

Expected: Workflow file exists with test sharding configuration.

### Verify NPM Scripts

```bash
npm run test:e2e -- --help
```

Expected: Playwright CLI help output.

---

## Full Test Suite Verification

### Run All Tests (Chromium Only)

```bash
npm run test:e2e:chromium
```

Expected Results:
- Smoke tests: 5/5 pass
- Navigation tests: 5/5 pass
- Accessibility tests: 7/7 pass
- Playground tests: 6/7 pass (1 skipped)
- API tests: 5/5 pass
- **Total: ~28/29 pass, 1 skipped**

### Run All Tests (All Browsers)

```bash
npm run test:e2e
```

Expected: Tests run on Chromium, Firefox, and WebKit.

**Note**: This will take longer (~10-15 minutes) as tests run on multiple browsers.

### Run Tests in UI Mode

```bash
npm run test:e2e:ui
```

Expected: Playwright UI opens with test explorer.

---

## Headed Mode Verification

### Run Single Test in Headed Mode

```bash
npm run test:e2e:headed -- smoke.spec.ts
```

Expected: Browser window opens, tests run visibly, browser closes.

### Verify File System Access API Mocking

```bash
npm run test:e2e:chromium -- playground.spec.ts -g "mocked API"
```

Expected: Test with mocked File System Access API passes.

---

## Documentation Verification

### Check Phase Summaries

```bash
ls -la .prompts/019-playwright-e2e-testing-implement/
```

Expected files:
- Phase-1-SUMMARY.md
- Phase-2-SUMMARY.md
- Phase-3-SUMMARY.md
- Phase-4-SUMMARY.md
- Phase-5-SUMMARY.md
- SUMMARY.md
- FILE-INVENTORY.md
- VERIFICATION-GUIDE.md

### Check Test Suite Documentation

```bash
cat tests/e2e/README.md | head -20
```

Expected: Comprehensive README with overview, structure, usage instructions.

---

## TypeScript Compilation Verification

### Check All TypeScript Files Compile

```bash
npx tsc --noEmit tests/e2e/**/*.ts
```

Expected: No compilation errors.

---

## CI/CD Simulation (Local)

### Simulate CI Environment

```bash
# Set CI environment variable
CI=true npm run test:e2e:chromium
```

Expected:
- Blob reporter used
- GitHub reporter used
- 2 retries enabled
- 1 worker per shard

---

## Accessibility Detailed Verification

### Run Accessibility Scan with Details

```bash
npm run test:e2e:chromium -- accessibility.spec.ts --reporter=line
```

Expected: All pages show 0 violations for WCAG 2.1 AA.

### Test Keyboard Navigation

```bash
npm run test:e2e:headed -- accessibility.spec.ts -g "keyboard"
```

Expected: Keyboard navigation tests pass, visible in browser.

---

## Common Issues and Solutions

### Issue: Browsers Not Installed

```bash
npx playwright install --with-deps chromium firefox webkit
```

### Issue: Port 4321 Already in Use

```bash
# Kill process on port 4321
lsof -ti:4321 | xargs kill -9

# Or change port in playwright.config.ts
```

### Issue: Tests Timeout

```bash
# Increase timeout for specific test
npm run test:e2e:chromium -- --timeout=60000
```

### Issue: File System Access API Test Fails

This is expected - use mocked tests for automation:
```bash
npm run test:e2e:chromium -- playground.spec.ts -g "mocked"
```

---

## Performance Verification

### Measure Test Execution Time

```bash
time npm run test:e2e:chromium
```

Expected: < 5 minutes for full suite on Chromium.

### Check Test Report

```bash
npm run test:e2e:chromium
open playwright-report/index.html
```

Expected: HTML report opens with test results, screenshots, videos.

---

## Final Verification Checklist

Run this comprehensive verification:

```bash
#!/bin/bash

echo "=== Playwright E2E Testing Verification ==="
echo ""

echo "1. Checking installation..."
npm list @playwright/test @axe-core/playwright

echo ""
echo "2. Checking browsers..."
npx playwright --version

echo ""
echo "3. Checking configuration..."
cat playwright.config.ts | grep -E "headless|baseURL|projects"

echo ""
echo "4. Running smoke tests..."
npm run test:e2e:chromium -- smoke.spec.ts

echo ""
echo "5. Running accessibility tests..."
npm run test:e2e:chromium -- accessibility.spec.ts

echo ""
echo "6. Checking documentation..."
ls -la .prompts/019-playwright-e2e-testing-implement/

echo ""
echo "7. Checking test files..."
find tests/e2e -name "*.spec.ts" -o -name "*Page.ts" -o -name "*Component.ts" | wc -l

echo ""
echo "=== Verification Complete ==="
```

Save as `verify-playwright.sh`, make executable, and run:

```bash
chmod +x verify-playwright.sh
./verify-playwright.sh
```

---

## Success Criteria

All verifications should show:

- [x] Dependencies installed correctly
- [x] Browsers installed (Chromium, Firefox, WebKit)
- [x] Configuration valid (headed mode, multi-browser)
- [x] Directory structure complete
- [x] All page objects compile
- [x] Smoke tests pass (5/5)
- [x] Navigation tests pass (5/5)
- [x] Accessibility tests pass (7/7, 0 violations)
- [x] Playground tests pass (6/7, 1 skipped)
- [x] API tests pass (5/5)
- [x] Documentation complete (8 files)
- [x] GitHub Actions workflow exists
- [x] TypeScript compilation successful
- [x] Test execution time < 5 minutes (Chromium)

---

## Next Steps After Verification

1. **Commit Changes**
   ```bash
   git add .
   git commit -m "feat: Add comprehensive Playwright E2E test suite

   - Add headed mode configuration for File System Access API
   - Implement Page Object Model architecture
   - Add WCAG 2.1 AA accessibility tests
   - Create playground, navigation, and API tests
   - Set up CI/CD with GitHub Actions and test sharding
   - Add comprehensive test documentation"
   ```

2. **Push to GitHub**
   ```bash
   git push origin develop
   ```

3. **Verify CI/CD**
   - Check GitHub Actions workflow runs
   - Verify tests pass in CI
   - Check artifacts are uploaded

4. **Create Pull Request** (if needed)
   - Compare develop with main
   - Add test results to PR description
   - Request review

---

**Verification Guide Created**: December 21, 2025
**Status**: ✅ READY FOR VERIFICATION
