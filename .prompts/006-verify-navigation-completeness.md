# Meta-Prompt: Verify and Ensure Complete Website Navigation

**Objective**: Verify that all website pages are accessible from the home page through various navigation paths, and fix any missing links or navigation gaps.

**Context**: This is a three-phase meta-prompt designed for Claude-to-Claude execution. Each phase produces outputs consumed by the next phase.

---

## Phase 1: Research - Navigation Discovery

**Input**: Website source code in `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/website/`

**Task**: Discover and catalog all navigation paths from the home page.

**Instructions**:
1. Scan `src/pages/` directory to identify all `.astro` page files
2. Read `src/layouts/MainLayout.astro` to understand header/footer navigation
3. Read `src/pages/index.astro` to identify all links from home page
4. For each page found, check if it's linked from:
   - Header navigation in MainLayout
   - Direct links on home page
   - Footer links (if any)
5. Create a navigation map showing all reachable pages from home
6. Identify any orphaned pages (pages without links from home)

**Output Format** (save to `.prompts/006-phase1-navigation-map.json`):
```json
{
  "allPages": [
    {"path": "/", "file": "index.astro", "title": "Home"},
    {"path": "/about", "file": "about.astro", "title": "About"}
  ],
  "navigationSources": {
    "header": ["about", "features", "architecture", "..."],
    "homePageDirectLinks": ["playground", "docs", "getting-started", "..."],
    "footer": []
  },
  "accessibleFromHome": ["about", "features", "..."],
  "orphanedPages": [],
  "missingLinks": []
}
```

**Verification Criteria**:
- All pages in `src/pages/` are cataloged
- Navigation sources are accurately identified
- Orphaned pages list is complete
- Output is valid JSON

---

## Phase 2: Planning - Navigation Improvement Strategy

**Input**:
- Navigation map from Phase 1 (`.prompts/006-phase1-navigation-map.json`)
- Website design patterns from existing pages

**Task**: Design a plan to ensure all pages are accessible from home, respecting existing design patterns.

**Instructions**:
1. Read the navigation map from Phase 1
2. For each orphaned or poorly-linked page, determine best navigation placement:
   - Should it be in header navigation?
   - Should it be a direct link on home page?
   - Should it be in a footer?
   - Should it be in contextual "Related Pages" sections?
3. Review existing navigation patterns in `src/pages/index.astro` and `src/layouts/MainLayout.astro`
4. Design changes that:
   - Match existing visual/structural patterns
   - Follow information architecture best practices
   - Don't overcrowd navigation areas
   - Group related pages logically
5. Consider user journeys:
   - New users: Home → Getting Started → Features → Playground
   - Developers: Home → Docs → Architecture → Examples
   - Researchers: Home → About → Benchmarks → FAQ
6. Identify any pages that should have reciprocal links

**Output Format** (save to `.prompts/006-phase2-navigation-plan.md`):
```markdown
# Navigation Improvement Plan

## Current State
- Total pages: X
- Accessible from home: Y
- Orphaned: Z
- Navigation sources: header, home page, footer

## Identified Issues
1. Page X is not linked from home
2. Page Y only accessible via header, no contextual links
3. Navigation group Z is overcrowded

## Proposed Changes

### Change 1: Add Missing Links to Home Page
- **Where**: Home page "Get Started" section
- **Add links to**: [page1, page2]
- **Pattern**: Use existing arrow link style
- **Code location**: `src/pages/index.astro` lines XX-YY

### Change 2: Update Header Navigation
- **Where**: MainLayout header
- **Changes**: Reorder items, add dropdown, etc.
- **Code location**: `src/layouts/MainLayout.astro` lines XX-YY

### Change 3: Add Footer Navigation
- **Where**: MainLayout footer
- **Add**: Quick links section with [pages]
- **Code location**: `src/layouts/MainLayout.astro` lines XX-YY

## User Journey Validation
- Journey 1 (New User): ✅ Home → Getting Started → Features → Playground
- Journey 2 (Developer): ✅ Home → Docs → Architecture → Examples
- Journey 3 (Researcher): ⚠️  Missing link from About → Benchmarks

## Implementation Order
1. Fix critical orphaned pages
2. Add contextual links for key journeys
3. Enhance footer navigation
4. Add "Related Pages" sections
```

**Verification Criteria**:
- All orphaned pages have a solution
- Changes respect existing design patterns
- User journeys are validated
- Implementation order is logical

---

## Phase 3: Execution - Implement Navigation Changes

**Input**:
- Navigation plan from Phase 2 (`.prompts/006-phase2-navigation-plan.md`)
- Website source code

**Task**: Implement the planned navigation changes and verify completeness using Playwright or fetch.

**Instructions**:

### 3.1 Implement Code Changes
1. Read the navigation plan from Phase 2
2. For each proposed change:
   - Read the target file
   - Make the change following existing code patterns
   - Preserve styling consistency
   - Use proper Astro syntax and base URL handling
3. Changes might include:
   - Updating `src/layouts/MainLayout.astro` (header/footer)
   - Updating `src/pages/index.astro` (home page links)
   - Adding "Related Pages" sections to individual pages
   - Creating navigation components if needed

### 3.2 Build and Test
1. Run `npm run build` to verify no build errors
2. Run `npm run dev` in background for testing
3. Use Playwright to verify navigation:

```typescript
// Verification script concept
async function verifyNavigation(page: Page) {
  await page.goto('http://localhost:4321/');

  // Find all navigation links
  const headerLinks = await page.locator('header a').all();
  const homeLinks = await page.locator('main a').all();

  // Test each link is accessible and works
  for (const link of [...headerLinks, ...homeLinks]) {
    const href = await link.getAttribute('href');
    if (href?.startsWith('/') || href?.startsWith(baseUrl)) {
      // Click and verify page loads
      await link.click();
      await page.waitForLoadState('networkidle');
      // Verify not 404
      // Navigate back
      await page.goBack();
    }
  }

  return { totalLinks, workingLinks, brokenLinks };
}
```

### 3.3 Verification Steps
1. Start dev server: `npm run dev`
2. Use Playwright or fetch to:
   - Load home page
   - Extract all internal links
   - Verify each link returns 200 status
   - Check that all pages from Phase 1 are reachable
3. Generate verification report

### 3.4 Commit Changes
1. Stage changed files: `git add src/pages/index.astro src/layouts/MainLayout.astro ...`
2. Commit with descriptive message: `feat: ensure complete navigation from home page`
3. Push changes

**Output Format** (save to `.prompts/006-phase3-verification-report.md`):
```markdown
# Navigation Verification Report

## Changes Implemented
- ✅ Updated header navigation in MainLayout.astro
- ✅ Added links to home page index.astro
- ✅ Added footer navigation
- ✅ Added "Related Pages" sections to 3 pages

## Verification Results

### Build Test
- Status: ✅ Success
- Build time: 942ms
- Pages built: 10

### Navigation Test (Playwright/Fetch)
- Test method: Playwright browser automation
- Base URL: http://localhost:4321/
- Total pages: 10
- Pages accessible from home: 10/10 ✅

### Detailed Link Test
| Page | Status | Response Time | Notes |
|------|--------|---------------|-------|
| / | ✅ 200 | 45ms | Home page |
| /about | ✅ 200 | 32ms | Linked from header |
| /features | ✅ 200 | 28ms | Linked from header + home |
| ... | ... | ... | ... |

### User Journey Validation
- ✅ New User: Home → Getting Started → Features → Playground
- ✅ Developer: Home → Docs → Architecture → Examples
- ✅ Researcher: Home → About → Benchmarks → FAQ

## Remaining Issues
- None

## Commit Info
- Commit: abc123f
- Message: "feat: ensure complete navigation from home page"
- Files changed: 3
- Lines added: 45
```

**Verification Criteria**:
- All code changes implemented correctly
- Build succeeds without errors
- All pages return 200 status
- All pages reachable from home
- Changes committed to git
- Verification report is complete

---

## Success Criteria (All Phases)

1. **Completeness**: All pages in `src/pages/` are discoverable
2. **Accessibility**: Every page has at least one link from home page (direct or via header/footer)
3. **User Experience**: Navigation follows logical user journeys
4. **Consistency**: Changes match existing design patterns
5. **Verification**: Automated test confirms all links work
6. **Documentation**: Each phase produces clear outputs for next phase

---

## Usage Instructions

Execute each phase sequentially in separate Claude contexts:

```bash
# Phase 1: Research
claude --prompt "$(cat .prompts/006-verify-navigation-completeness.md | sed -n '/## Phase 1/,/## Phase 2/p')"

# Phase 2: Planning
claude --prompt "$(cat .prompts/006-verify-navigation-completeness.md | sed -n '/## Phase 2/,/## Phase 3/p')"

# Phase 3: Execution
claude --prompt "$(cat .prompts/006-verify-navigation-completeness.md | sed -n '/## Phase 3/,/## Success Criteria/p')"
```

Or use the `/run-prompt` command:
```
/run-prompt 006-verify-navigation-completeness --sequential
```

---

## Notes

- This meta-prompt uses a research → plan → implement pattern
- Each phase can be executed independently with fresh context
- Phases can be parallelized if multiple navigation areas need work
- Playwright verification ensures links actually work, not just exist
- The prompt respects existing design patterns and navigation structure
