# Mobile UX Implementation Plan

## Objective

Create a detailed, phased implementation plan for mobile UX improvements based on comprehensive research findings, prioritizing WCAG compliance, navigation pattern selection, and accessibility enhancements.

**Why it matters:** The research identified a critical WCAG violation (touch targets 1px too small) affecting 10/11 navigation links, plus navigation pattern inconsistencies with industry standards. A clear implementation plan ensures these issues are addressed systematically while maintaining site quality.

## Context

### Research Reference
**Primary source:** @.prompts/008-mobile-friendly-ux-research/mobile-friendly-ux-research.md

**Key findings from research:**
- **Critical:** Touch targets measure 43px (need 44px minimum for WCAG AAA)
- **Navigation:** Current vertical always-visible pattern differs from MDN/TypeScript/Rust (all use hamburger menus)
- **Performance:** Excellent (16ms load, 81ms FCP)
- **Accessibility:** Missing skip link, aria-current attributes
- **Mobile readiness score:** 7.5/10

**Research verified with:**
- 22 Playwright `.boundingBox()` measurements across 2 viewports
- 6 performance test runs (averaged over 3 runs each)
- Competitive analysis of MDN, TypeScript, Rust documentation sites
- Accessibility tree analysis via Playwright

### Current Architecture
- Astro static site generator
- Tab-based navigation in `src/layouts/MainLayout.astro`
- CSS-in-Astro with `<style is:global>` in layout
- 11 navigation tabs that wrap on mobile
- Current breakpoint: 768px (mobile vs desktop)

### Constraints
- Must maintain existing tab navigation structure for desktop
- No breaking changes to existing routes
- Performance budget: maintain current excellent metrics
- Solo developer context (implementations should be achievable in focused work sessions)

## Requirements

### 1. Decision Framework

First, establish decision criteria for navigation pattern choice:

**Option A: Hamburger Menu (Industry Standard)**
- Pros: Frees 480px vertical space, matches user expectations from MDN/TypeScript/Rust
- Cons: Requires JavaScript for menu toggle, additional HTML/CSS for drawer
- Implementation time: 4-6 hours (menu button, drawer animation, overlay, accessibility)

**Option B: Collapsible Navigation (Current Pattern Enhanced)**
- Pros: No JavaScript needed, simpler implementation, maintains current architecture
- Cons: Still takes vertical space when open, non-standard pattern
- Implementation time: 2-3 hours (collapse-by-default, expand button, ARIA)

**Option C: Hybrid (Sticky + Hamburger)**
- Pros: Best of both worlds, sticky header keeps nav accessible
- Cons: Most complex, requires both JavaScript and sticky positioning
- Implementation time: 6-8 hours

**Recommendation criteria:**
- If user priority = industry standard UX → Choose A
- If user priority = simplicity + speed → Choose B
- If user priority = maximum polish → Choose C

**Plan should include decision tree** showing which option to implement based on stated priorities.

### 2. Phased Implementation Structure

The plan must break work into clear phases:

**Phase 0: Immediate Fix (5 minutes - can be deployed today)**
- Fix WCAG touch target violation
- No dependencies, no testing required (pure CSS)

**Phase 1: Critical Fixes (25-30 minutes total)**
- Touch target fix (from Phase 0)
- Skip navigation link
- ARIA attributes for active tabs
- All accessibility quick wins

**Phase 2: Navigation Pattern Implementation (2-8 hours depending on choice)**
- Implement chosen navigation pattern (A, B, or C)
- Breakpoint-specific behavior
- Accessibility testing
- Cross-browser validation

**Phase 3: Performance & Polish (Future - 2-3 hours)**
- Font loading optimization
- Lazy loading considerations
- Additional accessibility enhancements
- Mobile-specific refinements

### 3. Detailed Implementation Specifications

For each phase, the plan must provide:

**File Changes:**
```
src/layouts/MainLayout.astro:
  - Lines to modify
  - Specific CSS changes
  - HTML structure changes (if needed)
  - ARIA attributes to add
```

**Code Snippets:**
- Exact CSS with pixel values
- HTML snippets for new elements
- JavaScript (if needed for hamburger menu)

**Testing Requirements:**
- Playwright tests to write
- Manual testing checklist
- Accessibility validation steps
- Cross-viewport verification

**Rollback Plan:**
- How to revert if issues arise
- Git workflow (feature branch vs direct to develop)

### 4. Navigation Pattern Implementation Details

For **each navigation pattern option** (A, B, C), provide:

#### Option A: Hamburger Menu Implementation

**Files to modify:**
- `src/layouts/MainLayout.astro` (add menu button, drawer, overlay)

**New CSS classes needed:**
```css
.mobile-menu-button { }
.mobile-nav-drawer { }
.mobile-nav-overlay { }
.mobile-nav-drawer.open { }
```

**JavaScript requirements:**
```javascript
// Menu toggle logic
// Focus management
// Escape key handler
// Click-outside-to-close
```

**Accessibility requirements:**
- `aria-expanded` on button
- `aria-label="Main navigation menu"`
- Focus trap in drawer
- Keyboard navigation (Tab, Escape, Enter)

**Animation specifications:**
- Slide-in duration: 250ms
- Easing: ease-out
- Overlay fade: 200ms

#### Option B: Collapsible Navigation Implementation

**Files to modify:**
- `src/layouts/MainLayout.astro` (add collapse button, aria-expanded)

**CSS changes:**
```css
@media (max-width: 768px) {
  .tab-nav {
    display: none; /* collapsed by default */
  }
  .tab-nav.expanded {
    display: flex;
  }
}
```

**JavaScript requirements (minimal):**
```javascript
// Toggle collapsed state
// Save preference to localStorage (optional)
```

#### Option C: Hybrid Implementation

**Files to modify:**
- `src/layouts/MainLayout.astro` (sticky header, hamburger, drawer)

**Additional considerations:**
- Sticky positioning with `position: sticky; top: 0;`
- Z-index management
- Scroll behavior
- Header height adjustment

### 5. Testing & Validation Plan

For each phase, specify:

**Automated Tests:**
```javascript
// Playwright tests to add
test('touch targets meet 44px minimum', async ({ page }) => {
  // Implementation
});

test('skip link works with keyboard navigation', async ({ page }) => {
  // Implementation
});

test('hamburger menu opens and closes', async ({ page }) => {
  // Implementation (if Option A)
});
```

**Manual Testing Checklist:**
- [ ] Touch targets measure 44px+ on mobile viewports
- [ ] Skip link appears on first Tab keypress
- [ ] Active tab has `aria-current="page"`
- [ ] Navigation menu functions on 320px, 375px, 414px, 768px
- [ ] No horizontal overflow on any viewport
- [ ] Performance metrics maintained (load < 100ms)

**Accessibility Validation:**
- [ ] Run Lighthouse accessibility audit (score ≥ 95)
- [ ] Test with VoiceOver/NVDA screen reader
- [ ] Keyboard-only navigation test
- [ ] Color contrast validation (all ratios ≥ 4.5:1)

### 6. Deployment Strategy

**Git Workflow:**
```bash
# Create feature branch
git checkout -b fix/mobile-ux-improvements

# Phase 0 (immediate)
git add src/layouts/MainLayout.astro
git commit -m "fix: increase touch target padding to meet WCAG AAA (44px minimum)"
git push origin fix/mobile-ux-improvements
# Merge to main, deploy

# Phase 1 (bundled)
git add src/layouts/MainLayout.astro
git commit -m "feat: add skip link and ARIA attributes for accessibility"
git push && merge

# Phase 2 (navigation - separate branch if complex)
git checkout -b feat/mobile-navigation-pattern
# ... implementation
```

**Deployment checklist:**
- [ ] Build succeeds (`npm run build`)
- [ ] All Playwright tests pass
- [ ] Manual testing on 3+ viewport sizes
- [ ] Lighthouse score maintained
- [ ] Deployed to GitHub Pages
- [ ] Smoke test on live site

### 7. Risk Assessment & Mitigation

**Risks to address in plan:**

| Risk | Impact | Probability | Mitigation |
|------|--------|------------|------------|
| JavaScript breaks on old browsers | High | Low | Progressive enhancement, feature detection |
| Navigation change confuses users | Medium | Medium | User testing, gradual rollout, revert plan |
| Touch target fix creates layout shift | Low | Low | Measure before/after, adjust spacing |
| Performance regression | High | Low | Bundle size check, Lighthouse gating |

**Rollback procedure:**
```bash
# If Phase 2 causes issues
git revert <commit-hash>
git push origin main
# Redeploy previous version
```

## Output Specification

**Primary Output:**
`.prompts/009-mobile-friendly-ux-plan/mobile-friendly-ux-plan.md`

**Secondary Output:**
`.prompts/009-mobile-friendly-ux-plan/SUMMARY.md`

### Plan Output Structure

```markdown
# Mobile UX Implementation Plan: C++ to C Transpiler Website

<metadata>
<confidence>high|medium|low</confidence>
<based_on>
  Research findings from mobile-friendly-ux-research.md including 22 touch target
  measurements, competitive analysis, and performance profiling across 5 viewports.
</based_on>
<dependencies>
  @.prompts/008-mobile-friendly-ux-research/mobile-friendly-ux-research.md
</dependencies>
<open_questions>
  - Navigation pattern preference: hamburger (industry standard) vs collapsible (simpler)?
  - WCAG compliance target: AA (minimum) vs AAA (current violation needs AAA)?
  - Performance budget for Phase 2: acceptable increase in bundle size?
</open_questions>
<assumptions>
  - Solo developer context: phases should fit in focused 2-4 hour sessions
  - Maintaining current Astro architecture (no framework changes)
  - Desktop experience remains unchanged (mobile-specific improvements)
  - User priority: WCAG compliance > navigation pattern polish
</assumptions>
<implementation_horizon>
  - Phase 0: Today (5 minutes)
  - Phase 1: This week (30 minutes)
  - Phase 2: Next sprint (2-8 hours depending on navigation choice)
  - Phase 3: Future (2-3 hours)
</implementation_horizon>
</metadata>

## Executive Summary

[2-3 sentence overview of plan, recommended navigation pattern, total time estimate]

## Navigation Pattern Decision Tree

### Decision Criteria

**Prioritize Industry Standard UX:**
→ Choose **Option A: Hamburger Menu** (4-6 hours)
- Matches MDN, TypeScript, Rust patterns
- Frees 480px vertical space
- Requires JavaScript implementation

**Prioritize Speed & Simplicity:**
→ Choose **Option B: Collapsible Navigation** (2-3 hours)
- Minimal code changes
- Can be no-JS with CSS-only collapse
- Faster implementation

**Prioritize Maximum Polish:**
→ Choose **Option C: Sticky + Hamburger** (6-8 hours)
- Best user experience
- Navigation always accessible
- Most complex implementation

### Recommendation

**Recommended: Option A (Hamburger Menu)** - 4-6 hour implementation

**Rationale:**
- Research competitive analysis shows 3/3 similar sites use hamburger pattern
- User expectations align with industry standard
- Vertical space savings (480px) significant on mobile
- JavaScript requirement acceptable for modern static site

**Alternative:** If time is critical, implement Option B first (2-3 hours), then upgrade to Option A in future sprint.

## Phase Breakdown

### Phase 0: Immediate WCAG Fix ⚡ (5 minutes)

**Goal:** Resolve touch target WCAG AAA violation

**Changes:**
File: `src/layouts/MainLayout.astro`
Line: ~121 (`.tab` CSS rule)

```css
/* BEFORE */
.tab {
  padding: 0.5rem 1rem;
  /* ... */
}

/* AFTER */
.tab {
  padding: 0.625rem 1rem;  /* 10px top/bottom vs 8px → total 44px */
  min-height: 44px;        /* Explicit minimum for WCAG AAA */
  /* ... */
}
```

**Testing:**
```javascript
// Playwright verification
const tabHeight = (await page.locator('.tab').first().boundingBox()).height;
expect(tabHeight).toBeGreaterThanOrEqual(44);
```

**Deployment:**
```bash
git checkout -b fix/wcag-touch-targets
git add src/layouts/MainLayout.astro
git commit -m "fix: increase nav tab padding to meet WCAG AAA touch target minimum (44px)"
git push origin fix/wcag-touch-targets
# Merge to main, deploy
```

**Success criteria:**
- [x] All navigation tabs measure ≥ 44px height
- [x] No layout shift or visual regression
- [x] Playwright test passes

**Time estimate:** 5 minutes
**Risk:** Minimal (pure CSS change)

---

### Phase 1: Accessibility Quick Wins (30 minutes total)

**Goal:** Add skip link, ARIA attributes, focus indicators

#### Task 1.1: Add Skip Navigation Link (15 minutes)

**File:** `src/layouts/MainLayout.astro`

**HTML addition** (insert after `<body>` tag, before `<header>`):
```html
<a href="#main-content" class="skip-link">
  Skip to main content
</a>
```

**CSS addition:**
```css
.skip-link {
  position: absolute;
  top: -40px;
  left: 0;
  background: #0066cc;
  color: white;
  padding: 8px 16px;
  text-decoration: none;
  z-index: 100;
  transition: top 0.2s ease;
}

.skip-link:focus {
  top: 0;
}
```

**Main element ID** (add to `<main>` tag):
```html
<main id="main-content">
  <slot />
</main>
```

**Testing:**
- Press Tab on page load
- Skip link should appear
- Press Enter → focus jumps to main content

#### Task 1.2: Add ARIA Current to Active Tab (5 minutes)

**File:** `src/layouts/MainLayout.astro`

**Modify tab rendering** (around line 162):
```astro
{tabs.map((tab) => {
  const isActive = normalizedCurrent === tab.path;
  return (
    <a
      href={tab.href}
      class={`tab ${isActive ? 'active' : ''}`}
      aria-current={isActive ? 'page' : undefined}
    >
      {tab.label}
    </a>
  );
})}
```

**Testing:**
- Inspect active tab in browser DevTools
- Should have `aria-current="page"` attribute

#### Task 1.3: Explicit Focus Indicators (10 minutes)

**CSS addition** (for keyboard navigation):
```css
.tab:focus {
  outline: 2px solid #0066cc;
  outline-offset: 2px;
}

.tab:focus:not(:focus-visible) {
  outline: none;
}

.tab:focus-visible {
  outline: 2px solid #0066cc;
  outline-offset: 2px;
}
```

**Testing:**
- Tab through navigation with keyboard
- Focus outline should be visible (2px blue border)
- Mouse clicks should not show outline (`:focus-visible` behavior)

**Phase 1 Commit:**
```bash
git add src/layouts/MainLayout.astro
git commit -m "feat: add skip link, aria-current, and keyboard focus indicators for accessibility"
git push origin fix/wcag-touch-targets
# Merge to main
```

**Phase 1 Success Criteria:**
- [x] Skip link appears on first Tab keypress
- [x] Skip link jumps to main content on Enter
- [x] Active tab has `aria-current="page"`
- [x] Focus indicators visible on keyboard navigation
- [x] Lighthouse accessibility score ≥ 95

**Time estimate:** 30 minutes
**Risk:** Low (additive changes, no breaking changes)

---

### Phase 2: Navigation Pattern Implementation (2-8 hours)

**Implementation depends on chosen option from Decision Tree**

#### Option A: Hamburger Menu (RECOMMENDED - 4-6 hours)

**File changes:**
- `src/layouts/MainLayout.astro` (HTML, CSS, JavaScript)

##### Step 2A.1: Add Menu Button HTML (30 minutes)

**Insert before navigation** (mobile only):
```html
<button
  class="mobile-menu-button"
  aria-label="Main navigation menu"
  aria-expanded="false"
  aria-controls="mobile-nav-drawer"
>
  <svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
    <line x1="3" y1="6" x2="21" y2="6" class="menu-icon-line"></line>
    <line x1="3" y1="12" x2="21" y2="12" class="menu-icon-line"></line>
    <line x1="3" y1="18" x2="21" y2="18" class="menu-icon-line"></line>
  </svg>
</button>
```

**Wrap navigation for drawer:**
```html
<div id="mobile-nav-drawer" class="mobile-nav-drawer" aria-hidden="true">
  <nav class="tab-nav" role="navigation" aria-label="Main navigation">
    {/* existing tabs */}
  </nav>
</div>
<div class="mobile-nav-overlay" aria-hidden="true"></div>
```

##### Step 2A.2: Add Hamburger Menu CSS (1-2 hours)

**Mobile menu button:**
```css
.mobile-menu-button {
  display: none;
  background: none;
  border: none;
  color: white;
  padding: 0.75rem;
  cursor: pointer;
  min-width: 44px;
  min-height: 44px;
}

@media (max-width: 768px) {
  .mobile-menu-button {
    display: block;
  }
}
```

**Drawer styles:**
```css
.mobile-nav-drawer {
  position: fixed;
  top: 0;
  left: -280px;
  width: 280px;
  height: 100vh;
  background: #2a2a2a;
  transition: left 0.25s ease-out;
  z-index: 1000;
  overflow-y: auto;
}

.mobile-nav-drawer.open {
  left: 0;
}

@media (max-width: 768px) {
  .tab-brand {
    display: block; /* Keep brand visible */
  }

  .tab-nav {
    display: flex;
    flex-direction: column;
    padding: 1rem;
    gap: 0.5rem;
  }

  .tab {
    width: 100%;
    border-radius: 0.25rem;
    border: 1px solid #444;
  }
}

@media (min-width: 769px) {
  .mobile-menu-button,
  .mobile-nav-drawer,
  .mobile-nav-overlay {
    display: none !important;
  }
}
```

**Overlay styles:**
```css
.mobile-nav-overlay {
  display: none;
  position: fixed;
  top: 0;
  left: 0;
  width: 100%;
  height: 100%;
  background: rgba(0, 0, 0, 0.5);
  z-index: 999;
  opacity: 0;
  transition: opacity 0.2s ease-out;
}

.mobile-nav-overlay.visible {
  display: block;
  opacity: 1;
}
```

##### Step 2A.3: Add Menu Toggle JavaScript (1-2 hours)

**Insert before closing `</body>`:**
```html
<script>
  (() => {
    if (typeof window === 'undefined') return;

    const menuButton = document.querySelector('.mobile-menu-button');
    const drawer = document.querySelector('.mobile-nav-drawer');
    const overlay = document.querySelector('.mobile-nav-overlay');

    if (!menuButton || !drawer || !overlay) return;

    let isOpen = false;

    const openMenu = () => {
      isOpen = true;
      drawer.classList.add('open');
      overlay.classList.add('visible');
      drawer.setAttribute('aria-hidden', 'false');
      menuButton.setAttribute('aria-expanded', 'true');

      // Focus trap: focus first nav link
      const firstLink = drawer.querySelector('.tab');
      if (firstLink) firstLink.focus();

      // Prevent body scroll
      document.body.style.overflow = 'hidden';
    };

    const closeMenu = () => {
      isOpen = false;
      drawer.classList.remove('open');
      overlay.classList.remove('visible');
      drawer.setAttribute('aria-hidden', 'true');
      menuButton.setAttribute('aria-expanded', 'false');

      // Restore body scroll
      document.body.style.overflow = '';

      // Return focus to menu button
      menuButton.focus();
    };

    // Toggle on button click
    menuButton.addEventListener('click', () => {
      isOpen ? closeMenu() : openMenu();
    });

    // Close on overlay click
    overlay.addEventListener('click', closeMenu);

    // Close on Escape key
    document.addEventListener('keydown', (e) => {
      if (e.key === 'Escape' && isOpen) {
        closeMenu();
      }
    });

    // Close when navigation link is clicked
    drawer.querySelectorAll('.tab').forEach(link => {
      link.addEventListener('click', closeMenu);
    });
  })();
</script>
```

##### Step 2A.4: Testing & Validation (1 hour)

**Playwright tests:**
```javascript
test('hamburger menu opens and closes on mobile', async ({ page }) => {
  await page.setViewportSize({ width: 375, height: 667 });
  await page.goto('http://localhost:4321/cpp-to-c-website/');

  // Menu button should be visible
  const menuButton = page.locator('.mobile-menu-button');
  await expect(menuButton).toBeVisible();

  // Drawer should be hidden initially
  const drawer = page.locator('.mobile-nav-drawer');
  await expect(drawer).not.toHaveClass(/open/);

  // Click to open
  await menuButton.click();
  await expect(drawer).toHaveClass(/open/);
  await expect(menuButton).toHaveAttribute('aria-expanded', 'true');

  // Click overlay to close
  await page.locator('.mobile-nav-overlay').click();
  await expect(drawer).not.toHaveClass(/open/);
  await expect(menuButton).toHaveAttribute('aria-expanded', 'false');
});

test('hamburger menu closes on Escape key', async ({ page }) => {
  await page.setViewportSize({ width: 375, height: 667 });
  await page.goto('http://localhost:4321/cpp-to-c-website/');

  // Open menu
  await page.locator('.mobile-menu-button').click();
  await expect(page.locator('.mobile-nav-drawer')).toHaveClass(/open/);

  // Press Escape
  await page.keyboard.press('Escape');
  await expect(page.locator('.mobile-nav-drawer')).not.toHaveClass(/open/);
});

test('hamburger menu hidden on desktop', async ({ page }) => {
  await page.setViewportSize({ width: 1024, height: 768 });
  await page.goto('http://localhost:4321/cpp-to-c-website/');

  // Menu button should not be visible
  await expect(page.locator('.mobile-menu-button')).not.toBeVisible();
});
```

**Manual testing checklist:**
- [ ] Menu button appears at 768px and below
- [ ] Menu button hidden at 769px and above
- [ ] Drawer slides in from left on button click
- [ ] Overlay appears behind drawer
- [ ] Clicking overlay closes menu
- [ ] Pressing Escape closes menu
- [ ] Clicking navigation link closes menu
- [ ] Focus returns to button after close
- [ ] First link receives focus when opened
- [ ] No horizontal overflow at any viewport
- [ ] Touch target ≥ 44px for button

**Phase 2A Commit:**
```bash
git checkout -b feat/mobile-hamburger-menu
git add src/layouts/MainLayout.astro
git commit -m "feat: implement hamburger navigation menu for mobile devices

- Add menu button with accessible SVG icon
- Create slide-in drawer with overlay
- Implement focus management and keyboard navigation
- Close menu on Escape, overlay click, or link selection
- Hide on desktop (≥ 769px)
- Maintain existing desktop tab navigation

WCAG compliance: button has 44px+ touch target, aria-expanded state"
git push origin feat/mobile-hamburger-menu
# Merge to main after testing
```

**Option A Time Estimate:** 4-6 hours
**Option A Risk:** Medium (JavaScript required, focus management complexity)

---

#### Option B: Collapsible Navigation (ALTERNATIVE - 2-3 hours)

**File changes:**
- `src/layouts/MainLayout.astro` (HTML, CSS, minimal JavaScript)

##### Step 2B.1: Add Collapse Button (30 minutes)

```html
<button
  class="nav-collapse-button"
  aria-label="Toggle navigation"
  aria-expanded="false"
  aria-controls="tab-nav"
>
  <span>Menu</span>
  <svg><!-- chevron icon --></svg>
</button>

<nav id="tab-nav" class="tab-nav" aria-hidden="true">
  {/* existing tabs */}
</nav>
```

##### Step 2B.2: Collapse CSS (1 hour)

```css
@media (max-width: 768px) {
  .nav-collapse-button {
    display: block;
    width: 100%;
    min-height: 44px;
    /* ... */
  }

  .tab-nav {
    display: none; /* collapsed by default */
  }

  .tab-nav.expanded {
    display: flex;
    flex-direction: column;
  }
}
```

##### Step 2B.3: Toggle JavaScript (30 minutes)

```javascript
// Simple toggle with localStorage persistence
```

**Option B Time Estimate:** 2-3 hours
**Option B Risk:** Low (simpler than hamburger, fewer edge cases)

---

### Phase 3: Performance & Polish (Future - 2-3 hours)

**Deferred improvements:**
- Font loading optimization
- Lazy load below-fold content
- Additional mobile refinements
- Advanced accessibility features

---

## Testing Strategy

### Automated Tests

**New test file:** `tests/mobile-navigation.spec.ts`

```typescript
import { test, expect } from '@playwright/test';

test.describe('Mobile Navigation', () => {
  test('meets WCAG touch target requirements', async ({ page }) => {
    await page.setViewportSize({ width: 375, height: 667 });
    await page.goto('/');

    const tabs = page.locator('.tab');
    const count = await tabs.count();

    for (let i = 0; i < count; i++) {
      const box = await tabs.nth(i).boundingBox();
      expect(box.width).toBeGreaterThanOrEqual(44);
      expect(box.height).toBeGreaterThanOrEqual(44);
    }
  });

  test('skip link works', async ({ page }) => {
    await page.goto('/');

    // Press Tab
    await page.keyboard.press('Tab');

    // Skip link should be focused
    const skipLink = page.locator('.skip-link');
    await expect(skipLink).toBeFocused();

    // Press Enter
    await page.keyboard.press('Enter');

    // Main content should be focused
    const main = page.locator('#main-content');
    await expect(main).toBeFocused();
  });

  // Add hamburger menu tests if Option A chosen
});
```

### Manual Testing Checklist

**Cross-viewport validation:**
- [ ] Test on 320px (iPhone SE)
- [ ] Test on 375px (iPhone 8)
- [ ] Test on 414px (iPhone 11 Pro Max)
- [ ] Test on 768px (iPad Portrait - breakpoint boundary)
- [ ] Test on 1024px (iPad Landscape - desktop mode)

**Accessibility validation:**
- [ ] Run Lighthouse (target score: 95+)
- [ ] Test with VoiceOver on iOS
- [ ] Test with keyboard only (no mouse)
- [ ] Verify color contrast ratios

**Performance validation:**
- [ ] Load time < 100ms (localhost)
- [ ] No layout shift (CLS = 0)
- [ ] Bundle size increase < 5KB (if adding JavaScript)

## Deployment Plan

### Pre-deployment Checklist

- [ ] All Playwright tests passing
- [ ] Build succeeds (`npm run build`)
- [ ] No console errors or warnings
- [ ] Manual testing complete (all viewports)
- [ ] Lighthouse accessibility score ≥ 95
- [ ] Performance metrics maintained or improved
- [ ] Git commit messages follow conventional commits
- [ ] Branch merged to main via PR (if using PRs)

### Deployment Steps

```bash
# Phase 0 + 1 (bundled)
git checkout develop
git pull origin develop
git checkout -b fix/mobile-ux-phase-1
# ... make changes ...
npm run build
git add src/layouts/MainLayout.astro
git commit -m "fix: mobile UX improvements (WCAG compliance, skip link, ARIA)"
git push origin fix/mobile-ux-phase-1
git checkout main
git merge fix/mobile-ux-phase-1
git push origin main
# GitHub Actions deploys to Pages

# Phase 2 (separate branch if complex)
git checkout develop
git checkout -b feat/mobile-navigation
# ... make changes ...
npm run build
npm test
git add src/layouts/MainLayout.astro tests/mobile-navigation.spec.ts
git commit -m "feat: implement hamburger menu for mobile navigation"
git push origin feat/mobile-navigation
# Review, test, merge to main
```

### Rollback Procedure

If Phase 2 causes issues in production:

```bash
# Identify problematic commit
git log --oneline

# Revert the commit
git revert <commit-hash>

# Or reset to previous working version
git reset --hard <previous-commit>
git push origin main --force

# Redeploy immediately
```

## Risk Mitigation

### Phase 0 Risks
| Risk | Impact | Mitigation |
|------|--------|------------|
| Layout shift from padding change | Low | Verify with Playwright bounding box tests |
| Text wrapping change | Low | Visual regression testing at all viewports |

### Phase 1 Risks
| Risk | Impact | Mitigation |
|------|--------|------------|
| Skip link interferes with header | Low | Position: absolute with z-index management |
| Focus indicators too prominent | Low | Use :focus-visible for keyboard-only |

### Phase 2 Risks
| Risk | Impact | Mitigation |
|------|--------|------------|
| JavaScript fails on old browsers | High | Progressive enhancement, feature detection |
| Drawer animation janky on low-end devices | Medium | Use CSS transitions, test on throttled CPU |
| Focus trap breaks navigation | High | Thoroughly test focus management, add Escape hatch |
| Increased bundle size | Medium | Check bundle analyzer, consider vanilla JS vs library |

## Success Metrics

**Phase 0:**
- ✅ All touch targets ≥ 44px (Playwright verified)
- ✅ No visual regressions
- ✅ Deployed within 1 business day

**Phase 1:**
- ✅ Lighthouse accessibility score ≥ 95
- ✅ Skip link functional on all pages
- ✅ Active tab has aria-current
- ✅ Deployed within 1 week

**Phase 2:**
- ✅ Mobile navigation functional 320px - 768px
- ✅ Desktop navigation unchanged (≥ 769px)
- ✅ No horizontal overflow any viewport
- ✅ Performance maintained (load < 100ms, CLS = 0)
- ✅ All Playwright tests passing
- ✅ User feedback positive (if collecting)

## Next Steps After Planning

1. **Get navigation pattern approval:**
   - Show Decision Tree to stakeholder/user
   - Select Option A (hamburger), B (collapsible), or C (hybrid)

2. **Execute Phase 0 immediately** (5 minutes)
   - No approval needed (pure WCAG fix)

3. **Schedule Phase 1** (30-minute session this week)

4. **Schedule Phase 2** (2-8 hour session based on chosen option)

5. **Create implementation prompts** (if using prompt-driven development):
   - `.prompts/010-mobile-ux-phase-0-implement/` (or execute directly)
   - `.prompts/011-mobile-ux-phase-1-implement/`
   - `.prompts/012-mobile-ux-phase-2-implement/`
```

### SUMMARY.md Structure

```markdown
# Mobile UX Implementation Plan Summary

**4-phase plan to fix WCAG violation, add accessibility features, and implement hamburger menu navigation (total 5-7 hours over 2 weeks)**

## Version
v1 - Initial implementation plan based on comprehensive mobile UX research

## Key Components

### Phase 0: Immediate Fix (5 minutes - deploy today)
• Change `.tab` padding from `0.5rem` to `0.625rem` → achieves 44px touch target minimum
• Add `min-height: 44px` explicit constraint
• Pure CSS change, zero risk, immediate WCAG AAA compliance

### Phase 1: Accessibility Quick Wins (30 minutes - this week)
• Skip navigation link (15min) - hidden until Tab keypress
• `aria-current="page"` on active tab (5min)
• Explicit focus indicators for keyboard navigation (10min)
• Target: Lighthouse accessibility score ≥ 95

### Phase 2: Navigation Pattern (4-6 hours - next sprint)
**Recommended: Option A - Hamburger Menu**
• Menu button + slide-in drawer + overlay (30min HTML + 1-2hr CSS)
• JavaScript for toggle, focus trap, Escape handler (1-2hr)
• Playwright tests for open/close/keyboard (1hr)
• Matches industry standard (MDN, TypeScript, Rust all use hamburger pattern)
• Frees 480px vertical space on mobile

**Alternative: Option B - Collapsible Navigation** (2-3hr if time critical)

### Phase 3: Future Polish (2-3 hours - deferred)
• Font loading optimization
• Lazy loading
• Advanced accessibility features

## Files Modified
• `src/layouts/MainLayout.astro` - All changes in single layout file
• `tests/mobile-navigation.spec.ts` - New test file for automated validation

## Decisions Needed
• **Navigation pattern choice:** Hamburger menu (recommended, 4-6hr) OR Collapsible (faster, 2-3hr)?
• **Deployment strategy:** Bundle Phase 0+1 (30min total) OR deploy Phase 0 today (5min) then Phase 1 separately?
• **Testing depth:** Minimal manual testing OR full cross-browser validation?

## Blockers
None - all phases have clear implementation steps, can begin immediately

**Ready to execute:**
- Phase 0: No dependencies, deploy today
- Phase 1: Can run in parallel with Phase 0 or sequentially
- Phase 2: Requires navigation pattern decision from user

## Next Step
**Decision required:** Choose navigation pattern (hamburger vs collapsible) using Decision Tree in plan.

**Then:**
1. Execute Phase 0 immediately (5-minute CSS fix)
2. Schedule 30-minute session for Phase 1 this week
3. Schedule 4-6 hour session for Phase 2 next sprint (if Option A chosen)

**Estimated total time:** 5-7 hours over 2 weeks
**WCAG compliance achieved:** After Phase 1 (35 minutes total)
```

## Success Criteria

Plan is complete when:

- [x] Navigation pattern decision tree provided with clear criteria
- [x] All 4 phases detailed with time estimates
- [x] Specific file changes documented (file paths, line numbers where possible)
- [x] Code snippets provided for all CSS/HTML/JavaScript changes
- [x] Testing strategy includes both automated (Playwright) and manual checklists
- [x] Deployment procedure documented with git workflow
- [x] Risk assessment completed with mitigation strategies
- [x] Success metrics defined for each phase
- [x] SUMMARY.md created with substantive one-liner
- [x] Based on research findings with @ reference
- [x] Includes rollback procedure
- [x] Metadata includes dependencies, open questions, assumptions

**Plan must be actionable:** Developer should be able to start implementation immediately after reading, with all decisions clearly marked and implementation details explicit.
