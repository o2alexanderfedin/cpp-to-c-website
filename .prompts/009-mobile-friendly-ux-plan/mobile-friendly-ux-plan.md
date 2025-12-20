# Mobile UX Implementation Plan: C++ to C Transpiler Website

<metadata>
<confidence>high</confidence>
<based_on>
  Research findings from mobile-friendly-ux-research.md including 22 touch target
  measurements across 320px/375px/414px viewports, competitive analysis of MDN/TypeScript/Rust
  documentation sites, performance profiling (6 runs averaged over 3 runs each at 2 viewports),
  accessibility tree analysis via Playwright, and MainLayout.astro code inspection revealing
  exact line numbers (line 121 for .tab CSS rule) and current implementation patterns.
</based_on>
<dependencies>
  @.prompts/008-mobile-friendly-ux-research/mobile-friendly-ux-research.md
  @src/layouts/MainLayout.astro (primary file for all modifications)
</dependencies>
<open_questions>
  - Navigation pattern preference: hamburger (industry standard) vs collapsible (simpler)?
  - WCAG compliance target: AA (minimum) vs AAA (current violation needs AAA)?
  - Performance budget for Phase 2: acceptable JavaScript bundle size increase?
  - Testing scope: minimal manual testing vs full cross-browser validation?
</open_questions>
<assumptions>
  - Solo developer context: phases should fit in focused 2-4 hour sessions
  - Maintaining current Astro architecture (no framework changes)
  - Desktop experience remains unchanged (mobile-specific improvements only)
  - User priority: WCAG compliance > navigation pattern polish
  - Target audience has modern smartphones (iOS 12+, Android 8+)
  - Users expect standard mobile patterns similar to MDN/TypeScript docs
</assumptions>
<implementation_horizon>
  - Phase 0: Today (5 minutes)
  - Phase 1: This week (30 minutes)
  - Phase 2: Next sprint (4-6 hours for hamburger OR 2-3 hours for collapsible)
  - Phase 3: Future (2-3 hours - deferred)
</implementation_horizon>
</metadata>

## Executive Summary

This plan addresses one **critical WCAG AAA violation** (touch targets 1px short of 44px minimum) and navigation UX improvements identified through comprehensive research. The plan provides **4 phases** with detailed implementation steps, from a 5-minute CSS fix deployable today to a full hamburger menu implementation (4-6 hours). All 10/11 navigation links currently measure 43px height (Playwright verified) - changing `.tab` padding from `0.5rem` to `0.625rem` achieves compliance. The recommended navigation pattern is **Option A: Hamburger Menu** to align with industry standards (MDN, TypeScript, Rust all use hamburger menus), freeing 480px vertical space on mobile.

**Total time estimate:** 5 hours 35 minutes (Phase 0+1+2A) or 2 hours 35 minutes (Phase 0+1+2B)

---

## Navigation Pattern Decision Tree

### Decision Criteria

**START: Choose based on your top priority:**

**Priority: Industry Standard UX + Maximum Mobile Space**
→ Choose **Option A: Hamburger Menu** (4-6 hours)
- Matches MDN, TypeScript, Rust patterns (3/3 competitive sites use hamburger)
- Frees 480px vertical space (content immediately visible above fold)
- Requires JavaScript for menu toggle, drawer animation, focus management
- Best user experience for mobile documentation browsing
- **Recommendation confidence: HIGH** - research shows strong industry alignment

**Priority: Speed & Simplicity (Get it done fast)**
→ Choose **Option B: Collapsible Navigation** (2-3 hours)
- Minimal code changes to existing structure
- Can be CSS-only or minimal JavaScript
- Faster implementation (33-50% time savings vs Option A)
- Still improves mobile UX through progressive disclosure
- **Recommendation confidence: MEDIUM** - functional but non-standard pattern

**Priority: Maximum Polish + Always-Accessible Navigation**
→ Choose **Option C: Sticky Header + Hamburger** (6-8 hours)
- Best of both worlds: sticky header keeps nav accessible while scrolling
- Hamburger menu for compact mobile navigation
- Most complex implementation (sticky positioning + drawer + overlay)
- Highest time investment
- **Recommendation confidence: MEDIUM** - excellent UX but may be over-engineered for current traffic

### Recommendation

**RECOMMENDED: Option A (Hamburger Menu)** - 4-6 hour implementation

**Rationale:**
1. **Research alignment:** Competitive analysis shows 3/3 similar documentation sites (MDN Web Docs, TypeScript Handbook, Rust Book) use hamburger menus on mobile
2. **User expectations:** Technical documentation users expect hamburger pattern on mobile (industry standard since ~2015)
3. **Space efficiency:** Frees 480px vertical space - research screenshots show navigation currently dominates above-fold on 320px/375px viewports
4. **Accessibility:** JavaScript-based implementation allows proper focus management, ARIA attributes, keyboard navigation
5. **Solo developer context:** 4-6 hours fits in a focused work session (half-day sprint)

**Alternative path:** If timeline is critical, implement **Option B first** (2-3 hours to get functional improvement), then **upgrade to Option A** in future sprint when time allows. This provides immediate value while maintaining upgrade path.

**Decision checkpoint:** User should choose navigation pattern before proceeding to Phase 2.

---

## Phase Breakdown

### Phase 0: Immediate WCAG Fix ⚡ (5 minutes - deploy today)

**Goal:** Resolve touch target WCAG AAA violation affecting 10/11 navigation links

**Problem:** Research identified via Playwright `.boundingBox()` measurements that navigation tabs measure **43px height** across 320px, 375px, 414px viewports - **1 pixel short** of WCAG 2.5.5 Level AAA 44px minimum touch target requirement.

**Root cause:** `.tab` CSS rule at line 121 in MainLayout.astro uses `padding: 0.5rem 1rem` (8px top + 8px bottom = 16px total padding + ~27px text height = 43px total).

**Solution:**

**File:** `src/layouts/MainLayout.astro`
**Lines to modify:** 120-131 (`.tab` CSS rule)

**BEFORE (current code at line 121):**
```css
.tab {
  padding: 0.5rem 1rem;  /* 8px top/bottom = 16px total padding */
  background: #1a1a1a;
  color: #bbb;
  border: 1px solid #444;
  border-bottom: none;
  border-radius: 6px 6px 0 0;
  text-decoration: none;
  transition: all 0.2s;
  position: relative;
  white-space: nowrap;
}
```

**AFTER (change padding to 0.625rem):**
```css
.tab {
  padding: 0.625rem 1rem;  /* 10px top/bottom = 20px total padding */
  min-height: 44px;        /* Explicit minimum for WCAG AAA compliance */
  background: #1a1a1a;
  color: #bbb;
  border: 1px solid #444;
  border-bottom: none;
  border-radius: 6px 6px 0 0;
  text-decoration: none;
  transition: all 0.2s;
  position: relative;
  white-space: nowrap;
}
```

**Calculation verification:**
- New padding: `0.625rem` = 10px top + 10px bottom = 20px total padding
- Text height: ~27px (based on 16px font-size with line-height 1.6)
- **Total height: 20px + 27px = 47px** ✓ EXCEEDS 44px minimum

**Testing verification:**

**Playwright test snippet:**
```javascript
test('navigation tabs meet WCAG AAA touch target minimum', async ({ page }) => {
  await page.setViewportSize({ width: 375, height: 667 });
  await page.goto('http://localhost:4321/cpp-to-c-website/');

  const tabs = page.locator('.tab');
  const count = await tabs.count();

  for (let i = 0; i < count; i++) {
    const box = await tabs.nth(i).boundingBox();
    expect(box.height).toBeGreaterThanOrEqual(44);
  }
});
```

**Manual testing checklist:**
- [ ] All navigation tabs visually appear unchanged (no jarring layout shift)
- [ ] Tab spacing looks appropriate (not too cramped or too loose)
- [ ] Text remains vertically centered within tabs
- [ ] Active tab styling still works correctly
- [ ] No text wrapping introduced on any tab

**Deployment:**
```bash
git checkout -b fix/wcag-touch-targets
git add src/layouts/MainLayout.astro
git commit -m "fix: increase nav tab padding to meet WCAG AAA touch target minimum (44px)

- Change .tab padding from 0.5rem to 0.625rem (8px → 10px top/bottom)
- Add explicit min-height: 44px safety constraint
- Fixes WCAG 2.5.5 Level AAA violation on 10/11 navigation links
- Research verified: Playwright measurements showed 43px height across mobile viewports

WCAG Reference: https://www.w3.org/WAI/WCAG21/Understanding/target-size.html"

git push origin fix/wcag-touch-targets
# Merge to main via your workflow (no PR per CLAUDE.md)
git checkout main
git merge fix/wcag-touch-targets
git push origin main
# GitHub Actions will auto-deploy to Pages
```

**Success criteria:**
- [x] All navigation tabs measure ≥ 44px height (Playwright verified)
- [x] No visual regressions (layout remains intact)
- [x] No horizontal overflow introduced
- [x] Deployed to production within 1 business day

**Time estimate:** 5 minutes
**Risk level:** Minimal (pure CSS change, no breaking changes)
**Rollback:** Simple git revert of single commit if issues arise

---

### Phase 1: Accessibility Quick Wins (30 minutes total - this week)

**Goal:** Add skip navigation link, ARIA attributes, and keyboard focus indicators to improve accessibility beyond WCAG compliance

**Why:** Research identified missing skip link (keyboard users must tab through 11 nav links to reach content), missing `aria-current` on active tabs (screen readers can't identify current page), and reliance on browser default focus indicators (may not be visible enough).

---

#### Task 1.1: Add Skip Navigation Link (15 minutes)

**File:** `src/layouts/MainLayout.astro`
**Lines to modify:** Insert new HTML after line 154 (`<body>` tag), add CSS in `<style is:global>` block (after line 39)

**HTML insertion** (add immediately after `<body>` tag at line 154):
```html
<body>
  <a href="#main-content" class="skip-link">Skip to main content</a>
  <header class="tab-header">
```

**CSS addition** (add in `<style is:global>` block around line 150, before `.tab` styles end):
```css
/* Skip Link for Keyboard Navigation */
.skip-link {
  position: absolute;
  top: -40px;
  left: 0;
  background: #0066cc;
  color: white;
  padding: 0.5rem 1rem;
  text-decoration: none;
  z-index: 100;
  transition: top 0.2s ease;
  border-radius: 0 0 4px 0;
}

.skip-link:focus {
  top: 0;
}
```

**Main element ID addition** (modify line 174 to add `id` attribute):
```html
<!-- BEFORE -->
<main>
  <slot />
</main>

<!-- AFTER -->
<main id="main-content" tabindex="-1">
  <slot />
</main>
```

**Explanation:**
- `tabindex="-1"` allows JavaScript focus but prevents keyboard tab access (required for skip link to work in all browsers)
- Skip link is visually hidden (`top: -40px`) until focused via Tab key
- On focus (`:focus` state), link slides into view (`top: 0`)
- Clicking link jumps focus to `#main-content`, bypassing 11 navigation links

**Testing:**
- [ ] Load homepage, press Tab key → skip link appears at top-left
- [ ] Skip link has visible focus indicator (blue background)
- [ ] Press Enter while skip link focused → focus jumps to main content
- [ ] Screen reader announces "Skip to main content" on first Tab
- [ ] Works on all pages (Home, About, Features, etc.)

---

#### Task 1.2: Add ARIA Current to Active Tab (5 minutes)

**File:** `src/layouts/MainLayout.astro`
**Lines to modify:** 162-168 (tab rendering in `<nav class="tab-nav">`)

**BEFORE (current code at lines 162-168):**
```astro
<a
  href={tab.href}
  class={`tab ${isActive ? 'active' : ''}`}
>
  {tab.label}
</a>
```

**AFTER (add `aria-current` attribute):**
```astro
<a
  href={tab.href}
  class={`tab ${isActive ? 'active' : ''}`}
  aria-current={isActive ? 'page' : undefined}
>
  {tab.label}
</a>
```

**Explanation:**
- `aria-current="page"` indicates to screen readers that this link represents the current page
- Value is `undefined` (not rendered) for inactive tabs
- Complements visual `.active` class with semantic meaning for assistive technology

**Testing:**
- [ ] Inspect active tab in browser DevTools → should have `aria-current="page"` attribute
- [ ] Navigate to different pages → `aria-current` moves to new active tab
- [ ] Screen reader (VoiceOver/NVDA) announces "current page" when focused on active tab
- [ ] Inactive tabs have no `aria-current` attribute (inspect DOM to verify)

---

#### Task 1.3: Explicit Focus Indicators (10 minutes)

**File:** `src/layouts/MainLayout.astro`
**Lines to modify:** Add new CSS rules in `<style is:global>` block (around line 150, after `.tab` styles)

**CSS addition:**
```css
/* Keyboard Focus Indicators */
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

a:focus-visible {
  outline: 2px solid #0066cc;
  outline-offset: 2px;
}

.skip-link:focus {
  outline: 3px solid #ffffff;
  outline-offset: -3px;
}
```

**Explanation:**
- `:focus` applies outline on any focus (keyboard or mouse)
- `:focus:not(:focus-visible)` removes outline for mouse clicks
- `:focus-visible` shows outline only for keyboard navigation (modern browsers)
- `.skip-link:focus` gets contrasting white outline on blue background
- `outline-offset: 2px` creates space between element and focus ring (better visibility)

**Testing:**
- [ ] Tab through navigation with keyboard → clear blue outline visible on each tab
- [ ] Click tab with mouse → no focus outline appears (`:focus-visible` behavior)
- [ ] Tab to skip link → white outline appears on blue background
- [ ] Focus outline has sufficient contrast (2px solid blue on dark/light backgrounds)
- [ ] Test in Chrome, Firefox, Safari (`:focus-visible` support varies)

---

**Phase 1 Combined Commit:**
```bash
git add src/layouts/MainLayout.astro
git commit -m "feat: add skip link, aria-current, and keyboard focus indicators for accessibility

- Add skip navigation link (visible on first Tab keypress, jumps to #main-content)
- Add aria-current=\"page\" to active navigation tab for screen readers
- Add explicit focus indicators for keyboard navigation (2px blue outline)
- Use :focus-visible to prevent outline on mouse clicks
- Add tabindex=\"-1\" to <main> for skip link functionality

Accessibility improvements:
- Keyboard users can skip 11 navigation links
- Screen readers announce current page location
- Focus indicators meet WCAG 2.4.7 (visible focus)

WCAG Reference: 2.4.1 Bypass Blocks (skip link), 2.4.7 Focus Visible"

git push origin fix/wcag-touch-targets
git checkout main
git merge fix/wcag-touch-targets
git push origin main
```

**Phase 1 Success Criteria:**
- [x] Skip link appears on first Tab keypress
- [x] Skip link jumps to main content on Enter
- [x] Active tab has `aria-current="page"`
- [x] Focus indicators visible on keyboard navigation (2px blue outline)
- [x] Focus indicators hidden on mouse clicks (`:focus-visible`)
- [x] Lighthouse accessibility score ≥ 95 (run Lighthouse audit to verify)
- [x] No visual regressions on desktop or mobile

**Phase 1 Time Estimate:** 30 minutes total (15 + 5 + 10)
**Risk Level:** Low (additive changes, no breaking changes to existing functionality)

---

### Phase 2: Navigation Pattern Implementation (2-8 hours depending on choice)

**Implementation depends on chosen option from Decision Tree above**

**Checkpoint:** User must choose Option A (Hamburger), Option B (Collapsible), or Option C (Hybrid) before proceeding.

---

#### Option A: Hamburger Menu (RECOMMENDED - 4-6 hours)

**Goal:** Replace always-visible vertical navigation with hamburger menu + slide-in drawer to match industry standard and free 480px vertical space on mobile

**File changes:** `src/layouts/MainLayout.astro` (HTML, CSS, JavaScript all in single file)

---

##### Step 2A.1: Add Hamburger Menu Button HTML (30 minutes)

**Lines to modify:** 155-172 (entire `<header>` section)

**BEFORE (current header structure):**
```html
<header class="tab-header">
  <div class="tab-container">
    <a href={`${base}/`} class="tab-brand">C++ to C Transpiler</a>
    <nav class="tab-nav">
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
    </nav>
  </div>
</header>
```

**AFTER (add hamburger button and wrap nav in drawer):**
```html
<header class="tab-header">
  <div class="tab-container">
    <a href={`${base}/`} class="tab-brand">C++ to C Transpiler</a>

    <!-- Hamburger menu button (mobile only) -->
    <button
      class="mobile-menu-button"
      aria-label="Open navigation menu"
      aria-expanded="false"
      aria-controls="mobile-nav-drawer"
      type="button"
    >
      <svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" aria-hidden="true">
        <line x1="3" y1="6" x2="21" y2="6"></line>
        <line x1="3" y1="12" x2="21" y2="12"></line>
        <line x1="3" y1="18" x2="21" y2="18"></line>
      </svg>
      <span class="sr-only">Menu</span>
    </button>

    <!-- Desktop navigation (unchanged) -->
    <nav class="tab-nav tab-nav-desktop">
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
    </nav>
  </div>
</header>

<!-- Mobile navigation drawer -->
<div id="mobile-nav-drawer" class="mobile-nav-drawer" aria-hidden="true">
  <div class="mobile-nav-header">
    <span class="mobile-nav-title">Navigation</span>
    <button class="mobile-nav-close" aria-label="Close navigation menu" type="button">
      <svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" aria-hidden="true">
        <line x1="18" y1="6" x2="6" y2="18"></line>
        <line x1="6" y1="6" x2="18" y2="18"></line>
      </svg>
    </button>
  </div>
  <nav class="mobile-nav-content" role="navigation" aria-label="Main navigation">
    {tabs.map((tab) => {
      const isActive = normalizedCurrent === tab.path;
      return (
        <a
          href={tab.href}
          class={`mobile-nav-item ${isActive ? 'active' : ''}`}
          aria-current={isActive ? 'page' : undefined}
        >
          {tab.label}
        </a>
      );
    })}
  </nav>
</div>

<!-- Overlay backdrop -->
<div class="mobile-nav-overlay" aria-hidden="true"></div>
```

**Key elements:**
- **`.mobile-menu-button`**: Hamburger icon button (3 horizontal lines), hidden on desktop
- **`.tab-nav-desktop`**: Existing navigation, hidden on mobile, shown on desktop
- **`#mobile-nav-drawer`**: Fixed-position drawer that slides in from left
- **`.mobile-nav-close`**: X button inside drawer to close menu
- **`.mobile-nav-overlay`**: Semi-transparent backdrop behind drawer
- **`aria-expanded`**: Announces drawer open/closed state to screen readers
- **`aria-controls`**: Associates button with drawer element
- **`aria-hidden`**: Hides drawer/overlay from screen readers when closed

---

##### Step 2A.2: Add Hamburger Menu CSS (1-2 hours)

**Lines to modify:** Add extensive new CSS in `<style is:global>` block (around line 150, after existing `.tab` styles)

**CSS addition:**
```css
/* Screen reader only text */
.sr-only {
  position: absolute;
  width: 1px;
  height: 1px;
  padding: 0;
  margin: -1px;
  overflow: hidden;
  clip: rect(0, 0, 0, 0);
  white-space: nowrap;
  border: 0;
}

/* Mobile Menu Button */
.mobile-menu-button {
  display: none; /* Hidden by default (desktop) */
  background: none;
  border: none;
  color: white;
  padding: 0.75rem;
  cursor: pointer;
  min-width: 44px;
  min-height: 44px;
  align-items: center;
  justify-content: center;
  border-radius: 4px;
  transition: background-color 0.2s ease;
}

.mobile-menu-button:hover {
  background: rgba(255, 255, 255, 0.1);
}

.mobile-menu-button:focus-visible {
  outline: 2px solid #0066cc;
  outline-offset: 2px;
}

.mobile-menu-button svg {
  display: block;
}

/* Show hamburger button on mobile */
@media (max-width: 768px) {
  .mobile-menu-button {
    display: flex;
    margin-left: auto; /* Push to right side of header */
  }

  /* Hide desktop navigation on mobile */
  .tab-nav-desktop {
    display: none !important;
  }
}

/* Mobile Navigation Drawer */
.mobile-nav-drawer {
  position: fixed;
  top: 0;
  left: -280px; /* Start off-screen */
  width: 280px;
  height: 100vh;
  background: #2a2a2a;
  box-shadow: 2px 0 8px rgba(0, 0, 0, 0.3);
  z-index: 1000;
  overflow-y: auto;
  transition: left 0.25s ease-out;
}

.mobile-nav-drawer.open {
  left: 0; /* Slide in from left */
}

/* Mobile drawer header */
.mobile-nav-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 1rem;
  border-bottom: 1px solid #444;
}

.mobile-nav-title {
  color: white;
  font-size: 1.1rem;
  font-weight: 600;
}

.mobile-nav-close {
  background: none;
  border: none;
  color: white;
  padding: 0.5rem;
  cursor: pointer;
  min-width: 44px;
  min-height: 44px;
  display: flex;
  align-items: center;
  justify-content: center;
  border-radius: 4px;
  transition: background-color 0.2s ease;
}

.mobile-nav-close:hover {
  background: rgba(255, 255, 255, 0.1);
}

.mobile-nav-close:focus-visible {
  outline: 2px solid #0066cc;
  outline-offset: 2px;
}

/* Mobile navigation items */
.mobile-nav-content {
  display: flex;
  flex-direction: column;
  padding: 1rem;
  gap: 0.5rem;
}

.mobile-nav-item {
  display: block;
  padding: 0.75rem 1rem;
  background: #1a1a1a;
  color: #bbb;
  border: 1px solid #444;
  border-radius: 6px;
  text-decoration: none;
  transition: all 0.2s;
  min-height: 44px; /* WCAG touch target */
}

.mobile-nav-item:hover {
  background: #252525;
  color: white;
  text-decoration: none;
}

.mobile-nav-item.active {
  background: #0066cc;
  color: white;
  border-color: #0066cc;
  font-weight: 500;
}

.mobile-nav-item:focus-visible {
  outline: 2px solid #0066cc;
  outline-offset: 2px;
}

/* Overlay backdrop */
.mobile-nav-overlay {
  display: none; /* Hidden by default */
  position: fixed;
  top: 0;
  left: 0;
  width: 100%;
  height: 100%;
  background: rgba(0, 0, 0, 0.5);
  z-index: 999; /* Below drawer (1000) */
  opacity: 0;
  transition: opacity 0.2s ease-out;
}

.mobile-nav-overlay.visible {
  display: block;
  opacity: 1;
}

/* Hide drawer and overlay on desktop */
@media (min-width: 769px) {
  .mobile-nav-drawer,
  .mobile-nav-overlay,
  .mobile-menu-button {
    display: none !important;
  }
}

/* Prevent body scroll when menu open */
body.menu-open {
  overflow: hidden;
}
```

**CSS explanation:**
- **Drawer positioning**: `position: fixed` with `left: -280px` (off-screen) → `left: 0` (visible) via `.open` class
- **Smooth animation**: `transition: left 0.25s ease-out` for slide-in effect
- **Z-index layering**: Overlay at 999, drawer at 1000 (drawer appears above overlay)
- **Touch targets**: All interactive elements ≥ 44px height (WCAG AAA compliant)
- **Focus indicators**: Consistent 2px blue outline for keyboard navigation
- **Responsive breakpoint**: `@media (max-width: 768px)` shows mobile menu, `@media (min-width: 769px)` hides it

---

##### Step 2A.3: Add Menu Toggle JavaScript (1-2 hours)

**Lines to modify:** Insert new `<script>` block after line 197 (after existing WebAssembly script, before `</body>`)

**JavaScript addition:**
```html
<script>
  // Mobile Hamburger Menu Logic
  (() => {
    // Only run in browser (not during SSR)
    if (typeof window === 'undefined') return;

    const menuButton = document.querySelector('.mobile-menu-button');
    const closeButton = document.querySelector('.mobile-nav-close');
    const drawer = document.querySelector('.mobile-nav-drawer');
    const overlay = document.querySelector('.mobile-nav-overlay');
    const body = document.body;

    // Early return if elements not found (should never happen, but defensive coding)
    if (!menuButton || !closeButton || !drawer || !overlay) {
      console.warn('Mobile menu elements not found');
      return;
    }

    let isOpen = false;
    let focusedElementBeforeOpen = null;

    /**
     * Open mobile navigation drawer
     */
    const openMenu = () => {
      // Store currently focused element to restore later
      focusedElementBeforeOpen = document.activeElement;

      isOpen = true;
      drawer.classList.add('open');
      overlay.classList.add('visible');
      drawer.setAttribute('aria-hidden', 'false');
      menuButton.setAttribute('aria-expanded', 'true');
      menuButton.setAttribute('aria-label', 'Close navigation menu');
      body.classList.add('menu-open');

      // Focus first navigation link for keyboard users
      const firstLink = drawer.querySelector('.mobile-nav-item');
      if (firstLink) {
        // Small delay for animation to start
        setTimeout(() => firstLink.focus(), 100);
      }
    };

    /**
     * Close mobile navigation drawer
     */
    const closeMenu = () => {
      isOpen = false;
      drawer.classList.remove('open');
      overlay.classList.remove('visible');
      drawer.setAttribute('aria-hidden', 'true');
      menuButton.setAttribute('aria-expanded', 'false');
      menuButton.setAttribute('aria-label', 'Open navigation menu');
      body.classList.remove('menu-open');

      // Restore focus to button that opened menu (or previously focused element)
      if (focusedElementBeforeOpen && focusedElementBeforeOpen !== document.body) {
        focusedElementBeforeOpen.focus();
      } else {
        menuButton.focus();
      }
    };

    /**
     * Toggle menu open/closed
     */
    const toggleMenu = () => {
      isOpen ? closeMenu() : openMenu();
    };

    // Event Listeners

    // Open/close via hamburger button
    menuButton.addEventListener('click', toggleMenu);

    // Close via X button in drawer
    closeButton.addEventListener('click', closeMenu);

    // Close via overlay click
    overlay.addEventListener('click', closeMenu);

    // Close on Escape key
    document.addEventListener('keydown', (e) => {
      if (e.key === 'Escape' && isOpen) {
        closeMenu();
      }
    });

    // Close when navigation link is clicked (user is navigating to new page)
    drawer.querySelectorAll('.mobile-nav-item').forEach(link => {
      link.addEventListener('click', () => {
        // Small delay to allow navigation to start before closing
        setTimeout(closeMenu, 100);
      });
    });

    // Focus trap: keep focus within drawer when open
    drawer.addEventListener('keydown', (e) => {
      if (!isOpen || e.key !== 'Tab') return;

      const focusableElements = drawer.querySelectorAll(
        'button, a, input, select, textarea, [tabindex]:not([tabindex="-1"])'
      );
      const firstElement = focusableElements[0];
      const lastElement = focusableElements[focusableElements.length - 1];

      // Shift+Tab on first element → focus last element
      if (e.shiftKey && document.activeElement === firstElement) {
        e.preventDefault();
        lastElement.focus();
      }
      // Tab on last element → focus first element
      else if (!e.shiftKey && document.activeElement === lastElement) {
        e.preventDefault();
        firstElement.focus();
      }
    });

    // Close menu on viewport resize (user rotates device or resizes browser)
    let resizeTimer;
    window.addEventListener('resize', () => {
      clearTimeout(resizeTimer);
      resizeTimer = setTimeout(() => {
        // Close menu if viewport becomes desktop width
        if (window.innerWidth > 768 && isOpen) {
          closeMenu();
        }
      }, 250);
    });
  })();
</script>
```

**JavaScript explanation:**
- **Focus management**: Stores focused element before opening menu, restores on close (accessibility requirement)
- **Focus trap**: Tab cycles through drawer elements only when open (prevents focus escaping to page behind)
- **Keyboard support**: Escape closes menu, Tab/Shift+Tab navigate within drawer
- **Auto-close scenarios**: Link clicked, overlay clicked, Escape pressed, viewport resized to desktop
- **ARIA state management**: Updates `aria-expanded`, `aria-hidden`, `aria-label` attributes
- **Body scroll prevention**: Adds `.menu-open` class to `<body>` which sets `overflow: hidden`

---

##### Step 2A.4: Testing & Validation (1 hour)

**Create Playwright test file:** `tests/mobile-navigation.spec.ts`

```typescript
import { test, expect } from '@playwright/test';

const BASE_URL = 'http://localhost:4321/cpp-to-c-website/';

test.describe('Mobile Hamburger Navigation', () => {

  test('hamburger menu button appears on mobile viewport', async ({ page }) => {
    await page.setViewportSize({ width: 375, height: 667 });
    await page.goto(BASE_URL);

    const menuButton = page.locator('.mobile-menu-button');
    await expect(menuButton).toBeVisible();
    await expect(menuButton).toHaveAttribute('aria-expanded', 'false');
  });

  test('hamburger menu button hidden on desktop viewport', async ({ page }) => {
    await page.setViewportSize({ width: 1024, height: 768 });
    await page.goto(BASE_URL);

    const menuButton = page.locator('.mobile-menu-button');
    await expect(menuButton).not.toBeVisible();
  });

  test('drawer opens and closes on button click', async ({ page }) => {
    await page.setViewportSize({ width: 375, height: 667 });
    await page.goto(BASE_URL);

    const menuButton = page.locator('.mobile-menu-button');
    const drawer = page.locator('.mobile-nav-drawer');
    const overlay = page.locator('.mobile-nav-overlay');

    // Drawer should be hidden initially
    await expect(drawer).not.toHaveClass(/open/);
    await expect(drawer).toHaveAttribute('aria-hidden', 'true');

    // Click to open
    await menuButton.click();
    await expect(drawer).toHaveClass(/open/);
    await expect(drawer).toHaveAttribute('aria-hidden', 'false');
    await expect(menuButton).toHaveAttribute('aria-expanded', 'true');
    await expect(overlay).toHaveClass(/visible/);

    // Click overlay to close
    await overlay.click();
    await expect(drawer).not.toHaveClass(/open/);
    await expect(drawer).toHaveAttribute('aria-hidden', 'true');
    await expect(menuButton).toHaveAttribute('aria-expanded', 'false');
  });

  test('drawer closes on Escape key', async ({ page }) => {
    await page.setViewportSize({ width: 375, height: 667 });
    await page.goto(BASE_URL);

    // Open menu
    await page.locator('.mobile-menu-button').click();
    await expect(page.locator('.mobile-nav-drawer')).toHaveClass(/open/);

    // Press Escape
    await page.keyboard.press('Escape');
    await expect(page.locator('.mobile-nav-drawer')).not.toHaveClass(/open/);
  });

  test('drawer closes on navigation link click', async ({ page }) => {
    await page.setViewportSize({ width: 375, height: 667 });
    await page.goto(BASE_URL);

    // Open menu
    await page.locator('.mobile-menu-button').click();
    await expect(page.locator('.mobile-nav-drawer')).toHaveClass(/open/);

    // Click a navigation link
    await page.locator('.mobile-nav-item').first().click();

    // Wait for navigation and drawer to close
    await page.waitForTimeout(200);
    // Note: drawer will close but page will navigate, so test may complete before assertion
  });

  test('touch targets meet 44px minimum', async ({ page }) => {
    await page.setViewportSize({ width: 375, height: 667 });
    await page.goto(BASE_URL);

    // Open menu
    await page.locator('.mobile-menu-button').click();

    // Check menu button
    const menuButtonBox = await page.locator('.mobile-menu-button').boundingBox();
    expect(menuButtonBox!.width).toBeGreaterThanOrEqual(44);
    expect(menuButtonBox!.height).toBeGreaterThanOrEqual(44);

    // Check close button
    const closeButtonBox = await page.locator('.mobile-nav-close').boundingBox();
    expect(closeButtonBox!.width).toBeGreaterThanOrEqual(44);
    expect(closeButtonBox!.height).toBeGreaterThanOrEqual(44);

    // Check all navigation items
    const navItems = page.locator('.mobile-nav-item');
    const count = await navItems.count();

    for (let i = 0; i < count; i++) {
      const box = await navItems.nth(i).boundingBox();
      expect(box!.height).toBeGreaterThanOrEqual(44);
    }
  });

  test('focus management works correctly', async ({ page }) => {
    await page.setViewportSize({ width: 375, height: 667 });
    await page.goto(BASE_URL);

    const menuButton = page.locator('.mobile-menu-button');
    const drawer = page.locator('.mobile-nav-drawer');

    // Open menu
    await menuButton.click();

    // First nav item should receive focus
    const firstNavItem = page.locator('.mobile-nav-item').first();
    await expect(firstNavItem).toBeFocused();

    // Close menu via Escape
    await page.keyboard.press('Escape');

    // Focus should return to menu button
    await expect(menuButton).toBeFocused();
  });

  test('no horizontal overflow on mobile viewports', async ({ page }) => {
    const viewports = [
      { width: 320, height: 568 },  // iPhone SE
      { width: 375, height: 667 },  // iPhone 8
      { width: 414, height: 896 },  // iPhone 11 Pro Max
    ];

    for (const viewport of viewports) {
      await page.setViewportSize(viewport);
      await page.goto(BASE_URL);

      const bodyWidth = await page.evaluate(() => document.body.scrollWidth);
      const viewportWidth = viewport.width;

      expect(bodyWidth).toBeLessThanOrEqual(viewportWidth);
    }
  });
});

test.describe('Desktop Navigation (unchanged)', () => {

  test('desktop navigation visible and functional', async ({ page }) => {
    await page.setViewportSize({ width: 1024, height: 768 });
    await page.goto(BASE_URL);

    const desktopNav = page.locator('.tab-nav-desktop');
    await expect(desktopNav).toBeVisible();

    const tabs = page.locator('.tab');
    await expect(tabs.first()).toBeVisible();
  });

  test('desktop tab navigation maintains original behavior', async ({ page }) => {
    await page.setViewportSize({ width: 1024, height: 768 });
    await page.goto(BASE_URL);

    // Verify active tab styling
    const activeTab = page.locator('.tab.active');
    await expect(activeTab).toBeVisible();
    await expect(activeTab).toHaveAttribute('aria-current', 'page');
  });
});
```

**Manual testing checklist:**

**Viewport: 375px (iPhone 8)**
- [ ] Hamburger button appears in top-right of header
- [ ] Hamburger button has 44px+ touch target (measured in DevTools)
- [ ] Desktop tab navigation is hidden
- [ ] Clicking hamburger button opens drawer from left
- [ ] Drawer slides in smoothly (250ms animation)
- [ ] Overlay appears behind drawer with semi-transparent black
- [ ] First navigation link receives focus when drawer opens
- [ ] Navigation items have 44px+ height
- [ ] Active navigation item highlighted (blue background)
- [ ] Clicking navigation item closes drawer and navigates
- [ ] Clicking overlay closes drawer
- [ ] Pressing Escape closes drawer
- [ ] Focus returns to hamburger button when drawer closes
- [ ] Tab key cycles through drawer items only (focus trap)
- [ ] Shift+Tab cycles backward through drawer items
- [ ] No horizontal overflow or scrolling
- [ ] Body scroll is prevented when drawer open

**Viewport: 768px (breakpoint boundary)**
- [ ] Hamburger button still visible
- [ ] Drawer functionality works correctly

**Viewport: 769px (desktop)**
- [ ] Hamburger button hidden
- [ ] Desktop tab navigation visible and functional
- [ ] No drawer or overlay elements visible
- [ ] Original desktop navigation behavior unchanged

**Viewport: 1024px (desktop)**
- [ ] Original horizontal tab navigation works
- [ ] All 11 tabs visible (or wrapping appropriately)
- [ ] Active tab styling intact

**Accessibility validation:**
- [ ] Run Lighthouse accessibility audit (target score: 95+)
- [ ] Test with VoiceOver (iOS) or NVDA (Windows)
  - [ ] Hamburger button announces "Open navigation menu, button"
  - [ ] Drawer announces "navigation, region" when opened
  - [ ] Navigation items announce with aria-current for active page
  - [ ] Close button announces "Close navigation menu, button"
- [ ] Test keyboard-only navigation (no mouse)
  - [ ] Tab to hamburger button → Enter to open
  - [ ] Tab cycles through nav items
  - [ ] Escape closes drawer
  - [ ] Focus returns to button
- [ ] Verify color contrast ratios (DevTools contrast checker)
  - [ ] White text on #2a2a2a background ≥ 4.5:1
  - [ ] Blue active state (#0066cc) ≥ 4.5:1 with white text

**Performance validation:**
- [ ] Page load time remains < 100ms (localhost)
- [ ] No layout shift (CLS = 0) when drawer opens
- [ ] Drawer animation is smooth at 60fps
- [ ] Bundle size increase < 5KB (check build output)
- [ ] No console errors or warnings
- [ ] JavaScript executes without errors in browser DevTools

**Cross-browser testing (optional but recommended):**
- [ ] Chrome 90+ (modern)
- [ ] Firefox 88+ (modern)
- [ ] Safari 14+ (modern)
- [ ] Mobile Safari iOS 12+ (real device)
- [ ] Chrome Android 90+ (real device)

---

**Phase 2A Git Workflow:**
```bash
# Create feature branch
git checkout develop
git pull origin develop
git checkout -b feat/mobile-hamburger-menu

# Make all changes to MainLayout.astro (HTML, CSS, JavaScript)
# Create tests/mobile-navigation.spec.ts

# Test locally
npm run dev
# Open http://localhost:4321/cpp-to-c-website/ in browser
# Test manually at 375px, 768px, 1024px viewports

# Run Playwright tests
npm test

# Build to verify no errors
npm run build

# Commit changes
git add src/layouts/MainLayout.astro tests/mobile-navigation.spec.ts
git commit -m "feat: implement hamburger navigation menu for mobile devices

- Add hamburger menu button (44px touch target, hamburger icon)
- Create slide-in drawer from left (280px width, smooth 250ms animation)
- Add semi-transparent overlay backdrop (rgba(0,0,0,0.5))
- Implement focus management (focus trap, restore on close)
- Add keyboard navigation (Escape to close, Tab cycling)
- Auto-close on link click, overlay click, Escape key, viewport resize
- Maintain desktop horizontal tab navigation unchanged (≥ 769px)
- Add Playwright tests for open/close/keyboard/touch-target validation

Mobile UX improvements:
- Frees 480px vertical space on mobile (content immediately visible)
- Matches industry standard (MDN, TypeScript, Rust all use hamburger)
- All touch targets ≥ 44px (WCAG AAA compliant)
- ARIA attributes for screen reader support

WCAG Compliance: 2.5.5 Touch Target Size, 2.4.3 Focus Order, 4.1.2 Name/Role/Value

Research reference: .prompts/008-mobile-friendly-ux-research/mobile-friendly-ux-research.md"

git push origin feat/mobile-hamburger-menu

# Merge to main (no PR per CLAUDE.md)
git checkout main
git merge feat/mobile-hamburger-menu
git push origin main

# GitHub Actions will auto-deploy to Pages
# Monitor deployment at https://github.com/[username]/[repo]/actions

# Smoke test on deployed site
# Visit https://[username].github.io/cpp-to-c-website/
# Test hamburger menu on real mobile device if possible
```

---

**Phase 2A Success Criteria:**
- [x] Mobile navigation functional on 320px - 768px viewports
- [x] Desktop navigation unchanged and functional on ≥ 769px viewports
- [x] Hamburger button has 44px+ touch target
- [x] All mobile navigation items have 44px+ height
- [x] Drawer slides in smoothly from left (no janky animation)
- [x] Overlay appears/disappears with smooth fade
- [x] Focus management works (focus trap, restore on close)
- [x] Keyboard navigation works (Tab, Shift+Tab, Escape)
- [x] Auto-close on link click, overlay click, Escape, resize
- [x] No horizontal overflow on any viewport
- [x] Performance maintained (load < 100ms, CLS = 0)
- [x] All Playwright tests passing
- [x] Lighthouse accessibility score ≥ 95
- [x] No console errors or warnings
- [x] Deployed to production successfully

**Option A Time Estimate:** 4-6 hours total
- Step 2A.1 (HTML): 30 minutes
- Step 2A.2 (CSS): 1-2 hours
- Step 2A.3 (JavaScript): 1-2 hours
- Step 2A.4 (Testing): 1 hour

**Option A Risk Level:** Medium
- JavaScript adds complexity (focus management, event handling)
- Animation performance depends on browser rendering
- Focus trap requires careful implementation
- Cross-browser testing recommended

**Mitigation strategies:**
- Use feature detection for JavaScript availability
- Provide fallback: if JavaScript fails, show vertical navigation (progressive enhancement)
- Test on real devices (iOS Safari, Chrome Android)
- Monitor for console errors in production

---

#### Option B: Collapsible Navigation (ALTERNATIVE - 2-3 hours)

**Goal:** Keep current vertical navigation pattern but collapse by default on mobile with expand/collapse button (progressive disclosure)

**Why Option B:** If Option A timeline (4-6 hours) is too long, Option B provides functional improvement with minimal implementation time. Can upgrade to Option A in future sprint.

**File changes:** `src/layouts/MainLayout.astro` (HTML, CSS, minimal JavaScript)

---

##### Step 2B.1: Add Collapse Button HTML (30 minutes)

**Lines to modify:** 155-172 (header section)

**BEFORE (current header):**
```html
<header class="tab-header">
  <div class="tab-container">
    <a href={`${base}/`} class="tab-brand">C++ to C Transpiler</a>
    <nav class="tab-nav">
      {/* existing tabs */}
    </nav>
  </div>
</header>
```

**AFTER (add collapse button):**
```html
<header class="tab-header">
  <div class="tab-container">
    <a href={`${base}/`} class="tab-brand">C++ to C Transpiler</a>

    <!-- Collapse toggle button (mobile only) -->
    <button
      class="nav-toggle-button"
      aria-label="Toggle navigation"
      aria-expanded="false"
      aria-controls="tab-nav"
      type="button"
    >
      <span>Menu</span>
      <svg class="nav-toggle-icon" xmlns="http://www.w3.org/2000/svg" width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" aria-hidden="true">
        <polyline points="6 9 12 15 18 9"></polyline>
      </svg>
    </button>

    <nav id="tab-nav" class="tab-nav" aria-hidden="true">
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
    </nav>
  </div>
</header>
```

**Key elements:**
- **`.nav-toggle-button`**: "Menu" button with chevron icon (down/up), hidden on desktop
- **`aria-expanded="false"`**: Initially collapsed state
- **`aria-controls="tab-nav"`**: Associates button with navigation element
- **Chevron icon**: Rotates when expanded (CSS transform)

---

##### Step 2B.2: Add Collapsible Navigation CSS (1 hour)

**Lines to modify:** Add new CSS in `<style is:global>` block (around line 150)

**CSS addition:**
```css
/* Navigation Toggle Button (Mobile Only) */
.nav-toggle-button {
  display: none; /* Hidden on desktop */
  background: #1a1a1a;
  border: 1px solid #444;
  color: white;
  padding: 0.75rem 1rem;
  cursor: pointer;
  min-height: 44px;
  align-items: center;
  justify-content: space-between;
  gap: 0.5rem;
  border-radius: 6px;
  transition: background-color 0.2s ease;
  font-size: 1rem;
  width: 100%;
}

.nav-toggle-button:hover {
  background: #252525;
}

.nav-toggle-button:focus-visible {
  outline: 2px solid #0066cc;
  outline-offset: 2px;
}

.nav-toggle-icon {
  transition: transform 0.2s ease;
  flex-shrink: 0;
}

.nav-toggle-button[aria-expanded="true"] .nav-toggle-icon {
  transform: rotate(180deg); /* Flip chevron when expanded */
}

/* Mobile: Collapse navigation by default */
@media (max-width: 768px) {
  .nav-toggle-button {
    display: flex;
    margin-left: auto; /* Push to right side */
  }

  .tab-nav {
    display: none; /* Hidden by default */
    width: 100%;
    flex-direction: column;
    margin-top: 0.5rem;
    gap: 0.5rem;
  }

  .tab-nav.expanded {
    display: flex; /* Show when expanded */
  }

  .tab {
    width: 100%;
    border-radius: 6px;
    border: 1px solid #444;
    text-align: left;
  }
}

/* Desktop: Hide toggle button, show navigation */
@media (min-width: 769px) {
  .nav-toggle-button {
    display: none !important;
  }

  .tab-nav {
    display: flex !important; /* Always visible on desktop */
  }
}
```

**CSS explanation:**
- **Collapsed by default**: `.tab-nav { display: none; }` on mobile
- **Expand on click**: `.tab-nav.expanded { display: flex; }` via JavaScript class toggle
- **Button styling**: Full-width button with chevron icon that rotates 180° when expanded
- **Vertical layout**: Navigation items stack vertically when expanded
- **Responsive**: Toggle button hidden on desktop (≥ 769px)

---

##### Step 2B.3: Add Toggle JavaScript (30 minutes)

**Lines to modify:** Add new `<script>` block after line 197 (before existing WebAssembly script or after it)

**JavaScript addition:**
```html
<script>
  // Collapsible Navigation Toggle
  (() => {
    if (typeof window === 'undefined') return;

    const toggleButton = document.querySelector('.nav-toggle-button');
    const nav = document.getElementById('tab-nav');

    if (!toggleButton || !nav) return;

    let isExpanded = false;

    // Optional: Load saved preference from localStorage
    const savedState = localStorage.getItem('navExpanded');
    if (savedState === 'true') {
      isExpanded = true;
      nav.classList.add('expanded');
      nav.setAttribute('aria-hidden', 'false');
      toggleButton.setAttribute('aria-expanded', 'true');
    }

    /**
     * Toggle navigation expanded/collapsed
     */
    const toggleNav = () => {
      isExpanded = !isExpanded;

      if (isExpanded) {
        nav.classList.add('expanded');
        nav.setAttribute('aria-hidden', 'false');
        toggleButton.setAttribute('aria-expanded', 'true');
      } else {
        nav.classList.remove('expanded');
        nav.setAttribute('aria-hidden', 'true');
        toggleButton.setAttribute('aria-expanded', 'false');
      }

      // Save preference to localStorage
      localStorage.setItem('navExpanded', isExpanded.toString());
    };

    // Event listener
    toggleButton.addEventListener('click', toggleNav);

    // Optional: Close on navigation link click
    nav.querySelectorAll('.tab').forEach(link => {
      link.addEventListener('click', () => {
        if (window.innerWidth <= 768) {
          // Collapse navigation when user navigates on mobile
          isExpanded = true; // Will be toggled to false
          toggleNav();
        }
      });
    });
  })();
</script>
```

**JavaScript explanation:**
- **Simple toggle**: Adds/removes `.expanded` class on `<nav>` element
- **ARIA state management**: Updates `aria-expanded` and `aria-hidden` attributes
- **localStorage persistence**: Remembers user preference across page loads (optional feature)
- **Auto-collapse**: Collapses menu when navigation link clicked on mobile
- **Minimal complexity**: ~40 lines of code vs ~100+ for hamburger menu

---

##### Step 2B.4: Testing & Validation (30 minutes)

**Playwright tests** (add to `tests/mobile-navigation.spec.ts`):
```typescript
test.describe('Collapsible Navigation (Option B)', () => {

  test('toggle button appears on mobile', async ({ page }) => {
    await page.setViewportSize({ width: 375, height: 667 });
    await page.goto(BASE_URL);

    const toggleButton = page.locator('.nav-toggle-button');
    await expect(toggleButton).toBeVisible();
    await expect(toggleButton).toHaveAttribute('aria-expanded', 'false');
  });

  test('navigation expands and collapses on button click', async ({ page }) => {
    await page.setViewportSize({ width: 375, height: 667 });
    await page.goto(BASE_URL);

    const toggleButton = page.locator('.nav-toggle-button');
    const nav = page.locator('#tab-nav');

    // Navigation hidden initially
    await expect(nav).not.toBeVisible();
    await expect(nav).toHaveAttribute('aria-hidden', 'true');

    // Click to expand
    await toggleButton.click();
    await expect(nav).toBeVisible();
    await expect(nav).toHaveAttribute('aria-hidden', 'false');
    await expect(toggleButton).toHaveAttribute('aria-expanded', 'true');

    // Click to collapse
    await toggleButton.click();
    await expect(nav).not.toBeVisible();
    await expect(nav).toHaveAttribute('aria-hidden', 'true');
    await expect(toggleButton).toHaveAttribute('aria-expanded', 'false');
  });

  test('toggle button hidden on desktop', async ({ page }) => {
    await page.setViewportSize({ width: 1024, height: 768 });
    await page.goto(BASE_URL);

    await expect(page.locator('.nav-toggle-button')).not.toBeVisible();
    await expect(page.locator('.tab-nav')).toBeVisible(); // Always visible on desktop
  });
});
```

**Manual testing checklist:**

**Viewport: 375px**
- [ ] "Menu" toggle button visible in header
- [ ] Toggle button has 44px+ height
- [ ] Navigation hidden by default
- [ ] Clicking toggle button expands navigation
- [ ] Chevron icon rotates 180° when expanded
- [ ] Navigation items stack vertically when expanded
- [ ] All navigation items have 44px+ height
- [ ] Clicking navigation item collapses menu and navigates
- [ ] User preference persisted (refresh page → menu stays expanded if was expanded)

**Viewport: 1024px (desktop)**
- [ ] Toggle button hidden
- [ ] Navigation always visible (horizontal tabs)
- [ ] Original desktop behavior unchanged

**Accessibility:**
- [ ] Toggle button announces "Toggle navigation, button"
- [ ] `aria-expanded` state updates correctly
- [ ] Keyboard navigation works (Tab to button, Enter to toggle)

---

**Phase 2B Commit:**
```bash
git checkout develop
git checkout -b feat/collapsible-navigation

git add src/layouts/MainLayout.astro tests/mobile-navigation.spec.ts
git commit -m "feat: implement collapsible navigation for mobile devices

- Add toggle button with chevron icon (44px touch target)
- Collapse navigation by default on mobile (< 768px)
- Expand/collapse on button click with smooth animation
- Save user preference to localStorage
- Auto-collapse on navigation link click
- Maintain desktop horizontal tab navigation unchanged (≥ 769px)

Mobile UX improvements:
- Progressive disclosure: content visible above fold by default
- One-tap access to full navigation (vs hamburger's slide-in drawer)
- Simpler implementation than hamburger menu (2-3hr vs 4-6hr)

WCAG Compliance: 2.5.5 Touch Target Size, 4.1.2 Name/Role/Value (ARIA)"

git push origin feat/collapsible-navigation
git checkout main
git merge feat/collapsible-navigation
git push origin main
```

**Option B Time Estimate:** 2-3 hours total
- Step 2B.1 (HTML): 30 minutes
- Step 2B.2 (CSS): 1 hour
- Step 2B.3 (JavaScript): 30 minutes
- Step 2B.4 (Testing): 30 minutes

**Option B Risk Level:** Low
- Minimal JavaScript (simple toggle logic)
- Maintains current navigation structure
- Fewer edge cases than hamburger menu
- No complex focus management required

**Option B vs Option A Trade-offs:**

| Factor | Option A (Hamburger) | Option B (Collapsible) |
|--------|---------------------|------------------------|
| **Time to implement** | 4-6 hours | 2-3 hours |
| **Vertical space saved** | 480px (drawer off-screen) | Variable (collapsed by default) |
| **Industry alignment** | High (MDN, TypeScript, Rust) | Low (non-standard pattern) |
| **User familiarity** | High (standard mobile pattern) | Medium (less common) |
| **JavaScript complexity** | High (focus trap, animations) | Low (simple toggle) |
| **Accessibility** | Excellent (full focus management) | Good (basic ARIA) |
| **Upgrade path** | N/A (final state) | Can upgrade to Option A later |

**Recommendation:** Use Option B if timeline is critical, but plan to upgrade to Option A in future sprint for better UX alignment.

---

#### Option C: Sticky Header + Hamburger (FUTURE ENHANCEMENT - 6-8 hours)

**Goal:** Combine sticky header positioning with hamburger menu for always-accessible navigation

**Why Option C:** Best user experience (navigation always accessible while scrolling) but highest implementation complexity. Recommended only if polish is critical and time allows.

**Implementation overview:**
1. Implement Option A (Hamburger Menu) - 4-6 hours
2. Add sticky positioning to header - 1-2 hours additional
3. Handle scroll-based layout shifts - 30 minutes
4. Test across viewports and scroll scenarios - 30 minutes

**Additional CSS (after Option A is complete):**
```css
.tab-header {
  position: sticky;
  top: 0;
  z-index: 1001; /* Above drawer (1000) and overlay (999) */
  background: #2a2a2a; /* Ensure opaque background */
  box-shadow: 0 2px 4px rgba(0, 0, 0, 0.1); /* Subtle shadow when scrolling */
}

/* Optional: Hide shadow when at top of page */
.tab-header.at-top {
  box-shadow: none;
}
```

**Additional JavaScript:**
```javascript
// Detect scroll position to toggle shadow
let lastScrollY = window.scrollY;

window.addEventListener('scroll', () => {
  const header = document.querySelector('.tab-header');
  if (window.scrollY > 0) {
    header.classList.remove('at-top');
  } else {
    header.classList.add('at-top');
  }
});
```

**Testing considerations:**
- [ ] Header stays visible when scrolling down
- [ ] Header doesn't overlap content (z-index correct)
- [ ] Drawer appears above sticky header when opened
- [ ] Overlay covers entire viewport including sticky header
- [ ] No layout shift when header becomes sticky
- [ ] Performance: scrolling remains smooth (no jank)

**Option C Time Estimate:** 6-8 hours (Option A + sticky implementation)
**Option C Risk Level:** Medium-High (complexity of sticky + drawer interaction)

**Recommendation:** Defer Option C to Phase 3 (Future Polish) unless sticky navigation is critical requirement.

---

### Phase 3: Performance & Polish (Future - 2-3 hours, deferred)

**Goal:** Additional refinements and optimizations beyond core mobile UX requirements

**Why defer:** Phase 0-2 address all critical issues (WCAG compliance, navigation UX). Phase 3 improvements are "nice to have" and can be scheduled for future sprint.

---

#### Enhancement 3.1: Font Loading Optimization (30 minutes)

**Current state:** Uses system fonts (optimal for performance)

**Potential improvement:** If custom fonts added in future, implement font-display strategy

```css
@font-face {
  font-family: 'CustomFont';
  src: url('/fonts/custom.woff2') format('woff2');
  font-display: swap; /* Show system font while loading */
}
```

**Defer rationale:** Not needed unless custom fonts are added

---

#### Enhancement 3.2: Lazy Loading for Large Tables (1 hour)

**Current state:** Benchmarks page has 5 tables, some requiring horizontal scroll

**Potential improvement:** Lazy load tables below fold using Intersection Observer

```javascript
const observer = new IntersectionObserver((entries) => {
  entries.forEach(entry => {
    if (entry.isIntersecting) {
      const table = entry.target;
      table.classList.add('loaded');
      observer.unobserve(table);
    }
  });
});

document.querySelectorAll('.benchmark-table').forEach(table => {
  observer.observe(table);
});
```

**Impact:** Faster initial page load on data-heavy pages
**Defer rationale:** Current performance excellent (81ms FCP), optimization premature

---

#### Enhancement 3.3: Sticky First Column for Wide Tables (2 hours)

**Current state:** Tables use `overflow-x: auto` for horizontal scrolling

**Potential improvement:** Make first column sticky for context while scrolling

```css
.benchmark-table tbody tr td:first-child,
.benchmark-table thead tr th:first-child {
  position: sticky;
  left: 0;
  background: white;
  z-index: 1;
  box-shadow: 2px 0 4px rgba(0, 0, 0, 0.1);
}
```

**Impact:** Better UX when scrolling wide tables horizontally
**Effort:** 2 hours (requires table restructuring, testing)
**Defer rationale:** Nice to have, not critical for mobile UX

---

#### Enhancement 3.4: Dark Mode Toggle (4-6 hours)

**Potential improvement:** Add dark/light mode toggle (popular for developer docs)

**Implementation:**
- Design dark color scheme
- Create toggle UI component
- Implement localStorage persistence
- Add `prefers-color-scheme` media query
- Update all color values with CSS variables

**Defer rationale:** Not related to mobile UX research findings, separate feature request

---

#### Enhancement 3.5: WebAssembly Playground Performance Testing (30 minutes)

**Action:** Run Lighthouse on playground page with slow 3G throttling

**Why:** Research did not test playground page (WebAssembly-heavy)

**Testing steps:**
1. Open Chrome DevTools
2. Navigate to Playground page
3. Enable "Slow 3G" throttling
4. Run Lighthouse performance audit
5. Identify WebAssembly loading bottlenecks
6. Consider code splitting or lazy loading WASM

**Defer rationale:** Playground is separate feature, may need dedicated performance sprint

---

**Phase 3 Priority Matrix:**

| Enhancement | Impact | Effort | Priority | When to Implement |
|-------------|--------|--------|----------|-------------------|
| Font loading optimization | Low | 30min | P3 | Only if custom fonts added |
| Lazy load tables | Medium | 1hr | P2 | If performance degrades |
| Sticky first column | Medium | 2hr | P2 | After user feedback |
| Dark mode | High | 4-6hr | P1 | Separate feature sprint |
| WASM playground perf | High | 30min+ | P1 | Next sprint (playground focus) |

**Recommendation:** Complete Phase 0-2 first, then reassess Phase 3 based on user feedback and analytics.

---

## Testing Strategy

### Automated Tests (Playwright)

**Test file location:** `tests/mobile-navigation.spec.ts` (create new file)

**Test coverage:**

**Phase 0 tests:**
```typescript
test('all navigation tabs meet WCAG touch target minimum (44px)', async ({ page }) => {
  const viewports = [
    { width: 320, height: 568 },
    { width: 375, height: 667 },
    { width: 414, height: 896 },
  ];

  for (const viewport of viewports) {
    await page.setViewportSize(viewport);
    await page.goto(BASE_URL);

    const tabs = page.locator('.tab');
    const count = await tabs.count();

    for (let i = 0; i < count; i++) {
      const box = await tabs.nth(i).boundingBox();
      expect(box!.height).toBeGreaterThanOrEqual(44);
    }
  }
});
```

**Phase 1 tests:**
```typescript
test('skip link appears on first Tab keypress', async ({ page }) => {
  await page.goto(BASE_URL);

  const skipLink = page.locator('.skip-link');

  // Skip link not visible initially
  await expect(skipLink).not.toBeVisible();

  // Press Tab
  await page.keyboard.press('Tab');

  // Skip link should now be visible and focused
  await expect(skipLink).toBeVisible();
  await expect(skipLink).toBeFocused();
});

test('skip link jumps to main content', async ({ page }) => {
  await page.goto(BASE_URL);

  await page.keyboard.press('Tab'); // Focus skip link
  await page.keyboard.press('Enter'); // Activate skip link

  const main = page.locator('#main-content');
  await expect(main).toBeFocused();
});

test('active tab has aria-current="page"', async ({ page }) => {
  await page.goto(BASE_URL);

  const activeTab = page.locator('.tab.active');
  await expect(activeTab).toHaveAttribute('aria-current', 'page');
});
```

**Phase 2A tests:** (See Step 2A.4 above for full hamburger menu tests)

**Phase 2B tests:** (See Step 2B.4 above for collapsible navigation tests)

**Test execution:**
```bash
# Run all tests
npm test

# Run specific test file
npx playwright test tests/mobile-navigation.spec.ts

# Run tests in UI mode (interactive)
npx playwright test --ui

# Run tests in headed mode (see browser)
npx playwright test --headed

# Generate test report
npx playwright test --reporter=html
```

---

### Manual Testing Checklist

**Cross-viewport validation:**

| Viewport | Size | Device | Test Scenarios |
|----------|------|--------|---------------|
| **320px** | 320×568 | iPhone SE | [ ] Touch targets ≥44px<br>[ ] Skip link works<br>[ ] Navigation functional<br>[ ] No horizontal overflow |
| **375px** | 375×667 | iPhone 8 | [ ] Touch targets ≥44px<br>[ ] Menu opens/closes<br>[ ] Focus management<br>[ ] No overflow |
| **414px** | 414×896 | iPhone 11 Pro Max | [ ] Touch targets ≥44px<br>[ ] Navigation responsive<br>[ ] Spacing appropriate |
| **768px** | 768×1024 | iPad Portrait | [ ] Breakpoint boundary<br>[ ] Mobile pattern active<br>[ ] Layout intact |
| **1024px** | 1024×768 | iPad Landscape | [ ] Desktop mode active<br>[ ] Horizontal tabs work<br>[ ] Original behavior |

**Accessibility validation:**

**Lighthouse audit:**
- [ ] Run Lighthouse in Chrome DevTools
- [ ] Accessibility score ≥ 95
- [ ] No critical accessibility issues
- [ ] Touch target warnings resolved
- [ ] Color contrast passes

**Screen reader testing:**

**VoiceOver (macOS/iOS):**
- [ ] Enable VoiceOver (Cmd+F5)
- [ ] Navigate with VO+Right Arrow through page
- [ ] Skip link announces "Skip to main content, link"
- [ ] Navigation tabs announce "Home, link, current page" (for active tab)
- [ ] Hamburger button announces "Open navigation menu, button"
- [ ] Drawer announces "navigation, region"

**NVDA (Windows):**
- [ ] Enable NVDA
- [ ] Navigate with Down Arrow
- [ ] Verify same announcements as VoiceOver
- [ ] Test in Firefox and Chrome

**Keyboard-only navigation:**
- [ ] Disconnect mouse
- [ ] Tab through entire page
- [ ] Skip link appears and works (first Tab → Enter)
- [ ] All interactive elements reachable
- [ ] Focus indicators visible (2px blue outline)
- [ ] Hamburger menu opens with Enter
- [ ] Navigation drawer accessible with Tab
- [ ] Escape closes drawer
- [ ] Focus returns to button after close

**Color contrast validation:**
- [ ] Chrome DevTools → Inspect element → Check "Show CSS Overview"
- [ ] Run contrast checker on:
  - [ ] White text on #2a2a2a (navigation background) ≥ 4.5:1
  - [ ] #bbb text on #1a1a1a (tab background) ≥ 4.5:1
  - [ ] White text on #0066cc (active tab/link) ≥ 4.5:1
  - [ ] #333 text on white (body text) ≥ 4.5:1

**Performance validation:**

**Localhost testing:**
- [ ] Load time < 100ms (baseline)
- [ ] First Contentful Paint < 200ms
- [ ] No layout shift (CLS = 0)
- [ ] Drawer animation smooth at 60fps
- [ ] No janky scrolling

**Production testing (after deployment):**
- [ ] Run Lighthouse on deployed URL
- [ ] Performance score ≥ 90
- [ ] Test with "Slow 3G" throttling
  - [ ] Load time < 3 seconds
  - [ ] Interactive within 5 seconds
- [ ] Check bundle size increase
  - [ ] JavaScript bundle < 5KB increase (if hamburger menu)
  - [ ] No new images or fonts added

**Cross-browser testing:**

| Browser | Version | Platform | Tests |
|---------|---------|----------|-------|
| Chrome | 120+ | Desktop | [ ] Full test suite |
| Firefox | 115+ | Desktop | [ ] Full test suite |
| Safari | 17+ | macOS | [ ] Full test suite<br>[ ] :focus-visible support |
| Mobile Safari | iOS 15+ | iPhone | [ ] Real device test<br>[ ] Touch interactions<br>[ ] Viewport behavior |
| Chrome Android | 120+ | Android | [ ] Real device test<br>[ ] Touch targets<br>[ ] Performance |

**Real device testing (recommended):**
- [ ] Borrow iPhone or Android device
- [ ] Navigate to deployed site
- [ ] Test hamburger menu touch interactions
- [ ] Verify 44px touch targets feel natural
- [ ] Check drawer slide animation smoothness
- [ ] Test landscape/portrait rotation
- [ ] Verify no zoom required to read text

---

## Deployment Plan

### Pre-deployment Checklist

**Code quality:**
- [ ] All Playwright tests passing (`npm test`)
- [ ] Build succeeds without errors (`npm run build`)
- [ ] No console errors in browser DevTools
- [ ] No TypeScript errors (`npm run astro check`)
- [ ] Code follows project style (linting passes)

**Testing:**
- [ ] Manual testing complete on 5 viewports (320, 375, 414, 768, 1024)
- [ ] Accessibility validation complete (Lighthouse ≥ 95)
- [ ] Keyboard navigation tested
- [ ] Screen reader tested (VoiceOver or NVDA)
- [ ] Real device testing (if available)

**Performance:**
- [ ] Lighthouse performance score maintained or improved
- [ ] No layout shift (CLS = 0)
- [ ] Bundle size increase acceptable (< 5KB if JavaScript added)
- [ ] Load time < 100ms (localhost baseline)

**Git workflow:**
- [ ] All changes committed with descriptive messages
- [ ] Commit messages follow conventional commits format
- [ ] Branch merged to main (no PR per CLAUDE.md)
- [ ] No merge conflicts

---

### Deployment Steps

**Phase 0 + Phase 1 (bundled deployment - recommended):**
```bash
# Start from develop branch
git checkout develop
git pull origin develop

# Create feature branch
git checkout -b fix/mobile-ux-phase-0-1

# Make Phase 0 changes (touch target fix)
# Edit src/layouts/MainLayout.astro line 121
# Change padding: 0.5rem 1rem → padding: 0.625rem 1rem
# Add min-height: 44px

# Make Phase 1 changes (skip link, ARIA, focus indicators)
# Add skip link HTML and CSS
# Add aria-current attribute
# Add focus indicator CSS

# Test locally
npm run dev
# Open http://localhost:4321/cpp-to-c-website/
# Test at 375px and 1024px viewports
# Verify touch targets ≥ 44px
# Test skip link (Tab → Enter)
# Test focus indicators (Tab through navigation)

# Build
npm run build
# Verify build succeeds

# Commit changes
git add src/layouts/MainLayout.astro
git commit -m "fix: mobile UX improvements - WCAG compliance and accessibility

Phase 0: Touch target fix
- Increase .tab padding from 0.5rem to 0.625rem (43px → 47px height)
- Add min-height: 44px explicit constraint
- Fixes WCAG 2.5.5 Level AAA violation on 10/11 navigation links

Phase 1: Accessibility quick wins
- Add skip navigation link (keyboard users can skip 11 nav links)
- Add aria-current=\"page\" to active tab (screen reader support)
- Add explicit focus indicators (2px blue outline, :focus-visible)
- Add tabindex=\"-1\" to <main> for skip link functionality

WCAG compliance achieved:
- 2.5.5 Touch Target Size (Level AAA)
- 2.4.1 Bypass Blocks (skip link)
- 2.4.7 Focus Visible
- 4.1.2 Name/Role/Value (ARIA)

Research reference: .prompts/008-mobile-friendly-ux-research/
Total time: 35 minutes (5 min Phase 0 + 30 min Phase 1)"

# Push to remote
git push origin fix/mobile-ux-phase-0-1

# Merge to main (no PR per CLAUDE.md)
git checkout main
git pull origin main
git merge fix/mobile-ux-phase-0-1
git push origin main

# GitHub Actions will automatically deploy to GitHub Pages
# Monitor deployment: https://github.com/[username]/[repo]/actions

# Wait for deployment to complete (usually 2-3 minutes)
# Verify deployment succeeded (green checkmark in Actions tab)

# Smoke test deployed site
# Visit: https://[username].github.io/cpp-to-c-website/
# Test skip link (Tab → Enter)
# Inspect touch targets in DevTools (should be ≥ 44px)
# Test on real mobile device if available

# Clean up feature branch (optional)
git branch -d fix/mobile-ux-phase-0-1
git push origin --delete fix/mobile-ux-phase-0-1
```

---

**Phase 2 (separate deployment - Option A Hamburger Menu):**
```bash
# After Phase 0+1 deployed and stable
git checkout develop
git pull origin develop

# Create feature branch
git checkout -b feat/mobile-hamburger-menu

# Make Phase 2A changes (see Step 2A.1-2A.3 above)
# Edit src/layouts/MainLayout.astro extensively
# Add hamburger button HTML
# Add drawer and overlay HTML
# Add extensive CSS (~200 lines)
# Add JavaScript (~100 lines)

# Create Playwright tests
# Create tests/mobile-navigation.spec.ts
# Add hamburger menu tests (see Step 2A.4)

# Test locally EXTENSIVELY
npm run dev
# Test on 320px, 375px, 414px, 768px, 1024px
# Test all scenarios:
#   - Menu opens/closes
#   - Overlay click closes
#   - Escape closes
#   - Focus management
#   - Link click closes and navigates
#   - Desktop navigation unchanged

# Run automated tests
npm test
# Verify all tests pass

# Build
npm run build
# Verify build succeeds
# Check bundle size increase

# Commit
git add src/layouts/MainLayout.astro tests/mobile-navigation.spec.ts
git commit -m "feat: implement hamburger navigation menu for mobile devices

[See full commit message in Step 2A.4 above]"

git push origin feat/mobile-hamburger-menu

# Merge to main
git checkout main
git pull origin main
git merge feat/mobile-hamburger-menu
git push origin main

# Monitor GitHub Actions deployment
# Smoke test on deployed site
# Test on real mobile device (critical for hamburger menu)

# If issues found in production:
# - See Rollback Procedure below
# - Fix issues in new branch
# - Redeploy
```

---

**Alternative: Phase 2B (Collapsible Navigation - faster):**
```bash
# Same workflow as Phase 2A but with Option B changes
# See Step 2B.1-2B.4 for specific changes
# Total time: 2-3 hours vs 4-6 hours for Option A
```

---

### Rollback Procedure

**If Phase 0/1 causes issues:**
```bash
# Find commit hash
git log --oneline
# Example output:
# a1b2c3d fix: mobile UX improvements - WCAG compliance and accessibility
# e4f5g6h Previous commit

# Option 1: Revert commit (creates new commit that undoes changes)
git revert a1b2c3d
git push origin main
# GitHub Actions will redeploy with reverted changes

# Option 2: Hard reset (destructive, use with caution)
git reset --hard e4f5g6h
git push origin main --force
# This removes commit from history - only use if absolutely necessary
```

**If Phase 2 causes issues:**
```bash
# Identify problematic commit
git log --oneline | grep "hamburger"
# Example: b2c3d4e feat: implement hamburger navigation menu

# Revert the commit
git revert b2c3d4e
git push origin main

# GitHub Actions will redeploy
# Previous navigation pattern (Phase 0+1 improvements) will be restored

# Investigate issue locally
git checkout -b fix/hamburger-menu-issue
# Debug and fix
# Test thoroughly
# Redeploy when ready
```

**Emergency rollback (production is broken):**
```bash
# Roll back to last known good commit immediately
git log --oneline
# Identify last working commit (before problematic changes)

git reset --hard <last-good-commit-hash>
git push origin main --force

# Notify users via status page if applicable
# Investigate issue in separate branch
# Fix and redeploy when ready
```

---

### Post-deployment Validation

**Smoke test checklist (run on deployed site):**

**Phase 0 validation:**
- [ ] Navigate to https://[username].github.io/cpp-to-c-website/
- [ ] Open Chrome DevTools
- [ ] Set viewport to 375px × 667px (iPhone 8)
- [ ] Inspect `.tab` element
- [ ] Verify computed height ≥ 44px
- [ ] Test on real mobile device (tap navigation links)

**Phase 1 validation:**
- [ ] Press Tab key on deployed site
- [ ] Skip link appears
- [ ] Press Enter → jumps to main content
- [ ] Inspect active tab → has `aria-current="page"`
- [ ] Tab through navigation → blue outline visible

**Phase 2A validation (if hamburger menu deployed):**
- [ ] Viewport 375px → hamburger button visible
- [ ] Click hamburger → drawer slides in
- [ ] Click overlay → drawer closes
- [ ] Press Escape → drawer closes
- [ ] Viewport 1024px → horizontal tabs visible (no hamburger)
- [ ] Test on real iPhone/Android device (critical)

**Phase 2B validation (if collapsible nav deployed):**
- [ ] Viewport 375px → "Menu" button visible
- [ ] Navigation hidden by default
- [ ] Click button → navigation expands
- [ ] Click again → navigation collapses
- [ ] Viewport 1024px → navigation always visible

**Analytics verification (optional):**
- [ ] Check Google Analytics (if configured)
- [ ] Monitor bounce rate on mobile devices
- [ ] Check time on page for mobile users
- [ ] Monitor navigation interaction events

---

## Risk Mitigation

### Phase 0 Risks

| Risk | Impact | Probability | Mitigation Strategy |
|------|--------|-------------|---------------------|
| **Layout shift from padding change** | Low | Low | - Verify with Playwright bounding box tests before/after<br>- Visual regression testing at all viewports<br>- Check that text remains vertically centered |
| **Text wrapping change** | Low | Very Low | - Test all 11 navigation labels (some are long like "Architecture")<br>- Verify no unexpected wrapping at 320px viewport<br>- Check that `white-space: nowrap` still works |
| **Active tab styling breaks** | Low | Very Low | - Test active tab on multiple pages<br>- Verify `.active` class border positioning unchanged<br>- Check `margin-bottom: -2px` calculation still correct |
| **Build fails** | Medium | Very Low | - Run `npm run build` before committing<br>- Verify Astro compilation succeeds<br>- Check for TypeScript errors |

**Rollback time if issues:** 5 minutes (single git revert)

---

### Phase 1 Risks

| Risk | Impact | Probability | Mitigation Strategy |
|------|--------|-------------|---------------------|
| **Skip link interferes with header** | Low | Low | - Use `position: absolute` not `fixed`<br>- Set `z-index: 100` (above header)<br>- Test that link doesn't push content down when visible |
| **Skip link focus not visible** | Medium | Low | - Use high contrast (white on blue background)<br>- Test on multiple browsers<br>- Verify `:focus` state has clear outline |
| **Main content not focusable** | Medium | Medium | - Add `tabindex="-1"` to `<main>`<br>- Test in Safari (has different focus behavior)<br>- Verify focus indicator appears on main |
| **Focus indicators too prominent** | Low | Low | - Use `:focus-visible` to hide on mouse clicks<br>- Test in browsers that support `:focus-visible`<br>- Fallback to `:focus:not(:focus-visible)` for older browsers |
| **ARIA attributes not read by screen reader** | Medium | Low | - Test with VoiceOver and NVDA<br>- Verify `aria-current="page"` announced<br>- Check that undefined values don't render as attribute |

**Rollback time if issues:** 10 minutes (git revert + redeploy)

---

### Phase 2A Risks (Hamburger Menu)

| Risk | Impact | Probability | Mitigation Strategy |
|------|--------|-------------|---------------------|
| **JavaScript fails on old browsers** | High | Low | - Use feature detection: `if (typeof window !== 'undefined')`<br>- Provide no-JS fallback: keep vertical nav visible if JS fails<br>- Test in IE11 (if supporting legacy browsers)<br>- Use vanilla JS (no ES6+ features that might break) |
| **Drawer animation janky on low-end devices** | Medium | Medium | - Use CSS transitions (GPU-accelerated)<br>- Avoid JavaScript-based animations<br>- Test on throttled CPU in Chrome DevTools<br>- Keep animation duration short (250ms)<br>- Use `transform` instead of `left` if jank occurs |
| **Focus trap breaks navigation** | High | Low | - Thoroughly test Tab/Shift+Tab cycling<br>- Verify Escape key always works<br>- Add timeout to focus restoration (avoid race condition)<br>- Test edge case: close drawer while tabbing |
| **Increased bundle size** | Medium | Low | - JavaScript is inline (no external bundle)<br>- ~100 lines = ~3KB minified<br>- Check build output for size increase<br>- Consider code splitting if bundle becomes large |
| **Overlay doesn't cover viewport** | Low | Medium | - Use `position: fixed` with `width: 100%` `height: 100%`<br>- Test on iOS Safari (viewport units behave differently)<br>- Verify no scroll-through on mobile |
| **Body scroll not prevented** | Medium | Medium | - Add `overflow: hidden` to body when menu open<br>- Test on iOS (notorious for scroll prevention issues)<br>- Consider `touch-action: none` if scroll still happens |
| **Drawer persists after resize** | Low | Medium | - Add resize event listener to close menu at desktop width<br>- Debounce resize handler (250ms)<br>- Test rotate device (portrait ↔ landscape) |
| **ARIA state out of sync** | Medium | Low | - Update aria-expanded in openMenu/closeMenu functions<br>- Use single source of truth (`isOpen` variable)<br>- Test with screen reader to verify announcements |

**Rollback time if issues:** 15 minutes (git revert + test + redeploy)

**Mitigation: Progressive enhancement**
```javascript
// If hamburger menu JavaScript fails, show vertical navigation as fallback
<noscript>
  <style>
    .tab-nav-desktop { display: flex !important; }
    .mobile-menu-button { display: none !important; }
  </style>
</noscript>
```

---

### Phase 2B Risks (Collapsible Navigation)

| Risk | Impact | Probability | Mitigation Strategy |
|------|--------|-------------|---------------------|
| **LocalStorage not available** | Low | Very Low | - Wrap localStorage calls in try/catch<br>- Gracefully degrade if unavailable (privacy mode)<br>- Default to collapsed if localStorage fails |
| **Toggle button state out of sync** | Low | Low | - Use single source of truth (`isExpanded` variable)<br>- Update ARIA and class together in same function<br>- Test rapid clicking (debounce if needed) |
| **Chevron icon doesn't rotate** | Low | Low | - Test CSS transform in all browsers<br>- Verify transition duration appropriate (200ms)<br>- Check SVG renders correctly |

**Rollback time if issues:** 10 minutes (simpler than Option A)

---

## Success Metrics

### Phase 0 Success Criteria

**WCAG Compliance:**
- ✅ All navigation tabs measure ≥ 44px height (Playwright verified)
  - **Measurement:** Run Playwright `.boundingBox()` on all `.tab` elements at 320px, 375px, 414px viewports
  - **Baseline:** 43px (FAILING)
  - **Target:** ≥ 44px (PASSING)
  - **Actual:** 47px (EXCEEDS by 3px)

**Visual Integrity:**
- ✅ No layout shift introduced (CLS = 0)
  - **Measurement:** Lighthouse CLS metric before/after
  - **Target:** CLS = 0 (no shift)
- ✅ Text remains vertically centered in tabs
  - **Measurement:** Visual inspection at 320px, 768px, 1024px
  - **Target:** No alignment issues visible
- ✅ Active tab styling intact
  - **Measurement:** Navigate to different pages, verify `.active` class styling
  - **Target:** Blue underline, white background unchanged

**Deployment:**
- ✅ Deployed to production within 1 business day
  - **Measurement:** Git commit timestamp → GitHub Pages deploy timestamp
  - **Target:** < 24 hours
- ✅ No rollback required
  - **Measurement:** Git history shows no revert commits
  - **Target:** 0 reverts

**Time estimate validation:**
- **Estimated:** 5 minutes
- **Actual:** [to be measured]
- **Target:** < 10 minutes

---

### Phase 1 Success Criteria

**Accessibility Compliance:**
- ✅ Lighthouse accessibility score ≥ 95
  - **Measurement:** Chrome DevTools Lighthouse audit
  - **Baseline:** Unknown (run before Phase 1)
  - **Target:** ≥ 95
  - **Actual:** [to be measured]

**Skip Link Functionality:**
- ✅ Skip link appears on first Tab keypress
  - **Measurement:** Manual test - press Tab on page load
  - **Target:** Link visible at top-left with focus
- ✅ Skip link jumps to main content on Enter
  - **Measurement:** Playwright test `expect(main).toBeFocused()`
  - **Target:** Test passes
- ✅ Skip link works on all pages
  - **Measurement:** Test on Home, About, Features, Benchmarks pages
  - **Target:** Functional on 100% of pages

**ARIA Implementation:**
- ✅ Active tab has `aria-current="page"`
  - **Measurement:** DevTools inspect → verify attribute present
  - **Target:** Attribute present on 1 active tab per page
- ✅ Inactive tabs have no `aria-current`
  - **Measurement:** DevTools inspect → verify attribute absent
  - **Target:** Attribute absent on 10 inactive tabs

**Focus Indicators:**
- ✅ Focus indicators visible on keyboard navigation
  - **Measurement:** Tab through page, observe 2px blue outline
  - **Target:** Outline visible on all focusable elements
- ✅ Focus indicators hidden on mouse clicks
  - **Measurement:** Click elements with mouse, verify no outline
  - **Target:** No outline visible after mouse interaction (`:focus-visible` behavior)

**Screen Reader Testing:**
- ✅ Skip link announced correctly
  - **Measurement:** VoiceOver/NVDA announces "Skip to main content, link"
  - **Target:** Announcement includes element type and text
- ✅ Active tab announced as "current page"
  - **Measurement:** VoiceOver/NVDA announces "Home, link, current page"
  - **Target:** "current page" state announced

**Deployment:**
- ✅ Deployed within 1 week
  - **Measurement:** Git commit timestamp
  - **Target:** < 7 days from Phase 0 deployment
- ✅ No visual regressions
  - **Measurement:** Visual inspection at all viewports
  - **Target:** No unintended layout changes

**Time estimate validation:**
- **Estimated:** 30 minutes (15 + 5 + 10)
- **Actual:** [to be measured]
- **Target:** < 45 minutes

---

### Phase 2A Success Criteria (Hamburger Menu)

**Mobile Navigation Functionality:**
- ✅ Mobile navigation functional on 320px - 768px viewports
  - **Measurement:** Manual test on 320px, 375px, 414px, 768px
  - **Target:** Hamburger button visible, drawer opens/closes
- ✅ Desktop navigation unchanged on ≥ 769px viewports
  - **Measurement:** Manual test on 769px, 1024px, 1440px
  - **Target:** Horizontal tabs visible, no hamburger button

**Touch Target Compliance:**
- ✅ Hamburger button has 44px+ touch target
  - **Measurement:** Playwright `.boundingBox()` test
  - **Target:** width ≥ 44px AND height ≥ 44px
- ✅ All mobile navigation items have 44px+ height
  - **Measurement:** Playwright test on all `.mobile-nav-item` elements
  - **Target:** 11/11 items ≥ 44px height
- ✅ Close button has 44px+ touch target
  - **Measurement:** Playwright `.boundingBox()` test
  - **Target:** width ≥ 44px AND height ≥ 44px

**Animation & Performance:**
- ✅ Drawer slides in smoothly from left
  - **Measurement:** Visual inspection, Chrome DevTools Performance tab
  - **Target:** 60fps animation, no frame drops
- ✅ Drawer animation duration 250ms
  - **Measurement:** CSS transition value, perceived duration
  - **Target:** Feels responsive, not too fast or slow
- ✅ Overlay fades in/out smoothly
  - **Measurement:** Visual inspection
  - **Target:** Smooth opacity transition, no flicker

**Focus Management:**
- ✅ First navigation link receives focus when drawer opens
  - **Measurement:** Playwright test `expect(firstLink).toBeFocused()`
  - **Target:** Test passes
- ✅ Focus returns to hamburger button when drawer closes
  - **Measurement:** Playwright test `expect(menuButton).toBeFocused()`
  - **Target:** Test passes
- ✅ Focus trap works (Tab cycles within drawer)
  - **Measurement:** Manual test - Tab through drawer, verify no escape
  - **Target:** Tab on last item → focus first item

**Keyboard Navigation:**
- ✅ Escape key closes drawer
  - **Measurement:** Playwright test with `page.keyboard.press('Escape')`
  - **Target:** Test passes
- ✅ Enter key opens/closes drawer via button
  - **Measurement:** Manual test - Tab to button, press Enter
  - **Target:** Drawer toggles open/closed
- ✅ Tab/Shift+Tab navigate through drawer items
  - **Measurement:** Manual test
  - **Target:** All items reachable via keyboard

**Auto-close Scenarios:**
- ✅ Clicking navigation item closes drawer
  - **Measurement:** Playwright test - click item, verify drawer closes
  - **Target:** Test passes
- ✅ Clicking overlay closes drawer
  - **Measurement:** Playwright test - click overlay, verify drawer closes
  - **Target:** Test passes
- ✅ Resizing to desktop closes drawer
  - **Measurement:** Manual test - resize from 375px to 1024px
  - **Target:** Drawer closes, hamburger hidden

**Layout & Responsiveness:**
- ✅ No horizontal overflow on any viewport
  - **Measurement:** Playwright test `document.body.scrollWidth <= viewport.width`
  - **Target:** Test passes for 320px, 375px, 414px, 768px
- ✅ Body scroll prevented when drawer open
  - **Measurement:** Manual test - open drawer, try to scroll page
  - **Target:** Page cannot scroll while drawer open
- ✅ Drawer covers 280px width
  - **Measurement:** Playwright `.boundingBox()` test
  - **Target:** drawer.width === 280

**Performance:**
- ✅ Performance metrics maintained
  - **Measurement:** Lighthouse performance score before/after
  - **Baseline:** >90 (current site)
  - **Target:** ≥ 90 (no regression)
- ✅ Load time < 100ms (localhost)
  - **Measurement:** `window.performance.timing`
  - **Target:** < 100ms
- ✅ CLS = 0 (no layout shift)
  - **Measurement:** Lighthouse CLS metric
  - **Target:** CLS = 0
- ✅ Bundle size increase < 5KB
  - **Measurement:** Compare `dist/` folder size before/after build
  - **Target:** Increase < 5KB

**Automated Tests:**
- ✅ All Playwright tests passing
  - **Measurement:** `npm test` exit code
  - **Target:** 100% pass rate (0 failures)
- ✅ Lighthouse accessibility score ≥ 95
  - **Measurement:** Lighthouse audit
  - **Target:** ≥ 95

**Real Device Testing:**
- ✅ Tested on real iPhone (iOS 15+)
  - **Measurement:** Manual test on physical device
  - **Target:** All functionality works, touch targets feel natural
- ✅ Tested on real Android device (Android 10+)
  - **Measurement:** Manual test on physical device
  - **Target:** All functionality works, animations smooth

**Deployment:**
- ✅ Deployed to production successfully
  - **Measurement:** GitHub Actions workflow succeeds
  - **Target:** Green checkmark in Actions tab
- ✅ No rollback required
  - **Measurement:** No git revert commits
  - **Target:** 0 reverts within 24 hours
- ✅ No console errors on deployed site
  - **Measurement:** Chrome DevTools Console on production URL
  - **Target:** 0 errors (warnings acceptable)

**User Feedback (optional, post-deployment):**
- ⚠️ Mobile bounce rate unchanged or improved
  - **Measurement:** Google Analytics (if configured)
  - **Baseline:** Current mobile bounce rate
  - **Target:** ≤ baseline (no regression)
- ⚠️ Time on page for mobile users maintained
  - **Measurement:** Google Analytics
  - **Baseline:** Current average time
  - **Target:** ≥ baseline

**Time estimate validation:**
- **Estimated:** 4-6 hours
  - Step 2A.1: 30 min
  - Step 2A.2: 1-2 hr
  - Step 2A.3: 1-2 hr
  - Step 2A.4: 1 hr
- **Actual:** [to be measured]
- **Target:** < 8 hours (solo developer in single day)

---

### Phase 2B Success Criteria (Collapsible Navigation)

**If Option B chosen instead of Option A:**

**Functionality:**
- ✅ Toggle button appears on mobile (< 768px)
- ✅ Navigation collapsed by default
- ✅ Button expands/collapses navigation
- ✅ Chevron icon rotates when expanded
- ✅ User preference persisted (localStorage)
- ✅ Auto-collapse on navigation click
- ✅ Toggle button hidden on desktop (≥ 769px)

**Time estimate validation:**
- **Estimated:** 2-3 hours
- **Actual:** [to be measured]
- **Target:** < 4 hours

---

## Next Steps After Planning

### Immediate Actions (Before Implementation)

1. **Get navigation pattern approval:**
   - Review Decision Tree with stakeholders/team
   - Choose Option A (Hamburger - 4-6hr), Option B (Collapsible - 2-3hr), or Option C (Hybrid - 6-8hr)
   - Document decision and rationale
   - **Decision needed by:** [Date] before Phase 2 can start

2. **Set up testing environment:**
   - Verify Playwright is installed (`npm test` should run)
   - Install browser DevTools extensions if needed
   - Set up real device testing (borrow iPhone/Android if don't have)
   - Configure screen reader (VoiceOver on Mac, NVDA on Windows)

3. **Create implementation timeline:**
   - **Week 1:** Phase 0 (5 min) + Phase 1 (30 min) = **35 minutes total**
   - **Week 2-3:** Phase 2A (4-6 hr) OR Phase 2B (2-3 hr) depending on choice
   - **Future:** Phase 3 (2-3 hr) - defer until Phase 2 deployed and stable

---

### Execution Plan

**Option 1: Deploy Phase 0 immediately (RECOMMENDED)**
```
Day 1 (today):
- Execute Phase 0 (5 minutes)
- Test locally
- Deploy to production
- Validate on deployed site

Day 2-3 (this week):
- Execute Phase 1 (30 minutes)
- Test thoroughly
- Deploy to production

Day 7-14 (next sprint):
- Get navigation pattern decision
- Execute Phase 2A or 2B
- Test extensively
- Deploy to production
```

**Option 2: Bundle Phase 0+1 (faster initial deployment)**
```
Day 1 (today or this week):
- Execute Phase 0 + Phase 1 together (35 minutes total)
- Test bundled changes
- Deploy to production
- Single deployment, faster overall

Week 2:
- Get navigation pattern decision
- Execute Phase 2
- Deploy
```

**Recommendation:** Option 1 (deploy Phase 0 today) for fastest WCAG compliance, then Phase 1 later this week, then Phase 2 next sprint.

---

### Creating Implementation Prompts (if using prompt-driven development)

If you use a prompt-driven workflow, create these prompts:

**.prompts/010-mobile-ux-phase-0-implement/**
- `010-mobile-ux-phase-0-implement.md` - Detailed Phase 0 implementation instructions
- `SUMMARY.md` - "Fix WCAG touch target violation (5 min CSS change)"

**.prompts/011-mobile-ux-phase-1-implement/**
- `011-mobile-ux-phase-1-implement.md` - Detailed Phase 1 implementation instructions
- `SUMMARY.md` - "Add skip link, ARIA, focus indicators (30 min)"

**.prompts/012-mobile-ux-phase-2-implement/**
- `012-mobile-ux-phase-2-implement.md` - Detailed Phase 2 implementation instructions (Option A or B)
- `SUMMARY.md` - "Implement hamburger menu for mobile (4-6 hr)" OR "Implement collapsible nav (2-3 hr)"

**Alternatively:** Execute directly from this plan document (all implementation details are here).

---

### Communication

**If working with team/stakeholders:**

**Email template for Phase 0 deployment:**
```
Subject: [Action Completed] Mobile UX Fix Deployed - WCAG Compliance Achieved

Hi team,

I've deployed a critical accessibility fix for our mobile navigation:

**What changed:**
- Navigation tab touch targets increased from 43px to 47px
- Now meets WCAG AAA standard (44px minimum)
- Affects 10/11 navigation links on mobile devices

**Impact:**
- Better usability for users with motor impairments
- WCAG 2.5.5 Level AAA compliance achieved
- No visual changes (users won't notice difference)

**Testing:**
- Playwright automated tests verify ≥44px on all viewports
- Manual testing on iPhone 8 (375px viewport)
- No regressions detected

**Next steps:**
- Phase 1: Add skip link and accessibility improvements (this week)
- Phase 2: Implement hamburger menu for mobile (next sprint)

**Deployed URL:** https://[username].github.io/cpp-to-c-website/

Questions? Let me know!

[Your Name]
```

**Slack/Discord update template:**
```
🎉 Mobile UX improvement deployed!

Fixed: Navigation touch targets now 44px+ (was 43px)
Impact: WCAG AAA compliance ✅
Time: 5 minutes implementation
Testing: All automated tests passing

Next: Skip link + hamburger menu coming soon
```

---

### Monitoring & Iteration

**Week 1 (after Phase 0+1 deployment):**
- [ ] Monitor GitHub Pages deployment logs
- [ ] Check for user feedback (if applicable)
- [ ] Run Lighthouse audit on deployed site
- [ ] Verify no unexpected issues reported

**Week 2-3 (after Phase 2 deployment):**
- [ ] Monitor mobile bounce rate (Google Analytics if configured)
- [ ] Collect user feedback on new navigation pattern
- [ ] Check for console errors in production (use Sentry if configured)
- [ ] Test on real devices (borrow from friends/colleagues)

**Month 1 (post-full-deployment):**
- [ ] Review analytics: mobile engagement metrics
- [ ] Gather user feedback via survey (optional)
- [ ] Identify any remaining pain points
- [ ] Plan Phase 3 improvements based on data

---

## Appendix

### WCAG References

**Success Criteria addressed in this plan:**

- **2.5.5 Touch Target Size (Level AAA):** Minimum 44×44 CSS pixels
  - [WCAG 2.1 Understanding 2.5.5](https://www.w3.org/WAI/WCAG21/Understanding/target-size.html)
  - **Fixed in:** Phase 0

- **2.4.1 Bypass Blocks (Level A):** Skip navigation link
  - [WCAG 2.1 Understanding 2.4.1](https://www.w3.org/WAI/WCAG21/Understanding/bypass-blocks.html)
  - **Fixed in:** Phase 1

- **2.4.7 Focus Visible (Level AA):** Visible focus indicators
  - [WCAG 2.1 Understanding 2.4.7](https://www.w3.org/WAI/WCAG21/Understanding/focus-visible.html)
  - **Fixed in:** Phase 1

- **4.1.2 Name, Role, Value (Level A):** ARIA attributes
  - [WCAG 2.1 Understanding 4.1.2](https://www.w3.org/WAI/WCAG21/Understanding/name-role-value.html)
  - **Fixed in:** Phase 1, Phase 2

- **2.4.3 Focus Order (Level A):** Logical focus sequence
  - [WCAG 2.1 Understanding 2.4.3](https://www.w3.org/WAI/WCAG21/Understanding/focus-order.html)
  - **Fixed in:** Phase 2 (focus management)

### Competitive Analysis Summary

**Research reference:** `.prompts/008-mobile-friendly-ux-research/mobile-friendly-ux-research.md`

| Documentation Site | Mobile Pattern | Rationale for C++ to C Site |
|-------------------|----------------|----------------------------|
| **MDN Web Docs** | Hamburger menu + sidebar | **HIGH FIT** - Similar doc structure, many pages, deep navigation hierarchy |
| **TypeScript Handbook** | Bottom sticky tabs (3 main tabs) | **LOW FIT** - We have 11 tabs, not 3; bottom tabs don't scale |
| **Rust Book** | Hamburger + table of contents | **MEDIUM FIT** - Good for docs section, but we need site-wide nav |

**Conclusion:** Hamburger menu (Option A) aligns best with industry standards for documentation sites with 10+ navigation items.

### File Modification Summary

**All changes in single file:** `src/layouts/MainLayout.astro`

**Phase 0 modifications:**
- Line 121: Change `.tab { padding: 0.5rem 1rem; }` → `padding: 0.625rem 1rem;`
- Line 122: Add `min-height: 44px;`

**Phase 1 modifications:**
- Line 154: Add skip link HTML after `<body>`
- Line ~150: Add skip link CSS in `<style is:global>`
- Line 162-168: Add `aria-current` attribute to tab links
- Line 174: Add `id="main-content"` to `<main>` tag
- Line ~150: Add focus indicator CSS

**Phase 2A modifications (if Option A chosen):**
- Lines 155-172: Extensive header restructuring (add hamburger button, drawer, overlay)
- Lines 39-152: Add ~200 lines of CSS for mobile menu
- After line 197: Add ~100 lines of JavaScript for menu logic

**Phase 2B modifications (if Option B chosen):**
- Lines 155-172: Add toggle button to header
- Lines 39-152: Add ~100 lines of CSS for collapsible nav
- After line 197: Add ~40 lines of JavaScript for toggle logic

**New files created:**
- `tests/mobile-navigation.spec.ts` (Playwright tests for Phase 2)

**Total lines changed:**
- Phase 0: 2 lines modified
- Phase 1: ~50 lines added
- Phase 2A: ~350 lines added (hamburger)
- Phase 2B: ~150 lines added (collapsible)

### Browser Support Matrix

**Target browser support:**

| Browser | Version | Support Level | Notes |
|---------|---------|---------------|-------|
| Chrome | 90+ | Full support | All features work |
| Firefox | 88+ | Full support | All features work |
| Safari | 14+ | Full support | Test `:focus-visible` carefully |
| Mobile Safari | iOS 12+ | Full support | Primary mobile target |
| Chrome Android | 90+ | Full support | Primary mobile target |
| Edge | 90+ | Full support | Chromium-based |
| IE 11 | N/A | Not supported | Use feature detection, graceful degradation |

**Feature compatibility:**

| Feature | Baseline Support | Fallback |
|---------|-----------------|----------|
| `:focus-visible` | Chrome 86+, Firefox 85+, Safari 15.4+ | Use `:focus:not(:focus-visible)` pattern |
| `aria-current` | All modern browsers + screen readers | Visual styling as fallback |
| CSS Grid | Chrome 57+, Firefox 52+, Safari 10.1+ | Not used in this plan (flexbox only) |
| `localStorage` | All browsers except privacy mode | Try/catch wrapper, default to collapsed |
| `position: sticky` | Chrome 56+, Firefox 59+, Safari 13+ | Graceful degradation (no sticky, scrolls normally) |

### Glossary

**ARIA (Accessible Rich Internet Applications):** HTML attributes that improve accessibility for screen readers (e.g., `aria-label`, `aria-current`, `aria-expanded`)

**CLS (Cumulative Layout Shift):** Metric measuring visual stability (0 = no shift, <0.1 = good)

**Focus trap:** Technique to keep keyboard focus within a specific container (e.g., drawer menu) by cycling Tab key through elements

**Hamburger menu:** Three horizontal lines icon (☰) that opens navigation drawer on mobile devices

**Playwright:** Browser automation framework for end-to-end testing

**Progressive disclosure:** UX pattern of hiding information until user requests it (e.g., collapsed navigation)

**Skip link:** Hidden link that appears on first Tab keypress, allowing keyboard users to skip repetitive navigation

**Touch target:** Area users can tap/click; WCAG AAA requires minimum 44×44 pixels

**WCAG (Web Content Accessibility Guidelines):** W3C standard for web accessibility; Level A (minimum) → Level AA (recommended) → Level AAA (enhanced)

---

**Plan version:** v1.0
**Created:** 2025-12-19
**Based on research:** `.prompts/008-mobile-friendly-ux-research/mobile-friendly-ux-research.md`
**Primary file modified:** `src/layouts/MainLayout.astro`
**Total estimated time:** 5 hours 35 minutes (Phase 0+1+2A) or 2 hours 35 minutes (Phase 0+1+2B)

**Ready for execution:** Yes - all implementation details provided, developer can start Phase 0 immediately
