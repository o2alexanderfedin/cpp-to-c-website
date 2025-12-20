# Mobile UX Implementation Plan Summary

**Phased plan to fix WCAG violation (43px→47px touch targets), add accessibility features (skip link, ARIA), and implement industry-standard hamburger menu navigation - deployable in stages from 5 minutes to 6 hours**

## Version
v1.0 - Comprehensive implementation plan based on mobile UX research findings

## Key Components

### Navigation Pattern Decision Tree
**RECOMMENDED: Option A - Hamburger Menu** (4-6 hours)
- Matches industry standard (MDN, TypeScript, Rust all use hamburger pattern)
- Frees 480px vertical space on mobile
- JavaScript-based drawer with focus management
- **Alternative: Option B - Collapsible Navigation** (2-3 hours if timeline critical)

**Decision criteria:**
- Industry standard UX → Choose Option A (Hamburger)
- Speed & simplicity → Choose Option B (Collapsible)
- Maximum polish → Choose Option C (Sticky + Hamburger, 6-8 hours)

### Phase 0: Immediate WCAG Fix (5 minutes - deploy today)
**CRITICAL:** 10/11 navigation links currently 43px height (1px short of 44px WCAG AAA minimum)

**Single CSS change:**
```css
.tab {
  padding: 0.625rem 1rem;  /* was 0.5rem → increases 43px to 47px */
  min-height: 44px;        /* explicit safety constraint */
}
```

**File:** `src/layouts/MainLayout.astro` line 121
**Testing:** Playwright `.boundingBox()` verification
**Impact:** WCAG 2.5.5 Level AAA compliance achieved
**Risk:** Minimal (pure CSS, no breaking changes)

### Phase 1: Accessibility Quick Wins (30 minutes - this week)

**Task 1.1: Skip Navigation Link (15 min)**
- Add hidden link before header: `<a href="#main-content" class="skip-link">`
- Appears on first Tab keypress, jumps to main content
- Keyboard users skip 11 navigation links

**Task 1.2: ARIA Current Attribute (5 min)**
- Add `aria-current="page"` to active navigation tab
- Screen readers announce current page location

**Task 1.3: Focus Indicators (10 min)**
- Add explicit 2px blue outline for keyboard navigation
- Use `:focus-visible` to hide outline on mouse clicks
- Improves WCAG 2.4.7 compliance

**Bundled deployment:** Phase 0 + Phase 1 = 35 minutes total
**Impact:** Full WCAG AA/AAA compliance for navigation

### Phase 2: Navigation Pattern Implementation (4-6 hours OR 2-3 hours)

**Option A: Hamburger Menu (RECOMMENDED - 4-6 hours)**

**Step 2A.1: HTML Structure (30 min)**
- Add hamburger button (☰ icon, 44px touch target)
- Wrap navigation in slide-in drawer (280px width)
- Add semi-transparent overlay backdrop

**Step 2A.2: CSS Styling (1-2 hours)**
- Drawer: `position: fixed`, slides from `left: -280px` to `left: 0`
- Animation: `transition: left 0.25s ease-out`
- Mobile (≤768px): Show hamburger, hide horizontal tabs
- Desktop (≥769px): Hide hamburger, show horizontal tabs

**Step 2A.3: JavaScript Logic (1-2 hours)**
- Menu toggle (open/close with state management)
- Focus management (focus first link on open, return focus on close)
- Focus trap (Tab cycles within drawer when open)
- Keyboard support (Escape closes, Enter toggles)
- Auto-close (link click, overlay click, viewport resize)
- ARIA state updates (`aria-expanded`, `aria-hidden`)

**Step 2A.4: Testing (1 hour)**
- Playwright tests: open/close, keyboard, touch targets
- Manual testing: 320px, 375px, 414px, 768px, 1024px viewports
- Accessibility: VoiceOver/NVDA, keyboard-only navigation
- Real device testing (iPhone/Android)

**Success metrics:**
- All touch targets ≥ 44px (hamburger button, nav items, close button)
- Smooth 250ms drawer animation (60fps)
- Focus management works correctly
- Desktop navigation unchanged
- No horizontal overflow on any viewport

**Option B: Collapsible Navigation (ALTERNATIVE - 2-3 hours)**
- Toggle button with chevron icon (rotates when expanded)
- Navigation collapsed by default on mobile
- Simpler implementation (minimal JavaScript)
- Can upgrade to Option A later if needed

**Trade-off:** Option B is 50% faster but non-standard pattern; Option A matches industry expectations

### Phase 3: Future Polish (2-3 hours - deferred)
- Font loading optimization (if custom fonts added)
- Lazy load large tables (below fold)
- Sticky first column for wide tables
- Dark mode toggle (separate 4-6 hour feature)
- WebAssembly playground performance testing

**Defer rationale:** Phase 0-2 address all critical issues; Phase 3 is "nice to have"

## Files Modified
**Primary file:** `src/layouts/MainLayout.astro` (all HTML, CSS, JavaScript changes in single file)
- Phase 0: Lines 121-122 (2 lines modified)
- Phase 1: ~50 lines added (skip link, ARIA, focus CSS)
- Phase 2A: ~350 lines added (hamburger menu)
- Phase 2B: ~150 lines added (collapsible nav)

**New files:**
- `tests/mobile-navigation.spec.ts` (Playwright tests for automated validation)

## Decisions Needed

**CRITICAL DECISION: Choose navigation pattern before Phase 2**

**Question 1:** Hamburger menu (4-6hr, industry standard) OR Collapsible nav (2-3hr, faster)?
- **Recommendation:** Hamburger (Option A) - aligns with MDN/TypeScript/Rust patterns
- **Alternative:** Collapsible (Option B) if timeline critical, upgrade to Option A later

**Question 2:** Deploy Phase 0 today OR bundle Phase 0+1 (35 min total)?
- **Recommendation:** Bundle Phase 0+1 (faster overall, single deployment)
- **Alternative:** Deploy Phase 0 today (5 min) for immediate WCAG compliance

**Question 3:** Testing depth - minimal OR full cross-browser validation?
- **Recommendation:** Full testing (includes real device, screen reader, Lighthouse)
- **Alternative:** Minimal (Playwright + manual at 375px/1024px) if time critical

## Blockers
**None** - all phases have clear implementation steps, can begin immediately

**Dependencies:**
- Phase 1 depends on Phase 0 (can be bundled)
- Phase 2 depends on navigation pattern decision
- Phase 3 depends on Phase 2 deployment and user feedback

**Prerequisites:**
- Playwright installed and working (`npm test` should run)
- Browser DevTools available for testing
- Real mobile device available (optional but recommended for Phase 2)
- Screen reader configured (VoiceOver or NVDA for accessibility testing)

## Implementation Timeline

**Recommended execution:**

**Week 1 (this week):**
- Deploy Phase 0 + Phase 1 bundled (35 minutes implementation + testing)
- Validate on production (Lighthouse audit, manual testing)
- Immediate WCAG compliance achieved ✅

**Week 2-3 (next sprint):**
- Get navigation pattern decision from stakeholders
- Implement Phase 2A (Hamburger - 4-6 hours) OR Phase 2B (Collapsible - 2-3 hours)
- Extensive testing (Playwright, manual, real device)
- Deploy to production

**Future (deferred):**
- Phase 3 enhancements based on user feedback and analytics
- Monitor mobile engagement metrics
- Iterate based on data

**Alternative (fastest WCAG compliance):**
- Today: Phase 0 only (5 minutes) → immediate touch target fix
- This week: Phase 1 (30 minutes) → full accessibility
- Next sprint: Phase 2 (4-6 hours) → navigation UX

## Success Criteria

**Phase 0 (5 min):**
- ✅ All touch targets ≥ 44px (Playwright verified)
- ✅ No visual regressions
- ✅ Deployed within 1 business day

**Phase 1 (30 min):**
- ✅ Lighthouse accessibility score ≥ 95
- ✅ Skip link functional on all pages
- ✅ Active tab has `aria-current="page"`
- ✅ Focus indicators visible on keyboard navigation
- ✅ Deployed within 1 week

**Phase 2A (4-6 hours):**
- ✅ Mobile navigation functional 320px - 768px
- ✅ Desktop navigation unchanged (≥ 769px)
- ✅ All touch targets ≥ 44px (button, nav items, close)
- ✅ Smooth drawer animation (60fps, 250ms)
- ✅ Focus management works (focus trap, restore on close)
- ✅ Keyboard navigation works (Tab, Escape, Enter)
- ✅ No horizontal overflow on any viewport
- ✅ Performance maintained (load < 100ms, CLS = 0)
- ✅ All Playwright tests passing

**Phase 2B (2-3 hours):**
- ✅ Toggle button appears on mobile
- ✅ Navigation collapsed by default
- ✅ Expand/collapse functional
- ✅ User preference persisted (localStorage)

## Risk Assessment

**Phase 0:** Minimal risk (pure CSS change)
- Mitigation: Playwright verification, visual regression testing

**Phase 1:** Low risk (additive changes)
- Mitigation: Test skip link on all pages, verify ARIA with screen reader

**Phase 2A:** Medium risk (JavaScript complexity)
- Mitigation: Progressive enhancement (fallback if JS fails), extensive testing
- Key risks: Focus trap bugs, animation jank, iOS scroll issues
- Rollback time: 15 minutes (git revert + redeploy)

**Phase 2B:** Low risk (simpler than Option A)
- Mitigation: Try/catch for localStorage, test rapid clicking

## Next Step

**IMMEDIATE: Execute Phase 0 (5 minutes) or Phase 0+1 (35 minutes)**

**Phase 0 implementation:**
1. Open `src/layouts/MainLayout.astro`
2. Line 121: Change `padding: 0.5rem 1rem;` → `padding: 0.625rem 1rem;`
3. Line 122: Add `min-height: 44px;`
4. Test at 375px viewport (touch targets should be 47px)
5. Commit: "fix: increase nav tab padding to meet WCAG AAA touch target minimum (44px)"
6. Deploy to production

**THEN: Get navigation pattern decision**
- Review Decision Tree with team/stakeholders
- Choose Option A (Hamburger), Option B (Collapsible), or Option C (Hybrid)
- Document decision and rationale
- Schedule Phase 2 implementation (4-6 hour or 2-3 hour session)

**Estimated total time across all phases:**
- **Option A path:** 5 min (Phase 0) + 30 min (Phase 1) + 4-6 hr (Phase 2A) = **5 hours 35 minutes**
- **Option B path:** 5 min (Phase 0) + 30 min (Phase 1) + 2-3 hr (Phase 2B) = **2 hours 35 minutes**

**WCAG compliance timeline:**
- Touch targets: After Phase 0 (5 minutes from now)
- Full accessibility: After Phase 1 (35 minutes from now if bundled)
- Navigation UX: After Phase 2 (within 2 weeks)

---

**Research reference:** `.prompts/008-mobile-friendly-ux-research/mobile-friendly-ux-research.md`
**Plan details:** `.prompts/009-mobile-friendly-ux-plan/mobile-friendly-ux-plan.md`
**Primary file:** `src/layouts/MainLayout.astro`
**Testing:** Playwright + manual + real device + screen reader + Lighthouse
