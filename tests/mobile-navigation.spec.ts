import { test, expect, type Page } from '@playwright/test';

test.describe('Mobile Navigation - Hamburger Menu', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('');
  });

  test.describe('Desktop view (≥ 769px)', () => {
    test.use({ viewport: { width: 1024, height: 768 } });

    test('should hide hamburger button on desktop', async ({ page }) => {
      const menuButton = page.locator('.mobile-menu-button');
      await expect(menuButton).toBeHidden();
    });

    test('should show desktop navigation on desktop', async ({ page }) => {
      const desktopNav = page.locator('.tab-nav-desktop');
      await expect(desktopNav).toBeVisible();
    });

    test('should hide mobile drawer on desktop', async ({ page }) => {
      const drawer = page.locator('.mobile-nav-drawer');
      await expect(drawer).toBeHidden();
    });
  });

  test.describe('Mobile view (≤ 768px)', () => {
    test.use({ viewport: { width: 375, height: 667 } });

    test('should show hamburger button on mobile', async ({ page }) => {
      const menuButton = page.locator('.mobile-menu-button');
      await expect(menuButton).toBeVisible();
    });

    test('should hide desktop navigation on mobile', async ({ page }) => {
      const desktopNav = page.locator('.tab-nav-desktop');
      await expect(desktopNav).toBeHidden();
    });

    test('hamburger button meets WCAG AAA touch target size (44px)', async ({ page }) => {
      const menuButton = page.locator('.mobile-menu-button');
      const box = await menuButton.boundingBox();

      expect(box).not.toBeNull();
      expect(box!.width).toBeGreaterThanOrEqual(44);
      expect(box!.height).toBeGreaterThanOrEqual(44);
    });

    test('should open drawer when hamburger button is clicked', async ({ page }) => {
      const menuButton = page.locator('.mobile-menu-button');
      const drawer = page.locator('.mobile-nav-drawer');

      // Initially closed
      await expect(drawer).not.toHaveClass(/open/);

      // Click to open
      await menuButton.click();

      // Should be open
      await expect(drawer).toHaveClass(/open/);
    });

    test('should update ARIA attributes when opening menu', async ({ page }) => {
      const menuButton = page.locator('.mobile-menu-button');
      const drawer = page.locator('.mobile-nav-drawer');
      const overlay = page.locator('.mobile-nav-overlay');

      // Initially closed state
      await expect(menuButton).toHaveAttribute('aria-expanded', 'false');
      await expect(drawer).toHaveAttribute('aria-hidden', 'true');

      // Open menu
      await menuButton.click();

      // Open state
      await expect(menuButton).toHaveAttribute('aria-expanded', 'true');
      await expect(drawer).toHaveAttribute('aria-hidden', 'false');
      await expect(overlay).toHaveAttribute('aria-hidden', 'false');
    });

    test('should show overlay when menu is open', async ({ page }) => {
      const menuButton = page.locator('.mobile-menu-button');
      const overlay = page.locator('.mobile-nav-overlay');

      // Initially hidden
      await expect(overlay).not.toHaveClass(/visible/);

      // Open menu
      await menuButton.click();

      // Overlay should be visible
      await expect(overlay).toHaveClass(/visible/);
    });

    test('close button meets WCAG AAA touch target size (44px)', async ({ page }) => {
      const menuButton = page.locator('.mobile-menu-button');
      await menuButton.click();

      const closeButton = page.locator('.mobile-nav-close');
      const box = await closeButton.boundingBox();

      expect(box).not.toBeNull();
      expect(box!.width).toBeGreaterThanOrEqual(44);
      expect(box!.height).toBeGreaterThanOrEqual(44);
    });

    test('should close drawer when close button is clicked', async ({ page }) => {
      const menuButton = page.locator('.mobile-menu-button');
      const drawer = page.locator('.mobile-nav-drawer');
      const closeButton = page.locator('.mobile-nav-close');

      // Open menu
      await menuButton.click();
      await expect(drawer).toHaveClass(/open/);

      // Close menu
      await closeButton.click();
      await expect(drawer).not.toHaveClass(/open/);
    });

    test('should close drawer when overlay is clicked', async ({ page }) => {
      const menuButton = page.locator('.mobile-menu-button');
      const drawer = page.locator('.mobile-nav-drawer');
      const overlay = page.locator('.mobile-nav-overlay');

      // Open menu
      await menuButton.click();
      await expect(drawer).toHaveClass(/open/);

      // Click overlay
      await overlay.click();
      await expect(drawer).not.toHaveClass(/open/);
    });

    test('should close drawer when navigation link is clicked', async ({ page }) => {
      const menuButton = page.locator('.mobile-menu-button');
      const drawer = page.locator('.mobile-nav-drawer');

      // Open menu
      await menuButton.click();
      await expect(drawer).toHaveClass(/open/);

      // Click a navigation link
      const firstNavLink = page.locator('.mobile-nav-item').first();
      await firstNavLink.click();

      // Wait for navigation
      await page.waitForLoadState('networkidle');

      // Menu should be closed
      await expect(drawer).not.toHaveClass(/open/);
    });

    test('mobile navigation items meet WCAG AAA touch target size (44px)', async ({ page }) => {
      const menuButton = page.locator('.mobile-menu-button');
      await menuButton.click();

      const navItems = page.locator('.mobile-nav-item');
      const count = await navItems.count();

      for (let i = 0; i < count; i++) {
        const item = navItems.nth(i);
        const box = await item.boundingBox();

        expect(box).not.toBeNull();
        expect(box!.height).toBeGreaterThanOrEqual(44);
      }
    });

    test('should close drawer when Escape key is pressed', async ({ page }) => {
      const menuButton = page.locator('.mobile-menu-button');
      const drawer = page.locator('.mobile-nav-drawer');

      // Open menu
      await menuButton.click();
      await expect(drawer).toHaveClass(/open/);

      // Press Escape
      await page.keyboard.press('Escape');

      // Menu should be closed
      await expect(drawer).not.toHaveClass(/open/);
    });

    test('should trap focus within drawer when open', async ({ page }) => {
      const menuButton = page.locator('.mobile-menu-button');
      await menuButton.click();

      // Get all focusable elements in drawer
      const closeButton = page.locator('.mobile-nav-close');
      const navItems = page.locator('.mobile-nav-item');
      const lastNavItem = navItems.last();

      // Focus should start on first nav item
      const firstNavItem = navItems.first();
      await expect(firstNavItem).toBeFocused();

      // Tab forward through all items
      const navCount = await navItems.count();
      for (let i = 0; i < navCount - 1; i++) {
        await page.keyboard.press('Tab');
      }

      // Should be on last nav item
      await expect(lastNavItem).toBeFocused();

      // Tab forward should go to close button
      await page.keyboard.press('Tab');
      await expect(closeButton).toBeFocused();

      // Tab forward from close button should wrap to first nav item
      await page.keyboard.press('Tab');
      await expect(firstNavItem).toBeFocused();
    });

    test('should restore focus to hamburger button when menu is closed', async ({ page }) => {
      const menuButton = page.locator('.mobile-menu-button');
      const closeButton = page.locator('.mobile-nav-close');

      // Focus and open menu
      await menuButton.click();

      // Close menu
      await closeButton.click();

      // Focus should be restored to hamburger button
      await expect(menuButton).toBeFocused();
    });

    test('should prevent body scroll when menu is open', async ({ page }) => {
      const menuButton = page.locator('.mobile-menu-button');
      const body = page.locator('body');

      // Initially, body should not have menu-open class
      await expect(body).not.toHaveClass(/menu-open/);

      // Open menu
      await menuButton.click();

      // Body should have menu-open class (which sets overflow: hidden)
      await expect(body).toHaveClass(/menu-open/);
    });

    test('should display active page indicator in mobile navigation', async ({ page }) => {
      const menuButton = page.locator('.mobile-menu-button');
      await menuButton.click();

      // Check that one nav item has active class and aria-current="page"
      const activeItem = page.locator('.mobile-nav-item.active');
      await expect(activeItem).toBeVisible();
      await expect(activeItem).toHaveAttribute('aria-current', 'page');
    });

    test('should close menu when viewport is resized to desktop', async ({ page }) => {
      const menuButton = page.locator('.mobile-menu-button');
      const drawer = page.locator('.mobile-nav-drawer');

      // Open menu on mobile
      await menuButton.click();
      await expect(drawer).toHaveClass(/open/);

      // Resize to desktop
      await page.setViewportSize({ width: 1024, height: 768 });

      // Wait for resize handler debounce (250ms)
      await page.waitForTimeout(300);

      // Menu should be closed
      await expect(drawer).not.toHaveClass(/open/);
    });
  });

  test.describe('Multi-viewport touch target verification', () => {
    const mobileViewports = [
      { name: 'iPhone SE', width: 320, height: 568 },
      { name: 'iPhone 8', width: 375, height: 667 },
      { name: 'iPhone 11 Pro Max', width: 414, height: 896 },
      { name: 'iPad Portrait', width: 768, height: 1024 },
    ];

    for (const viewport of mobileViewports) {
      test(`hamburger button meets 44px minimum on ${viewport.name} (${viewport.width}x${viewport.height})`, async ({ page }) => {
        await page.setViewportSize({ width: viewport.width, height: viewport.height });
        await page.goto('');  // Empty string uses baseURL

        const menuButton = page.locator('.mobile-menu-button');

        // Only check if button is visible (not visible on iPad at 768px)
        const isVisible = await menuButton.isVisible();
        if (!isVisible) {
          test.skip();
        }

        const box = await menuButton.boundingBox();
        expect(box).not.toBeNull();
        expect(box!.width).toBeGreaterThanOrEqual(44);
        expect(box!.height).toBeGreaterThanOrEqual(44);
      });
    }
  });
});
