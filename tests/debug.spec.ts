import { test, expect } from '@playwright/test';

test('debug - check page structure', async ({ page }) => {
  console.log('Navigating to empty string (should use baseURL)');
  const response = await page.goto('');
  console.log('Response status:', response?.status());
  console.log('Final URL:', page.url());

  // Take a screenshot
  await page.screenshot({ path: 'test-debug.png', fullPage: true });

  // Get the HTML content
  const html = await page.content();
  console.log('Page HTML length:', html.length);
  console.log('Page title:', await page.title());
  console.log('Has mobile-menu-button:', html.includes('mobile-menu-button'));
  console.log('Has tab-nav-desktop:', html.includes('tab-nav-desktop'));
  console.log('Has mobile-nav-drawer:', html.includes('mobile-nav-drawer'));
  console.log('Has C++ to C Transpiler:', html.includes('C++ to C Transpiler'));

  // Try to find elements
  const menuButton = page.locator('.mobile-menu-button');
  const count = await menuButton.count();
  console.log('Mobile menu button count:', count);

  if (count > 0) {
    const visible = await menuButton.isVisible();
    console.log('Mobile menu button visible:', visible);
  }
});
