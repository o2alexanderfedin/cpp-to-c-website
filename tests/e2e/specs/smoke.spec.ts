import { test, expect } from '@playwright/test';
import { BasePage } from '../pages/BasePage';

test.describe('Smoke Tests', () => {
  let basePage: BasePage;

  test.beforeEach(async ({ page }) => {
    basePage = new BasePage(page);
  });

  test('homepage loads successfully', async ({ page }) => {
    await basePage.navigate('/');

    // Verify page title
    const title = await basePage.getTitle();
    expect(title).toBeTruthy();
    expect(title.length).toBeGreaterThan(0);

    // Verify page loaded
    const url = await basePage.getUrl();
    expect(url).toContain('localhost:4321');
  });

  test('homepage has main navigation', async ({ page }) => {
    await basePage.navigate('/');

    // Check for navigation elements
    const nav = page.locator('nav.tab-nav-desktop');
    await expect(nav).toBeVisible();
  });

  test('playground page loads', async ({ page }) => {
    await basePage.navigate('/playground');

    // Verify playground page loaded
    const heading = page.locator('main h1, #main-content h1').first();
    await expect(heading).toBeVisible();
  });

  test('features page loads', async ({ page }) => {
    await basePage.navigate('/features');

    // Verify features page loaded
    const heading = page.locator('main h1, #main-content h1').first();
    await expect(heading).toBeVisible();
  });

  test('docs page loads', async ({ page }) => {
    await basePage.navigate('/docs');

    // Verify docs page loaded
    const heading = page.locator('main h1, #main-content h1').first();
    await expect(heading).toBeVisible();
  });
});
