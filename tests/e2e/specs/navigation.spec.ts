import { test, expect } from '@playwright/test';
import { HomePage } from '../pages/HomePage';
import { FeaturesPage } from '../pages/FeaturesPage';
import { DocsPage } from '../pages/DocsPage';
import { PlaygroundPage } from '../pages/PlaygroundPage';

test.describe('Navigation Tests', () => {
  test('navigate from homepage to playground', async ({ page }) => {
    const homePage = new HomePage(page);
    await homePage.navigate();

    await homePage.navigateToPlayground();

    // Verify we're on the playground page
    expect(page.url()).toContain('/playground');
    const playgroundPage = new PlaygroundPage(page);
    await expect(playgroundPage.heading).toBeVisible();
  });

  test('navigate from homepage to features', async ({ page }) => {
    const homePage = new HomePage(page);
    await homePage.navigate();

    await homePage.navigateToFeatures();

    // Verify we're on the features page
    expect(page.url()).toContain('/features');
    const featuresPage = new FeaturesPage(page);
    await expect(featuresPage.heading).toBeVisible();
  });

  test('navigate from homepage to docs', async ({ page }) => {
    const homePage = new HomePage(page);
    await homePage.navigate();

    await homePage.navigateToDocs();

    // Verify we're on the docs page
    expect(page.url()).toContain('/docs');
    const docsPage = new DocsPage(page);
    await expect(docsPage.heading).toBeVisible();
  });

  test('all main navigation links are present', async ({ page }) => {
    const homePage = new HomePage(page);
    await homePage.navigate();

    await expect(homePage.navigation).toBeVisible();
    await expect(homePage.playgroundLink).toBeVisible();
    await expect(homePage.featuresLink).toBeVisible();
    await expect(homePage.docsLink).toBeVisible();
  });

  test('browser back navigation works', async ({ page }) => {
    const homePage = new HomePage(page);
    await homePage.navigate();

    await homePage.navigateToFeatures();
    expect(page.url()).toContain('/features');

    await page.goBack();
    expect(page.url()).toBe('http://localhost:4321/');
  });
});
