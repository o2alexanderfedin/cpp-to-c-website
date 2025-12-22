import { test, expect } from '@playwright/test';
import AxeBuilder from '@axe-core/playwright';
import { HomePage } from '../pages/HomePage';
import { PlaygroundPage } from '../pages/PlaygroundPage';
import { FeaturesPage } from '../pages/FeaturesPage';
import { DocsPage } from '../pages/DocsPage';

test.describe('Accessibility Tests - WCAG 2.1 AA', () => {
  test('homepage should have no accessibility violations', async ({ page }) => {
    const homePage = new HomePage(page);
    await homePage.navigate();

    const accessibilityScanResults = await new AxeBuilder({ page })
      .withTags(['wcag2a', 'wcag2aa', 'wcag21a', 'wcag21aa'])
      .analyze();

    expect(accessibilityScanResults.violations).toEqual([]);
  });

  test('playground page should have no accessibility violations', async ({ page }) => {
    const playgroundPage = new PlaygroundPage(page);
    await playgroundPage.navigate();

    const accessibilityScanResults = await new AxeBuilder({ page })
      .withTags(['wcag2a', 'wcag2aa', 'wcag21a', 'wcag21aa'])
      .analyze();

    expect(accessibilityScanResults.violations).toEqual([]);
  });

  test('features page should have no accessibility violations', async ({ page }) => {
    const featuresPage = new FeaturesPage(page);
    await featuresPage.navigate();

    const accessibilityScanResults = await new AxeBuilder({ page })
      .withTags(['wcag2a', 'wcag2aa', 'wcag21a', 'wcag21aa'])
      .analyze();

    expect(accessibilityScanResults.violations).toEqual([]);
  });

  test('docs page should have no accessibility violations', async ({ page }) => {
    const docsPage = new DocsPage(page);
    await docsPage.navigate();

    const accessibilityScanResults = await new AxeBuilder({ page })
      .withTags(['wcag2a', 'wcag2aa', 'wcag21a', 'wcag21aa'])
      .analyze();

    expect(accessibilityScanResults.violations).toEqual([]);
  });

  test('keyboard navigation should work on homepage', async ({ page }) => {
    const homePage = new HomePage(page);
    await homePage.navigate();

    // Tab through focusable elements
    await page.keyboard.press('Tab');
    let focusedElement = await page.evaluate(() => document.activeElement?.tagName);
    expect(focusedElement).toBeTruthy();

    // Continue tabbing and verify focus moves
    await page.keyboard.press('Tab');
    await page.keyboard.press('Tab');

    // Verify focus visible indicator present
    const hasFocusVisible = await page.evaluate(() => {
      const el = document.activeElement;
      if (!el) return false;
      const styles = window.getComputedStyle(el);
      return styles.outline !== 'none' && styles.outline !== '';
    });
    expect(hasFocusVisible).toBe(true);
  });

  test('keyboard navigation on playground directory selector', async ({ page }) => {
    const playgroundPage = new PlaygroundPage(page);
    await playgroundPage.navigate();

    // Tab to select directory button
    await page.keyboard.press('Tab');
    await page.keyboard.press('Tab'); // May need multiple tabs depending on header

    // Verify we can activate with keyboard
    const selectButton = playgroundPage.directorySelector.selectButton;
    await selectButton.focus();
    const isFocused = await selectButton.evaluate((el) => el === document.activeElement);
    expect(isFocused).toBe(true);
  });

  test('ARIA labels are present on interactive elements', async ({ page }) => {
    const playgroundPage = new PlaygroundPage(page);
    await playgroundPage.navigate();

    // Check select directory button has aria-label
    const selectButton = playgroundPage.directorySelector.selectButton;
    const ariaLabel = await selectButton.getAttribute('aria-label');
    expect(ariaLabel).toBeTruthy();
  });
});
