import { test, expect } from '@playwright/test';
import { PlaygroundPage } from '../pages/PlaygroundPage';
import { mockFileSystemAccessAPI } from '../utils/test-helpers';

test.describe('Playground Tests', () => {
  test('playground page loads successfully', async ({ page }) => {
    const playgroundPage = new PlaygroundPage(page);
    await playgroundPage.navigate();

    await expect(playgroundPage.heading).toBeVisible();
    await expect(playgroundPage.directorySelector.selectButton).toBeVisible();
  });

  test('directory selector displays correctly', async ({ page }) => {
    const playgroundPage = new PlaygroundPage(page);
    await playgroundPage.navigate();

    // Verify directory selector components
    await expect(playgroundPage.directorySelector.selectButton).toBeVisible();
    await expect(playgroundPage.directorySelector.dropZone).toBeVisible();
  });

  test('select directory button is clickable', async ({ page }) => {
    const playgroundPage = new PlaygroundPage(page);
    await playgroundPage.navigate();

    // Button should be enabled
    const isEnabled = await playgroundPage.directorySelector.selectButton.isEnabled();
    expect(isEnabled).toBe(true);

    // NOTE: Clicking will open native file picker in headed mode
    // In real tests, we would mock the File System Access API
  });

  test.skip('complete transpilation workflow - MANUAL TEST', async ({ page }) => {
    // This test requires manual interaction in headed mode
    // Skipped for automated runs

    const playgroundPage = new PlaygroundPage(page);
    await playgroundPage.navigate();

    // MANUAL: Click select directory and choose small-project
    await playgroundPage.selectDirectory();

    // Wait for manual selection (30 seconds)
    await page.waitForTimeout(30000);

    // Continue automated testing after manual selection
    const selectedPath = await playgroundPage.getSelectedPath();
    expect(selectedPath).toBeTruthy();
  });

  test('error display component is present', async ({ page }) => {
    const playgroundPage = new PlaygroundPage(page);
    await playgroundPage.navigate();

    // Error display should be visible (even if showing no errors)
    await expect(playgroundPage.errorDisplay.element).toBeVisible();
  });

  test('transpile button is present', async ({ page }) => {
    const playgroundPage = new PlaygroundPage(page);
    await playgroundPage.navigate();

    // Transpile button should be visible
    await expect(playgroundPage.transpileButton).toBeVisible();
  });
});

test.describe('Playground Tests with Mocked File System API', () => {
  test('transpile small project with mocked API', async ({ page }) => {
    // Mock the File System Access API
    await mockFileSystemAccessAPI(page, {
      directoryName: 'small-project',
      files: new Map([
        ['main.cpp', 'int main() { return 0; }'],
        ['utils.h', '#pragma once\nvoid helper();'],
        ['utils.cpp', '#include "utils.h"\nvoid helper() {}'],
      ]),
    });

    const playgroundPage = new PlaygroundPage(page);
    await playgroundPage.navigate();

    // Select directory (will use mocked API)
    await playgroundPage.selectDirectory();

    // Verify directory selected
    await page.waitForTimeout(1000);
    const selectedPath = await playgroundPage.getSelectedPath();
    expect(selectedPath).toContain('small-project');
  });
});
