import { test, expect } from '@playwright/test';
import { WizardPage } from '../pages/WizardPage';
import { smallProject, generateLargeProject } from '../fixtures/projects';
import { mockFileSystemAccessAPI } from '../utils/test-helpers';

/**
 * E2E tests for the complete wizard flow
 *
 * These tests verify the wizard can navigate through all 4 steps and handle
 * various scenarios including file selection, navigation, and UI states.
 *
 * Note: Full transpilation testing requires WASM module to be functional.
 * These tests focus on UI behavior and navigation.
 */
test.describe('Wizard Complete Flow', () => {
  let wizardPage: WizardPage;

  test.beforeEach(async ({ page }) => {
    wizardPage = new WizardPage(page);
  });

  test('navigates through all wizard steps', async ({ page }) => {
    // Setup mock BEFORE navigating
    const filesMap = new Map(smallProject.files.map(f => [f.name, f.content]));
    await mockFileSystemAccessAPI(page, {
      directoryName: smallProject.name,
      files: filesMap
    });

    // Navigate to the page
    await wizardPage.goto();

    // Step 1: Select source directory
    const selectButton = page.locator('button', { hasText: /Select.*Directory/i }).first();
    await selectButton.click();

    // Verify tree shows files
    await expect(wizardPage.fileTree).toBeVisible({ timeout: 10000 });

    // Step 2: Navigate to target selection
    await wizardPage.goToNextStep();
    await expect(wizardPage.step2Content).toBeVisible();

    // Step 3: Navigate to transpilation
    await wizardPage.goToNextStep();
    await expect(wizardPage.step3Content).toBeVisible();

    // Step 4: Navigate to results
    await wizardPage.goToNextStep();
    await expect(wizardPage.step4Content).toBeVisible();
  });

  test('displays file tree after directory selection', async ({ page }) => {
    const filesMap = new Map(smallProject.files.map(f => [f.name, f.content]));
    await mockFileSystemAccessAPI(page, {
      directoryName: smallProject.name,
      files: filesMap
    });

    await wizardPage.goto();

    // Select directory
    const selectButton = page.locator('button', { hasText: /Select.*Directory/i }).first();
    await selectButton.click();

    // Verify tree is visible
    await expect(wizardPage.fileTree).toBeVisible({ timeout: 10000 });

    // Verify at least one file is shown
    const treeNodes = page.locator('.tree-node, [data-testid="tree-node"]');
    await expect(treeNodes.first()).toBeVisible();
  });

  test('shows empty state on step 4 without transpilation', async ({ page }) => {
    await wizardPage.goto();

    // Navigate directly to step 4
    await wizardPage.goToStep(4);

    // Verify we're on step 4
    await expect(wizardPage.step4Content).toBeVisible();

    // Empty state or no results message should be visible
    // (exact message depends on implementation)
    const resultsSection = page.locator('[data-testid="step4-results"], .step4-results');
    await expect(resultsSection).toBeVisible();
  });

  test('handles large project file list', async ({ page }) => {
    const largeProj = generateLargeProject(50);
    const filesMap = new Map(largeProj.files.map(f => [f.name, f.content]));

    await mockFileSystemAccessAPI(page, {
      directoryName: largeProj.name,
      files: filesMap
    });

    await wizardPage.goto();

    // Select directory
    const selectButton = page.locator('button', { hasText: /Select.*Directory/i }).first();
    await selectButton.click();

    // Verify tree is visible even with many files
    await expect(wizardPage.fileTree).toBeVisible({ timeout: 10000 });

    // Verify tree renders (may be virtualized)
    const treeNodes = page.locator('.tree-node, [data-testid="tree-node"]');
    const count = await treeNodes.count();
    expect(count).toBeGreaterThan(0);
  });

  test('back button works from step 2', async ({ page }) => {
    const filesMap = new Map(smallProject.files.map(f => [f.name, f.content]));
    await mockFileSystemAccessAPI(page, {
      directoryName: smallProject.name,
      files: filesMap
    });

    await wizardPage.goto();

    // Select directory and go to step 2
    const selectButton = page.locator('button', { hasText: /Select.*Directory/i }).first();
    await selectButton.click();
    await expect(wizardPage.fileTree).toBeVisible({ timeout: 10000 });

    await wizardPage.goToNextStep();
    await expect(wizardPage.step2Content).toBeVisible();

    // Go back to step 1
    await wizardPage.clickBack();
    await expect(wizardPage.step1Content).toBeVisible();

    // File tree should still be visible
    await expect(wizardPage.fileTree).toBeVisible();
  });

  test('displays wizard steps in correct order', async ({ page }) => {
    await wizardPage.goto();

    // Verify step 1 is shown first
    expect(await wizardPage.getCurrentStep()).toBe(1);

    // Navigate forward
    await wizardPage.goToNextStep();
    expect(await wizardPage.getCurrentStep()).toBe(2);

    await wizardPage.goToNextStep();
    expect(await wizardPage.getCurrentStep()).toBe(3);

    await wizardPage.goToNextStep();
    expect(await wizardPage.getCurrentStep()).toBe(4);
  });

  test('responsive layout at different viewport sizes', async ({ page }) => {
    await wizardPage.goto();

    // Desktop size
    await page.setViewportSize({ width: 1920, height: 1080 });
    await expect(wizardPage.wizardContainer).toBeVisible();

    // Tablet size
    await page.setViewportSize({ width: 768, height: 1024 });
    await expect(wizardPage.wizardContainer).toBeVisible();

    // Mobile size
    await page.setViewportSize({ width: 375, height: 667 });
    await expect(wizardPage.wizardContainer).toBeVisible();
  });

  test('wizard maintains state when navigating back and forth', async ({ page }) => {
    const filesMap = new Map(smallProject.files.map(f => [f.name, f.content]));
    await mockFileSystemAccessAPI(page, {
      directoryName: smallProject.name,
      files: filesMap
    });

    await wizardPage.goto();

    // Step 1: Select directory
    const selectButton = page.locator('button', { hasText: /Select.*Directory/i }).first();
    await selectButton.click();
    await expect(wizardPage.fileTree).toBeVisible({ timeout: 10000 });

    // Go to step 2 and back to step 1
    await wizardPage.goToNextStep();
    await wizardPage.clickBack();

    // File tree should still be visible (state maintained)
    await expect(wizardPage.fileTree).toBeVisible();

    // Go forward again
    await wizardPage.goToNextStep();
    await expect(wizardPage.step2Content).toBeVisible();
  });

  test('statistics component exists on step 1', async ({ page }) => {
    const filesMap = new Map(smallProject.files.map(f => [f.name, f.content]));
    await mockFileSystemAccessAPI(page, {
      directoryName: smallProject.name,
      files: filesMap
    });

    await wizardPage.goto();

    // Select directory
    const selectButton = page.locator('button', { hasText: /Select.*Directory/i }).first();
    await selectButton.click();
    await expect(wizardPage.fileTree).toBeVisible({ timeout: 10000 });

    // File statistics should be visible
    const stats = page.locator('.file-statistics, [data-testid="file-statistics"]');
    await expect(stats).toBeVisible();
  });

  test('wizard has proper navigation buttons', async ({ page }) => {
    await wizardPage.goto();

    // Verify Next button exists and is enabled
    await expect(wizardPage.nextButton).toBeVisible();
    expect(await wizardPage.isNextEnabled()).toBe(true);

    // Verify Back button exists and is disabled on step 1
    await expect(wizardPage.backButton).toBeVisible();
    expect(await wizardPage.isBackEnabled()).toBe(false);

    // Navigate forward
    await wizardPage.goToNextStep();

    // Back should now be enabled
    expect(await wizardPage.isBackEnabled()).toBe(true);
  });

  test('step indicators show current progress', async ({ page }) => {
    await wizardPage.goto();

    // Verify step indicators are visible
    await expect(wizardPage.stepIndicators.first()).toBeVisible();

    // Active step should be 1
    expect(await wizardPage.getActiveStepNumber()).toBe(1);

    // Navigate to step 2
    await wizardPage.goToNextStep();
    expect(await wizardPage.getActiveStepNumber()).toBe(2);
  });
});
