import { test, expect } from '@playwright/test';
import { WizardPage } from '../pages/WizardPage';

test.describe('Wizard - Step 2: Target Selection', () => {
  let wizardPage: WizardPage;

  test.beforeEach(async ({ page }) => {
    wizardPage = new WizardPage(page);
    await wizardPage.goto();

    // Navigate to Step 2
    await wizardPage.clickNext();
  });

  test('displays Step 2 content', async () => {
    const currentStep = await wizardPage.getCurrentStep();
    expect(currentStep).toBe(2);
    await expect(wizardPage.step2Content).toBeVisible();
  });

  test('displays target directory selection button', async () => {
    await expect(wizardPage.selectTargetDirButton).toBeVisible();
  });

  test('allows changing transpilation options', async () => {
    // Change target standard to C11
    await wizardPage.setTargetStandard('c11');
    await expect(wizardPage.targetStandardSelect).toHaveValue('c11');

    // Change back to C99
    await wizardPage.setTargetStandard('c99');
    await expect(wizardPage.targetStandardSelect).toHaveValue('c99');
  });

  test('ACSL checkbox can be toggled', async () => {
    const initialState = await wizardPage.acslCheckbox.isChecked();

    await wizardPage.toggleACSL();
    const toggledState = await wizardPage.acslCheckbox.isChecked();
    expect(toggledState).toBe(!initialState);

    await wizardPage.toggleACSL();
    const revertedState = await wizardPage.acslCheckbox.isChecked();
    expect(revertedState).toBe(initialState);
  });

  test('can navigate back to Step 1', async () => {
    await wizardPage.clickBack();
    const currentStep = await wizardPage.getCurrentStep();
    expect(currentStep).toBe(1);
  });

  test('can navigate forward to Step 3', async () => {
    await wizardPage.clickNext();
    const currentStep = await wizardPage.getCurrentStep();
    expect(currentStep).toBe(3);
  });
});

test.describe('Wizard - Step 2: Target Directory Selection', () => {
  let wizardPage: WizardPage;

  test.beforeEach(async ({ page }) => {
    wizardPage = new WizardPage(page);
    await wizardPage.goto();
    await wizardPage.clickNext();
  });

  /**
   * Note: Full E2E testing of File System Access API requires either:
   * 1. Browser automation extensions (Chrome DevTools Protocol)
   * 2. Test fixtures with pre-selected directories
   * 3. Mocked File System Access API for test environment
   *
   * The following tests are structured to work when the implementation
   * includes test-specific hooks or mocking.
   */

  test.skip('shows permission indicator after directory selection', async () => {
    // This test requires mocking File System Access API
    // await wizardPage.selectTargetDirectory();
    // await wizardPage.assertTargetDirectorySelected('test-output');
    // await wizardPage.assertPermissionsGranted();
  });

  test.skip('detects conflicts and requires acknowledgment', async () => {
    // This test requires a mocked directory with existing files
    // await wizardPage.selectTargetDirectory(); // Directory with conflicts
    // await wizardPage.assertConflictWarningVisible(3); // 3 conflicts
    // await expect(wizardPage.nextButton).toBeDisabled();
    //
    // await wizardPage.proceedWithConflicts();
    // await expect(wizardPage.nextButton).toBeEnabled();
  });

  test.skip('allows proceeding when no conflicts detected', async () => {
    // This test requires a mocked empty directory
    // await wizardPage.selectTargetDirectory(); // Empty directory
    // await expect(wizardPage.conflictWarning).toContainText(/no conflicts/i);
    // await expect(wizardPage.nextButton).toBeEnabled();
  });

  test.skip('allows choosing a different directory after conflict', async () => {
    // This test requires mocked directories
    // await wizardPage.selectTargetDirectory(); // Directory with conflicts
    // await wizardPage.assertConflictWarningVisible(3);
    //
    // await wizardPage.chooseDifferentDirButton.click();
    // // Should clear selection and allow selecting again
    // await expect(wizardPage.selectedTargetDir).not.toBeVisible();
  });
});

test.describe('Wizard - Step 2: Accessibility', () => {
  let wizardPage: WizardPage;

  test.beforeEach(async ({ page }) => {
    wizardPage = new WizardPage(page);
    await wizardPage.goto();
    await wizardPage.clickNext();
  });

  test('target standard select has accessible label', async ({ page }) => {
    await expect(wizardPage.targetStandardSelect).toBeVisible();
    // Should have associated label
    const label = page.locator('label[for*="targetStandard"]');
    await expect(label).toBeVisible();
  });

  test('ACSL checkbox has accessible label', async () => {
    await expect(wizardPage.acslCheckbox).toBeVisible();
    // Checkbox should have accessible name
    await expect(wizardPage.acslCheckbox).toHaveAccessibleName(/acsl/i);
  });

  test('buttons have proper ARIA attributes', async () => {
    await expect(wizardPage.selectTargetDirButton).toHaveAttribute('type', 'button');
  });
});

test.describe('Wizard - Step 2: Keyboard Navigation', () => {
  let wizardPage: WizardPage;

  test.beforeEach(async ({ page }) => {
    wizardPage = new WizardPage(page);
    await wizardPage.goto();
    await wizardPage.clickNext();
  });

  test('can navigate options with keyboard', async ({ page }) => {
    // Focus on target standard select
    await wizardPage.targetStandardSelect.focus();

    // Change value with keyboard
    await page.keyboard.press('ArrowDown');

    // Verify keyboard interaction works
    const isFocused = await page.evaluate(() => {
      const el = document.activeElement;
      return el?.tagName === 'SELECT';
    });
    expect(isFocused).toBe(true);
  });

  test('can toggle ACSL with keyboard (Space)', async ({ page }) => {
    await wizardPage.acslCheckbox.focus();

    const initialState = await wizardPage.acslCheckbox.isChecked();

    await page.keyboard.press('Space');

    const toggledState = await wizardPage.acslCheckbox.isChecked();
    expect(toggledState).toBe(!initialState);
  });
});
