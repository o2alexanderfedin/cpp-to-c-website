import { test, expect } from '@playwright/test';
import { WizardPage } from '../pages/WizardPage';

test.describe('Wizard Navigation', () => {
  let wizardPage: WizardPage;

  test.beforeEach(async ({ page }) => {
    wizardPage = new WizardPage(page);
    await wizardPage.goto();
  });

  test('displays wizard on playground page', async () => {
    await expect(wizardPage.wizardContainer).toBeVisible();
    await expect(wizardPage.step1Content).toBeVisible();
  });

  test('starts on step 1 by default', async () => {
    const currentStep = await wizardPage.getCurrentStep();
    expect(currentStep).toBe(1);
  });

  test('Next button is enabled on step 1', async () => {
    const isEnabled = await wizardPage.isNextEnabled();
    expect(isEnabled).toBe(true);
  });

  test('Back button is disabled on step 1', async () => {
    const isEnabled = await wizardPage.isBackEnabled();
    expect(isEnabled).toBe(false);
  });

  test('can navigate forward through all steps', async () => {
    // Step 1 → Step 2
    await wizardPage.clickNext();
    expect(await wizardPage.getCurrentStep()).toBe(2);
    await expect(wizardPage.step2Content).toBeVisible();

    // Step 2 → Step 3
    await wizardPage.clickNext();
    expect(await wizardPage.getCurrentStep()).toBe(3);
    await expect(wizardPage.step3Content).toBeVisible();

    // Step 3 → Step 4
    await wizardPage.clickNext();
    expect(await wizardPage.getCurrentStep()).toBe(4);
    await expect(wizardPage.step4Content).toBeVisible();
  });

  test('can navigate backward through all steps', async () => {
    // Navigate to step 4
    await wizardPage.clickNext();
    await wizardPage.clickNext();
    await wizardPage.clickNext();
    expect(await wizardPage.getCurrentStep()).toBe(4);

    // Step 4 → Step 3
    await wizardPage.clickBack();
    expect(await wizardPage.getCurrentStep()).toBe(3);
    await expect(wizardPage.step3Content).toBeVisible();

    // Step 3 → Step 2
    await wizardPage.clickBack();
    expect(await wizardPage.getCurrentStep()).toBe(2);
    await expect(wizardPage.step2Content).toBeVisible();

    // Step 2 → Step 1
    await wizardPage.clickBack();
    expect(await wizardPage.getCurrentStep()).toBe(1);
    await expect(wizardPage.step1Content).toBeVisible();
  });

  test('Next button is disabled on step 4', async () => {
    // Navigate to step 4
    await wizardPage.clickNext();
    await wizardPage.clickNext();
    await wizardPage.clickNext();

    const isEnabled = await wizardPage.isNextEnabled();
    expect(isEnabled).toBe(false);
  });

  test('Back button is enabled on steps 2-4', async () => {
    // Step 2
    await wizardPage.clickNext();
    expect(await wizardPage.isBackEnabled()).toBe(true);

    // Step 3
    await wizardPage.clickNext();
    expect(await wizardPage.isBackEnabled()).toBe(true);

    // Step 4
    await wizardPage.clickNext();
    expect(await wizardPage.isBackEnabled()).toBe(true);
  });

  test('step indicators highlight current step', async () => {
    // Step 1 active
    let activeStep = await wizardPage.getActiveStepNumber();
    expect(activeStep).toBe(1);

    // Step 2 active
    await wizardPage.clickNext();
    activeStep = await wizardPage.getActiveStepNumber();
    expect(activeStep).toBe(2);

    // Step 3 active
    await wizardPage.clickNext();
    activeStep = await wizardPage.getActiveStepNumber();
    expect(activeStep).toBe(3);

    // Step 4 active
    await wizardPage.clickNext();
    activeStep = await wizardPage.getActiveStepNumber();
    expect(activeStep).toBe(4);
  });

  test('can navigate full round trip (1→2→3→4→3→2→1)', async () => {
    // Forward
    await wizardPage.clickNext(); // 1→2
    await wizardPage.clickNext(); // 2→3
    await wizardPage.clickNext(); // 3→4
    expect(await wizardPage.getCurrentStep()).toBe(4);

    // Backward
    await wizardPage.clickBack(); // 4→3
    await wizardPage.clickBack(); // 3→2
    await wizardPage.clickBack(); // 2→1
    expect(await wizardPage.getCurrentStep()).toBe(1);
  });
});

test.describe('Wizard Keyboard Navigation', () => {
  let wizardPage: WizardPage;

  test.beforeEach(async ({ page }) => {
    wizardPage = new WizardPage(page);
    await wizardPage.goto();
  });

  test('can navigate forward with keyboard', async () => {
    await wizardPage.navigateNextWithKeyboard();
    expect(await wizardPage.getCurrentStep()).toBe(2);

    await wizardPage.navigateNextWithKeyboard();
    expect(await wizardPage.getCurrentStep()).toBe(3);
  });

  test('can navigate backward with keyboard', async () => {
    // Navigate to step 3
    await wizardPage.clickNext();
    await wizardPage.clickNext();

    // Navigate back with keyboard
    await wizardPage.navigateBackWithKeyboard();
    expect(await wizardPage.getCurrentStep()).toBe(2);

    await wizardPage.navigateBackWithKeyboard();
    expect(await wizardPage.getCurrentStep()).toBe(1);
  });

  test('buttons have proper focus indicators', async ({ page }) => {
    await wizardPage.nextButton.focus();
    const nextFocused = await page.evaluate(() => {
      const el = document.activeElement;
      return el?.textContent?.toLowerCase().includes('next') || false;
    });
    expect(nextFocused).toBe(true);
  });
});

test.describe('Wizard Accessibility', () => {
  let wizardPage: WizardPage;

  test.beforeEach(async ({ page }) => {
    wizardPage = new WizardPage(page);
    await wizardPage.goto();
  });

  test('navigation buttons have accessible labels', async () => {
    await expect(wizardPage.nextButton).toHaveAccessibleName(/next step/i);
    await expect(wizardPage.backButton).toHaveAccessibleName(/previous step/i);
  });

  test('step content has proper heading structure', async () => {
    await expect(wizardPage.step1Content).toHaveRole('heading');
  });

  test('disabled buttons have proper aria-disabled attribute', async () => {
    // Back button should be disabled on step 1
    await expect(wizardPage.backButton).toBeDisabled();

    // Navigate to step 4
    await wizardPage.clickNext();
    await wizardPage.clickNext();
    await wizardPage.clickNext();

    // Next button should be disabled on step 4
    await expect(wizardPage.nextButton).toBeDisabled();
  });
});
