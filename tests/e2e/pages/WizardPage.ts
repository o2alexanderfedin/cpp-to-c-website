import { Page, Locator } from '@playwright/test';
import { BasePage } from './BasePage';

/**
 * Page Object for Wizard navigation
 *
 * Encapsulates wizard interactions for E2E tests
 */
export class WizardPage extends BasePage {
  readonly wizardContainer: Locator;
  readonly nextButton: Locator;
  readonly backButton: Locator;
  readonly step1Content: Locator;
  readonly step2Content: Locator;
  readonly step3Content: Locator;
  readonly step4Content: Locator;
  readonly stepIndicators: Locator;

  constructor(page: Page) {
    super(page);
    this.wizardContainer = page.locator('.playground-wizard');

    // Navigation buttons - use class selectors for reliability with disabled states
    this.nextButton = page.locator('button.btn-next');
    this.backButton = page.locator('button.btn-back');

    // Step content areas
    this.step1Content = page.getByRole('heading', { name: /step 1.*source/i });
    this.step2Content = page.getByRole('heading', { name: /step 2.*target/i });
    this.step3Content = page.getByRole('heading', { name: /step 3.*transpil/i });
    this.step4Content = page.getByRole('heading', { name: /step 4.*results/i });

    // Step indicator circles
    this.stepIndicators = page.locator('.wizard-step');
  }

  /**
   * Navigate to playground page
   */
  async goto() {
    // Use full path including base to avoid baseURL issues
    await this.page.goto('/cpp-to-c-website/playground');
    await this.waitForLoad();
    // Wait for React component to hydrate (client:only)
    // Wait for actual interactive elements to appear after hydration
    await this.nextButton.waitFor({ state: 'visible', timeout: 15000 });
  }

  /**
   * Click Next button
   */
  async clickNext() {
    await this.nextButton.click();
    // Wait for navigation to complete
    await this.page.waitForTimeout(100);
  }

  /**
   * Click Back button
   */
  async clickBack() {
    await this.backButton.click();
    await this.page.waitForTimeout(100);
  }

  /**
   * Get current step number based on visible content
   */
  async getCurrentStep(): Promise<number> {
    if (await this.step1Content.isVisible()) return 1;
    if (await this.step2Content.isVisible()) return 2;
    if (await this.step3Content.isVisible()) return 3;
    if (await this.step4Content.isVisible()) return 4;
    throw new Error('No step content is visible');
  }

  /**
   * Check if Next button is enabled
   */
  async isNextEnabled(): Promise<boolean> {
    return !(await this.nextButton.isDisabled());
  }

  /**
   * Check if Back button is enabled
   */
  async isBackEnabled(): Promise<boolean> {
    return !(await this.backButton.isDisabled());
  }

  /**
   * Get active step indicator number
   */
  async getActiveStepNumber(): Promise<number> {
    const activeStep = this.page.locator('.step.active .step-number');
    const text = await activeStep.textContent();
    return parseInt(text || '0', 10);
  }

  /**
   * Navigate using keyboard (Tab to Next button, Enter to click)
   */
  async navigateNextWithKeyboard() {
    await this.nextButton.focus();
    await this.page.keyboard.press('Enter');
    await this.page.waitForTimeout(100);
  }

  /**
   * Navigate back using keyboard
   */
  async navigateBackWithKeyboard() {
    await this.backButton.focus();
    await this.page.keyboard.press('Enter');
    await this.page.waitForTimeout(100);
  }
}
