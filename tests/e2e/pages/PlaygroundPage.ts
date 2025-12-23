import { Page, Locator } from '@playwright/test';
import { BasePage } from './BasePage';
import { DirectorySelectorComponent } from './components/DirectorySelectorComponent';
import { ProgressIndicatorComponent } from './components/ProgressIndicatorComponent';
import { ErrorDisplayComponent } from './components/ErrorDisplayComponent';

export class PlaygroundPage extends BasePage {
  readonly directorySelector: DirectorySelectorComponent;
  readonly progressIndicator: ProgressIndicatorComponent;
  readonly errorDisplay: ErrorDisplayComponent;
  readonly transpileButton: Locator;
  readonly heading: Locator;

  constructor(page: Page) {
    super(page);
    this.directorySelector = new DirectorySelectorComponent(page);
    this.progressIndicator = new ProgressIndicatorComponent(page);
    this.errorDisplay = new ErrorDisplayComponent(page);
    this.transpileButton = page.locator('button', { hasText: /transpile/i });
    this.heading = page.locator('main h1, #main-content h1').first();
  }

  async navigate() {
    await super.navigate('/playground');
  }

  async getSelectedPath(): Promise<string> {
    return await this.directorySelector.getSelectedPath();
  }

  async selectDirectory(): Promise<void> {
    // Note: This would trigger the File System Access API picker
    // In headed mode, this requires manual interaction
    // In automated tests, we use mocking via test-helpers
    await this.directorySelector.clickSelectButton();
  }

  async startTranspilation(): Promise<void> {
    await this.transpileButton.click();
  }

  async waitForCompletion(timeout: number = 30000): Promise<void> {
    await this.progressIndicator.waitForComplete(timeout);
  }

  async cancelTranspilation(): Promise<void> {
    await this.progressIndicator.clickCancel();
  }

  async getTranspilationProgress(): Promise<{
    percentage: number;
    current: number;
    total: number;
  }> {
    const percentage = await this.progressIndicator.getPercentage();
    const fileCount = await this.progressIndicator.getFileCount();
    return {
      percentage,
      ...fileCount,
    };
  }

  async hasErrors(): Promise<boolean> {
    return await this.errorDisplay.hasErrors();
  }

  async getErrors() {
    return await this.errorDisplay.getErrors();
  }
}
