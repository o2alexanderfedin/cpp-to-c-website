import { Page, Locator } from '@playwright/test';

export class ProgressIndicatorComponent {
  readonly element: Locator;
  readonly percentage: Locator;
  readonly count: Locator;
  readonly currentFile: Locator;
  readonly statusMessage: Locator;
  readonly cancelButton: Locator;
  readonly progressBar: Locator;
  readonly progressBarFill: Locator;

  constructor(private page: Page) {
    this.element = page.locator('[data-testid="progress-indicator"]');
    this.percentage = this.element.locator('.percentage');
    this.count = this.element.locator('.count');
    this.currentFile = page.locator('[data-testid="current-file"]');
    this.statusMessage = page.locator('[data-testid="status-message"]');
    this.cancelButton = this.element.locator('.cancel-button');
    this.progressBar = this.element.locator('.progress-bar');
    this.progressBarFill = page.locator('[data-testid="progress-bar-fill"]');
  }

  async isVisible(): Promise<boolean> {
    return await this.element.isVisible();
  }

  async getPercentage(): Promise<number> {
    const text = await this.percentage.textContent();
    return parseInt(text?.replace('%', '') || '0');
  }

  async getFileCount(): Promise<{ current: number; total: number }> {
    const text = await this.count.textContent();
    const match = text?.match(/(\d+)\s*\/\s*(\d+)/);
    if (!match) return { current: 0, total: 0 };
    return {
      current: parseInt(match[1]),
      total: parseInt(match[2]),
    };
  }

  async getCurrentFile(): Promise<string> {
    if (!(await this.currentFile.isVisible())) return '';
    const text = await this.currentFile.textContent();
    return text?.replace('Processing:', '').trim() || '';
  }

  async getStatusMessage(): Promise<string> {
    if (!(await this.statusMessage.isVisible())) return '';
    return await this.statusMessage.textContent() || '';
  }

  async clickCancel(): Promise<void> {
    await this.cancelButton.click();
  }

  async isComplete(): Promise<boolean> {
    const className = await this.element.getAttribute('class');
    return className?.includes('complete') || false;
  }

  async isCancelling(): Promise<boolean> {
    const className = await this.element.getAttribute('class');
    return className?.includes('cancelling') || false;
  }

  async waitForComplete(timeout: number = 30000): Promise<void> {
    await this.element.waitFor({ state: 'visible' });
    await this.page.waitForFunction(
      (selector) => {
        const element = document.querySelector(selector);
        return element?.classList.contains('complete');
      },
      this.element,
      { timeout }
    );
  }
}
