import { Page, Locator } from '@playwright/test';

export class ErrorDisplayComponent {
  readonly element: Locator;
  readonly errorTitle: Locator;
  readonly errorList: Locator;
  readonly copyButton: Locator;
  readonly searchInput: Locator;

  constructor(private page: Page) {
    this.element = page.locator('[data-testid="error-display"]');
    this.errorTitle = this.element.locator('.error-title');
    this.errorList = this.element.locator('.error-list');
    this.copyButton = this.element.locator('.copy-button');
    this.searchInput = this.element.locator('.search-input');
  }

  async hasErrors(): Promise<boolean> {
    const className = await this.element.getAttribute('class');
    return className?.includes('has-errors') || false;
  }

  async getErrorCount(): Promise<number> {
    const titleText = await this.errorTitle.textContent();
    const match = titleText?.match(/(\d+)\s+error/);
    return match ? parseInt(match[1]) : 0;
  }

  async getErrors(): Promise<Array<{ filePath: string; message: string }>> {
    if (!(await this.hasErrors())) return [];

    const errorItems = await this.errorList.locator('.error-item').all();
    const errors = [];

    for (const item of errorItems) {
      const filePath = await item.locator('.error-file-path').textContent();

      // Expand the error to see the message
      await item.locator('.error-item-button').click();

      const message = await item.locator('.error-message').textContent();

      errors.push({
        filePath: filePath?.trim() || '',
        message: message?.trim() || '',
      });
    }

    return errors;
  }

  async isVisible(): Promise<boolean> {
    return await this.element.isVisible();
  }
}
