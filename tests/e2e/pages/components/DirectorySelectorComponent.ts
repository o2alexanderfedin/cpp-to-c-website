import { Page, Locator } from '@playwright/test';

export class DirectorySelectorComponent {
  readonly selectButton: Locator;
  readonly selectedPathElement: Locator;
  readonly dropZone: Locator;
  readonly errorMessage: Locator;

  constructor(private page: Page) {
    this.selectButton = page.locator('button.select-button');
    this.selectedPathElement = page.locator('[data-testid="selected-path"]');
    this.dropZone = page.locator('[data-testid="drop-zone"]');
    this.errorMessage = page.locator('.error-message[role="alert"]');
  }

  async clickSelectButton(): Promise<void> {
    await this.selectButton.click();
  }

  async getSelectedPath(): Promise<string> {
    const text = await this.selectedPathElement.textContent();
    return text?.replace('Selected:', '').trim() || '';
  }

  async hasError(): Promise<boolean> {
    return await this.errorMessage.isVisible();
  }

  async getErrorMessage(): Promise<string> {
    return await this.errorMessage.textContent() || '';
  }

  async isDragActive(): Promise<boolean> {
    const className = await this.dropZone.getAttribute('class');
    return className?.includes('drag-active') || false;
  }
}
