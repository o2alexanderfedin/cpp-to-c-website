import { Page, Locator } from '@playwright/test';
import AxeBuilder from '@axe-core/playwright';

export class BasePage {
  constructor(protected page: Page) {}

  async navigate(path: string = '/') {
    // Remove leading slash for relative navigation
    // Playwright's baseURL will be prepended automatically
    const relativePath = path.startsWith('/') ? path.slice(1) : path;
    await this.page.goto(relativePath || '');
    await this.waitForLoad();
  }

  async waitForLoad() {
    await this.page.waitForLoadState('domcontentloaded');
  }

  async takeScreenshot(name: string) {
    await this.page.screenshot({
      path: `screenshots/${name}.png`,
      fullPage: true,
    });
  }

  async checkAccessibility() {
    const accessibilityScanResults = await new AxeBuilder({ page: this.page })
      .withTags(['wcag2a', 'wcag2aa', 'wcag21a', 'wcag21aa'])
      .analyze();

    return accessibilityScanResults;
  }

  async getTitle(): Promise<string> {
    return await this.page.title();
  }

  async getUrl(): Promise<string> {
    return this.page.url();
  }
}
