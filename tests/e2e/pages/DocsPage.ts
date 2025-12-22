import { Page, Locator } from '@playwright/test';
import { BasePage } from './BasePage';

export class DocsPage extends BasePage {
  readonly heading: Locator;
  readonly content: Locator;
  readonly codeBlocks: Locator;

  constructor(page: Page) {
    super(page);
    this.heading = page.locator('h1');
    this.content = page.locator('main, .content, article');
    this.codeBlocks = page.locator('pre code, .code-block');
  }

  async navigate() {
    await super.navigate('/docs');
  }

  async getCodeBlockCount(): Promise<number> {
    return await this.codeBlocks.count();
  }
}
