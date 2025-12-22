import { Page, Locator } from '@playwright/test';
import { BasePage } from './BasePage';

export class HomePage extends BasePage {
  readonly heading: Locator;
  readonly navigation: Locator;
  readonly playgroundLink: Locator;
  readonly featuresLink: Locator;
  readonly docsLink: Locator;

  constructor(page: Page) {
    super(page);
    this.heading = page.locator('h1');
    this.navigation = page.locator('nav');
    this.playgroundLink = page.locator('a[href*="playground"]');
    this.featuresLink = page.locator('a[href*="features"]');
    this.docsLink = page.locator('a[href*="docs"]');
  }

  async navigate() {
    await super.navigate('/');
  }

  async navigateToPlayground(): Promise<void> {
    await this.playgroundLink.click();
  }

  async navigateToFeatures(): Promise<void> {
    await this.featuresLink.click();
  }

  async navigateToDocs(): Promise<void> {
    await this.docsLink.click();
  }
}
