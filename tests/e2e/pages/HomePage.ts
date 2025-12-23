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
    this.heading = page.locator('main h1, #main-content h1').first();
    this.navigation = page.locator('nav.tab-nav-desktop');
    this.playgroundLink = page.locator('nav.tab-nav-desktop a[href*="playground"]');
    this.featuresLink = page.locator('nav.tab-nav-desktop a[href*="features"]');
    this.docsLink = page.locator('nav.tab-nav-desktop a[href*="docs"]');
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
