import { Page, Locator } from '@playwright/test';
import { BasePage } from './BasePage';

export class FeaturesPage extends BasePage {
  readonly heading: Locator;
  readonly featuresList: Locator;

  constructor(page: Page) {
    super(page);
    this.heading = page.locator('h1');
    this.featuresList = page.locator('.features-list, ul');
  }

  async navigate() {
    await super.navigate('/features');
  }

  async getFeatureCount(): Promise<number> {
    const items = await this.featuresList.locator('li, .feature-card').count();
    return items;
  }
}
