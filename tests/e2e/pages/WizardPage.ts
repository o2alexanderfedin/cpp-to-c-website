import type { Page, Locator } from '@playwright/test';
import { expect } from '@playwright/test';
import { BasePage } from './BasePage';
import type { TestProject } from '../fixtures/projects';

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

  // Step 2: Target Selection
  readonly selectTargetDirButton: Locator;
  readonly selectedTargetDir: Locator;
  readonly permissionIndicator: Locator;
  readonly conflictWarning: Locator;
  readonly proceedAnywayButton: Locator;
  readonly chooseDifferentDirButton: Locator;
  readonly targetStandardSelect: Locator;
  readonly acslCheckbox: Locator;

  // Step 3: Transpilation
  readonly progressBar: Locator;
  readonly progressFill: Locator;
  readonly progressText: Locator;
  readonly currentFile: Locator;
  readonly pauseButton: Locator;
  readonly resumeButton: Locator;
  readonly cancelButton: Locator;
  readonly metricsElapsed: Locator;
  readonly metricsSpeed: Locator;
  readonly metricsETA: Locator;
  readonly fileTree: Locator;
  readonly completionMessage: Locator;
  readonly errorMessage: Locator;

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

    // Step 2 selectors
    this.selectTargetDirButton = page.getByRole('button', { name: /select target directory/i });
    this.selectedTargetDir = page.locator('.selected-directory');
    this.permissionIndicator = page.locator('.permission-indicator');
    this.conflictWarning = page.locator('.conflict-warning');
    this.proceedAnywayButton = page.getByRole('button', { name: /proceed anyway/i });
    this.chooseDifferentDirButton = page.getByRole('button', { name: /choose different directory/i });
    this.targetStandardSelect = page.locator('select[name="targetStandard"]');
    this.acslCheckbox = page.getByRole('checkbox', { name: /include acsl/i });

    // Step 3 selectors
    this.progressBar = page.locator('.progress-bar');
    this.progressFill = page.locator('.progress-fill');
    this.progressText = page.locator('.progress-text');
    this.currentFile = page.locator('.current-file code');
    this.pauseButton = page.getByRole('button', { name: /pause/i });
    this.resumeButton = page.getByRole('button', { name: /resume/i });
    this.cancelButton = page.getByRole('button', { name: /cancel/i });
    this.metricsElapsed = page.locator('.metric-elapsed .metric-value');
    this.metricsSpeed = page.locator('.metric-speed .metric-value');
    this.metricsETA = page.locator('.metric-eta .metric-value');
    this.fileTree = page.locator('.file-tree-view');
    this.completionMessage = page.locator('.completion-message');
    this.errorMessage = page.locator('.error-message');
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

  // Step 2: Target Selection Actions

  /**
   * Select target directory
   * Note: File System Access API cannot be fully automated in Playwright
   * This would need to be mocked or use a test-specific API
   */
  async selectTargetDirectory() {
    await this.selectTargetDirButton.click();
  }

  /**
   * Set target C standard
   */
  async setTargetStandard(standard: 'c99' | 'c11') {
    await this.targetStandardSelect.selectOption(standard);
  }

  /**
   * Toggle ACSL checkbox
   */
  async toggleACSL() {
    await this.acslCheckbox.click();
  }

  /**
   * Proceed with conflicts acknowledgment
   */
  async proceedWithConflicts() {
    await this.proceedAnywayButton.click();
  }

  // Step 3: Transpilation Actions

  /**
   * Wait for transpilation to start
   */
  async waitForTranspilationStart() {
    await expect(this.progressBar).toBeVisible({ timeout: 5000 });
  }

  /**
   * Pause transpilation
   */
  async pauseTranspilation() {
    await this.pauseButton.click();
  }

  /**
   * Resume transpilation
   */
  async resumeTranspilation() {
    await this.resumeButton.click();
  }

  /**
   * Cancel transpilation
   */
  async cancelTranspilation() {
    await this.cancelButton.click();
  }

  /**
   * Wait for transpilation to complete
   */
  async waitForTranspilationComplete() {
    await expect(this.completionMessage).toBeVisible({ timeout: 30000 });
  }

  /**
   * Get current progress percentage
   */
  async getProgressPercentage(): Promise<number> {
    const text = await this.progressText.textContent();
    const match = text?.match(/(\d+)%/);
    return match ? parseInt(match[1], 10) : 0;
  }

  /**
   * Get current file being transpiled
   */
  async getCurrentFile(): Promise<string | null> {
    try {
      return await this.currentFile.textContent();
    } catch {
      return null;
    }
  }

  // Step 2 & 3 Assertions

  /**
   * Assert target directory is selected
   */
  async assertTargetDirectorySelected(dirName: string) {
    await expect(this.selectedTargetDir).toContainText(dirName);
  }

  /**
   * Assert permissions are granted
   */
  async assertPermissionsGranted() {
    await expect(this.permissionIndicator).toContainText('✓ Read');
    await expect(this.permissionIndicator).toContainText('✓ Write');
  }

  /**
   * Assert conflict warning is visible
   */
  async assertConflictWarningVisible(expectedConflicts: number) {
    await expect(this.conflictWarning).toBeVisible();
    await expect(this.conflictWarning).toContainText(`${expectedConflicts}`);
  }

  /**
   * Assert progress bar is visible
   */
  async assertProgressBarVisible() {
    await expect(this.progressBar).toBeVisible();
  }

  /**
   * Assert transpilation is complete
   */
  async assertTranspilationComplete() {
    await expect(this.completionMessage).toBeVisible();
    await expect(this.completionMessage).toContainText(/complete/i);
  }

  // Step 4: Results Page Methods

  /**
   * Get statistics from results page
   */
  async getStatistics() {
    const statsContainer = this.page.locator('.file-statistics, [data-testid="file-statistics"]');
    await statsContainer.waitFor({ state: 'visible', timeout: 5000 });

    const totalText = await this.page.locator('.stat-total .stat-value, [data-testid="stat-total"]').textContent();
    const successText = await this.page.locator('.stat-success .stat-value, [data-testid="stat-success"]').textContent();

    return {
      total: totalText?.trim() || '0',
      successful: successText?.trim() || '0'
    };
  }

  /**
   * Select file from tree
   */
  async selectFileInTree(filename: string) {
    await this.page.locator('.tree-node', { hasText: filename }).first().click();
    // Wait for selection to register
    await this.page.waitForTimeout(200);
  }

  /**
   * Get selected file in dual-pane viewer
   */
  async getSelectedFileInViewer() {
    const sourceFilename = await this.page.locator('.file-content-header .file-content-filename, [data-testid="source-filename"]').first().textContent();
    return sourceFilename?.trim() || '';
  }

  /**
   * Check if file content is displayed
   */
  async isFileContentDisplayed() {
    const sourceContent = await this.page.locator('.syntax-highlighter, [data-testid="syntax-highlighter"]').first().textContent();
    return sourceContent !== null && sourceContent.length > 0;
  }

  /**
   * Click download ZIP button
   */
  async downloadAllAsZip() {
    await this.page.locator('button', { hasText: /Download All as ZIP/i }).click();
  }

  /**
   * Click download current file button
   */
  async downloadCurrentFile() {
    await this.page.locator('button', { hasText: /Download.*\.c/i }).click();
  }

  /**
   * Get error count from error summary
   */
  async getErrorCount() {
    const errorHeader = await this.page.locator('.error-summary h3, [data-testid="error-summary-header"]').textContent();
    const match = errorHeader?.match(/\((\d+)\)/);
    return match ? parseInt(match[1], 10) : 0;
  }

  /**
   * Click error file link
   */
  async clickErrorFile(filename: string) {
    await this.page.locator('.error-file-link, [data-testid="error-file-link"]', { hasText: filename }).click();
  }

  /**
   * Check if metrics are displayed
   */
  async areMetricsDisplayed() {
    return await this.page.locator('.metrics-section, [data-testid="metrics-section"]').isVisible();
  }

  /**
   * Check if download options are displayed
   */
  async areDownloadOptionsDisplayed() {
    return await this.page.locator('.download-section, [data-testid="download-section"]').isVisible();
  }

  // Navigation Helper Methods

  /**
   * Navigate to specific step
   */
  async goToStep(stepNumber: number) {
    const current = await this.getCurrentStep();

    if (stepNumber > current) {
      // Navigate forward
      for (let i = current; i < stepNumber; i++) {
        await this.clickNext();
      }
    } else if (stepNumber < current) {
      // Navigate backward
      for (let i = current; i > stepNumber; i--) {
        await this.clickBack();
      }
    }
  }

  /**
   * Go to next step
   */
  async goToNextStep() {
    await this.clickNext();
  }

  // Test Helper Methods

  /**
   * Complete Steps 1-3 (transpilation) for a test project
   * Helper method to set up Step 4 tests
   *
   * NOTE: This uses the existing mockFileSystemAccessAPI pattern from test-helpers
   */
  async completeTranspilation(project: TestProject) {
    // Setup mock BEFORE page loads
    const filesMap = new Map(project.files.map(f => [f.name, f.content]));

    await this.page.addInitScript(({ directoryName, filesObj }) => {
      const files = new Map(Object.entries(filesObj));

      // Mock showDirectoryPicker
      (window as any).showDirectoryPicker = async () => {
        const mockFileHandles: any[] = [];

        // Create mock file handles
        for (const [name, content] of files) {
          mockFileHandles.push({
            kind: 'file',
            name,
            async getFile() {
              return new File([content], name, { type: 'text/plain' });
            },
          });
        }

        // Return mock directory handle
        return {
          kind: 'directory',
          name: directoryName,
          async *values() {
            for (const handle of mockFileHandles) {
              yield handle;
            }
          },
          async getFileHandle(name: string) {
            const handle = mockFileHandles.find((h) => h.name === name);
            if (!handle) {
              throw new Error(`File not found: ${name}`);
            }
            return handle;
          },
        };
      };
    }, {
      directoryName: project.name,
      filesObj: Object.fromEntries(filesMap),
    });

    // Step 1: Source - select directory
    await this.goToStep(1);

    // Click select directory button
    const selectButton = this.page.locator('button', { hasText: /Select.*Directory/i }).first();
    await selectButton.click();

    // Wait for file tree to appear
    await expect(this.fileTree).toBeVisible({ timeout: 10000 });

    // Step 2: Target
    await this.goToNextStep();

    // Mock target directory - simpler approach
    await this.page.evaluate(() => {
      // Mock target directory selection to auto-proceed
      const mockTargetHandle = {
        kind: 'directory',
        name: 'target-directory',
      };
      (window as any).__mockTargetSelected = mockTargetHandle;
    });

    await this.selectTargetDirButton.click();

    // Step 3: Transpile
    await this.goToNextStep();
    await this.startTranspilation();

    // Wait for transpilation to complete
    await this.waitForTranspilationComplete();

    // Navigate to Step 4
    await this.goToNextStep();
  }

  /**
   * Mock source directory selection for testing
   * Injects test data via page.evaluate
   */
  async selectSourceDirectoryMock(project: TestProject) {
    // Mock File System Access API with test data
    await this.page.addInitScript((projectData) => {
      const files = new Map(projectData.files.map((f: any) => [f.name, f.content]));

      // Mock showDirectoryPicker
      (window as any).showDirectoryPicker = async () => {
        const mockFileHandles: any[] = [];

        // Create mock file handles
        for (const [name, content] of files) {
          mockFileHandles.push({
            kind: 'file',
            name,
            async getFile() {
              return new File([content], name, { type: 'text/plain' });
            },
          });
        }

        // Return mock directory handle
        return {
          kind: 'directory',
          name: projectData.name,
          async *values() {
            for (const handle of mockFileHandles) {
              yield handle;
            }
          },
          async getFileHandle(name: string) {
            const handle = mockFileHandles.find((h) => h.name === name);
            if (!handle) {
              throw new Error(`File not found: ${name}`);
            }
            return handle;
          },
        };
      };
    }, project);

    // Click select directory button
    const selectButton = this.page.locator('button', { hasText: /Select.*Directory/i }).first();
    await selectButton.click();
  }

  /**
   * Mock target directory selection for testing
   */
  async selectTargetDirectoryMock() {
    // Mock target directory selection
    await this.page.evaluate(() => {
      (window as any).__mockTargetDirectory = true;
    });

    // Click select target directory button
    await this.selectTargetDirButton.click();
  }

  /**
   * Start transpilation
   */
  async startTranspilation() {
    // The transpilation should start automatically when we navigate to Step 3
    // or we might need to click a start button
    const startButton = this.page.locator('button', { hasText: /Start.*Transpil/i });

    // Check if start button exists and is visible
    const isVisible = await startButton.isVisible().catch(() => false);

    if (isVisible) {
      await startButton.click();
    }
  }
}
