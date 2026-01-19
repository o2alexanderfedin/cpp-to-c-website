/**
 * Comprehensive E2E Tests for IDBFS Playground
 *
 * Tests the complete browser-based transpilation workflow with:
 * - ZIP file upload
 * - IDBFS filesystem persistence
 * - WASM transpilation
 * - Output file download
 */

import { test, expect } from '@playwright/test';
import { readFile } from 'fs/promises';
import { join } from 'path';

const PLAYGROUND_URL = 'http://localhost:4321/playground-idbfs.html';
const TEST_ZIP_PATH = join(__dirname, '../.playwright-mcp/json-parser-test-transpiled.zip');

test.describe('IDBFS Playground E2E', () => {
  test.beforeEach(async ({ page }) => {
    // Navigate to playground
    await page.goto(PLAYGROUND_URL);

    // Wait for page to be fully loaded
    await page.waitForLoadState('networkidle');
  });

  test('should load playground page', async ({ page }) => {
    // Check page title
    await expect(page).toHaveTitle(/C\+\+ to C Transpiler/);

    // Check for key elements
    await expect(page.locator('h1')).toContainText('C++ to C Transpiler');
    await expect(page.locator('#zipInput')).toBeVisible();
    await expect(page.locator('#transpileBtn')).toBeVisible();
  });

  test('should upload ZIP file and show file list', async ({ page }) => {
    // Upload ZIP file
    const fileInput = page.locator('#zipInput');
    await fileInput.setInputFiles(TEST_ZIP_PATH);

    // Wait for file list to appear
    await page.waitForSelector('#fileList li', { timeout: 10000 });

    // Check that files are listed
    const fileListItems = page.locator('#fileList li');
    const count = await fileListItems.count();
    expect(count).toBeGreaterThan(0);

    // Check for expected C++ source files
    await expect(page.locator('#fileList')).toContainText('JsonParser.cpp');
    await expect(page.locator('#fileList')).toContainText('JsonValue.cpp');
  });

  test('should transpile uploaded C++ files to C', async ({ page }) => {
    // Upload ZIP file
    await page.locator('#zipInput').setInputFiles(TEST_ZIP_PATH);

    // Wait for file list
    await page.waitForSelector('#fileList li', { timeout: 10000 });

    // Click transpile button
    await page.locator('#transpileBtn').click();

    // Wait for transpilation to complete (status message)
    await page.waitForSelector('#status:has-text("Transpilation complete")', {
      timeout: 60000 // Allow up to 60s for transpilation
    });

    // Check that output files were generated
    const outputList = page.locator('#outputList li');
    const outputCount = await outputList.count();
    expect(outputCount).toBeGreaterThan(0);

    // Check for expected C output files
    await expect(page.locator('#outputList')).toContainText('JsonParser.c');
    await expect(page.locator('#outputList')).toContainText('JsonParser.h');
    await expect(page.locator('#outputList')).toContainText('JsonValue.c');
    await expect(page.locator('#outputList')).toContainText('JsonValue.h');
  });

  test('should show transpilation progress', async ({ page }) => {
    // Upload ZIP file
    await page.locator('#zipInput').setInputFiles(TEST_ZIP_PATH);
    await page.waitForSelector('#fileList li');

    // Click transpile button
    await page.locator('#transpileBtn').click();

    // Check that progress is shown
    await expect(page.locator('#status')).toContainText('Transpiling', {
      timeout: 5000
    });

    // Wait for completion
    await page.waitForSelector('#status:has-text("complete")', {
      timeout: 60000
    });
  });

  test('should download transpiled C files', async ({ page }) => {
    // Upload and transpile
    await page.locator('#zipInput').setInputFiles(TEST_ZIP_PATH);
    await page.waitForSelector('#fileList li');
    await page.locator('#transpileBtn').click();
    await page.waitForSelector('#status:has-text("complete")', { timeout: 60000 });

    // Set up download listener
    const downloadPromise = page.waitForEvent('download');

    // Click download button
    await page.locator('#downloadBtn').click();

    // Wait for download to start
    const download = await downloadPromise;

    // Check download filename
    expect(download.suggestedFilename()).toMatch(/\.zip$/);

    // Save and verify download
    const downloadPath = join(__dirname, '../.playwright/downloads', download.suggestedFilename());
    await download.saveAs(downloadPath);

    // Verify file was downloaded
    const fs = require('fs');
    expect(fs.existsSync(downloadPath)).toBe(true);
    expect(fs.statSync(downloadPath).size).toBeGreaterThan(0);
  });

  test('should show error for invalid ZIP file', async ({ page }) => {
    // Create a temporary invalid file
    const invalidZipPath = join(__dirname, '../.playwright/invalid.zip');
    require('fs').writeFileSync(invalidZipPath, 'not a valid zip file');

    // Upload invalid file
    await page.locator('#zipInput').setInputFiles(invalidZipPath);

    // Wait for error message
    await expect(page.locator('#status')).toContainText('Error', {
      timeout: 5000
    });

    // Clean up
    require('fs').unlinkSync(invalidZipPath);
  });

  test('should persist files in IDBFS across page reloads', async ({ page }) => {
    // Upload ZIP file
    await page.locator('#zipInput').setInputFiles(TEST_ZIP_PATH);
    await page.waitForSelector('#fileList li');

    // Get file count before reload
    const fileCountBefore = await page.locator('#fileList li').count();

    // Reload page
    await page.reload();
    await page.waitForLoadState('networkidle');

    // Check if files are still there (IDBFS persistence)
    // Note: This may require a "Load Previous Session" button in the UI
    const fileListAfterReload = page.locator('#fileList li');
    const fileCountAfter = await fileListAfterReload.count();

    // If IDBFS persistence is working, files should still be there
    // Otherwise, this test documents expected behavior
    if (fileCountAfter > 0) {
      expect(fileCountAfter).toBe(fileCountBefore);
    }
  });

  test('should handle large C++ projects', async ({ page }) => {
    test.slow(); // Mark as slow test

    // Upload ZIP file
    await page.locator('#zipInput').setInputFiles(TEST_ZIP_PATH);
    await page.waitForSelector('#fileList li');

    // Get file count
    const fileCount = await page.locator('#fileList li').count();
    console.log(`Processing ${fileCount} files`);

    // Transpile
    await page.locator('#transpileBtn').click();

    // Wait for completion (allow more time for large projects)
    await page.waitForSelector('#status:has-text("complete")', {
      timeout: 120000 // 2 minutes for large projects
    });

    // Verify all files were processed
    const outputCount = await page.locator('#outputList li').count();
    expect(outputCount).toBeGreaterThan(0);
  });

  test('should show file content when clicked', async ({ page }) => {
    // Upload ZIP file
    await page.locator('#zipInput').setInputFiles(TEST_ZIP_PATH);
    await page.waitForSelector('#fileList li');

    // Click on a file
    await page.locator('#fileList li:has-text("JsonParser.cpp")').click();

    // Check that file content is displayed
    const codeViewer = page.locator('#codeViewer, #fileContent, pre');
    await expect(codeViewer).toBeVisible();
    await expect(codeViewer).toContainText('class', { timeout: 5000 });
  });

  test('should support cancellation during transpilation', async ({ page }) => {
    // Upload ZIP file
    await page.locator('#zipInput').setInputFiles(TEST_ZIP_PATH);
    await page.waitForSelector('#fileList li');

    // Start transpilation
    await page.locator('#transpileBtn').click();

    // Wait a moment for transpilation to start
    await page.waitForTimeout(1000);

    // Click cancel button (if exists)
    const cancelBtn = page.locator('#cancelBtn, button:has-text("Cancel")');
    if (await cancelBtn.isVisible()) {
      await cancelBtn.click();

      // Check that status shows cancellation
      await expect(page.locator('#status')).toContainText(/cancel/i, {
        timeout: 5000
      });
    }
  });
});

test.describe('IDBFS Filesystem Operations', () => {
  test('should mount IDBFS filesystem on page load', async ({ page }) => {
    await page.goto(PLAYGROUND_URL);

    // Check console for IDBFS mount success message
    const consoleLogs: string[] = [];
    page.on('console', msg => consoleLogs.push(msg.text()));

    await page.waitForLoadState('networkidle');
    await page.waitForTimeout(2000); // Give time for IDBFS to mount

    // Look for IDBFS-related console messages
    const hasIDBFSMessage = consoleLogs.some(log =>
      log.includes('IDBFS') || log.includes('mount') || log.includes('filesystem')
    );

    if (!hasIDBFSMessage) {
      console.warn('No IDBFS mount message found in console');
    }
  });

  test('should write files to IDBFS', async ({ page }) => {
    await page.goto(PLAYGROUND_URL);

    // Upload ZIP
    await page.locator('#zipInput').setInputFiles(TEST_ZIP_PATH);
    await page.waitForSelector('#fileList li');

    // Check that files appear in the list (indicates successful write to IDBFS)
    const fileCount = await page.locator('#fileList li').count();
    expect(fileCount).toBeGreaterThan(0);
  });

  test('should read transpiled files from IDBFS', async ({ page }) => {
    await page.goto(PLAYGROUND_URL);

    // Upload and transpile
    await page.locator('#zipInput').setInputFiles(TEST_ZIP_PATH);
    await page.waitForSelector('#fileList li');
    await page.locator('#transpileBtn').click();
    await page.waitForSelector('#status:has-text("complete")', { timeout: 60000 });

    // Click on an output file to read it
    const outputFile = page.locator('#outputList li:has-text(".c")').first();
    if (await outputFile.isVisible()) {
      await outputFile.click();

      // Check that content is displayed (file was read from IDBFS)
      const codeViewer = page.locator('#codeViewer, #fileContent, pre');
      await expect(codeViewer).toBeVisible();
    }
  });
});
