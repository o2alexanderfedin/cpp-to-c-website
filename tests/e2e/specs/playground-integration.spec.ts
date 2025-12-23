import { test, expect } from '@playwright/test';
import { mockFileSystemAccessAPI } from '../utils/test-helpers';

test.describe('Playground Integration Tests - Complete Workflow', () => {
  test('should successfully transpile a small C++ project', async ({ page }) => {
    // Navigate to playground
    await page.goto('/playground');

    // Wait for React component to load
    await page.waitForSelector('h1:has-text("C++ to C Transpilation Playground")');

    // Create mock directory structure with test files
    const mockFiles = new Map<string, string>([
      ['main.cpp', `#include <iostream>
#include "helper.h"

int main() {
    std::cout << "Hello from C++ to C transpiler!" << std::endl;
    int result = add(5, 3);
    std::cout << "5 + 3 = " << result << std::endl;
    return 0;
}`],
      ['helper.h', `#ifndef HELPER_H
#define HELPER_H

int add(int a, int b);

#endif // HELPER_H`],
      ['helper.cpp', `#include "helper.h"

int add(int a, int b) {
    return a + b;
}`]
    ]);

    // Mock File System Access API with test files
    await mockFileSystemAccessAPI(page, { directoryName: 'test-cpp-project', files: mockFiles });

    // Click select directory button
    const selectButton = page.locator('button:has-text("Select Directory")');
    await expect(selectButton).toBeVisible();
    await selectButton.click();

    // Verify directory was selected
    await expect(page.locator('text=Selected: test-cpp-project')).toBeVisible({ timeout: 5000 });

    // Click transpile button
    const transpileButton = page.locator('button:has-text("Transpile Project")');
    await expect(transpileButton).toBeVisible();
    await transpileButton.click();

    // Wait for transpilation to complete
    await expect(page.locator('text=Transpilation completed')).toBeVisible({ timeout: 30000 });

    // Verify progress indicator shows 100%
    const progressText = await page.locator('[data-testid="progress-percentage"]').textContent();
    expect(progressText).toContain('100%');

    // Check that all 3 files were processed
    const fileCount = await page.locator('[data-testid="file-count"]').textContent();
    expect(fileCount).toContain('3');

    // Verify no "File not found" errors
    const errorList = await page.locator('[data-testid="error-list"]').textContent();
    expect(errorList).not.toContain('File not found');

    // Check for successful transpilation (API errors are expected since backend might not be running)
    // But file reading should work correctly
    const hasFileReadErrors = await page.locator('text=/File not found.*helper/').count();
    expect(hasFileReadErrors).toBe(0);
  });

  test('should handle directory with multiple file types', async ({ page }) => {
    await page.goto('/playground');
    await page.waitForSelector('h1:has-text("C++ to C Transpilation Playground")');

    const mockFiles = new Map<string, string>([
      ['main.cpp', '#include <iostream>\nint main() { return 0; }'],
      ['utils.cc', 'int util() { return 1; }'],
      ['app.cxx', 'int app() { return 2; }'],
      ['header.h', '#ifndef H\n#define H\n#endif'],
      ['header.hpp', '#ifndef HPP\n#define HPP\n#endif'],
      ['header.hxx', '#ifndef HXX\n#define HXX\n#endif'],
      ['README.md', '# Test Project'], // Should be ignored
      ['config.json', '{}'], // Should be ignored
    ]);

    await mockFileSystemAccessAPI(page, { directoryName: 'multi-type-project', files: mockFiles });

    await page.locator('button:has-text("Select Directory")').click();
    await expect(page.locator('text=Selected: multi-type-project')).toBeVisible();

    await page.locator('button:has-text("Transpile Project")').click();

    // Wait for completion
    await expect(page.locator('text=Transpilation completed')).toBeVisible({ timeout: 30000 });

    // Should process exactly 6 C++ files (not the .md or .json)
    const fileCount = await page.locator('[data-testid="file-count"]').textContent();
    expect(fileCount).toContain('6');
  });

  test('should read all files correctly without "File not found" errors', async ({ page }) => {
    await page.goto('/playground');
    await page.waitForSelector('h1:has-text("C++ to C Transpilation Playground")');

    // Create a larger test project
    const mockFiles = new Map<string, string>();
    for (let i = 1; i <= 10; i++) {
      mockFiles.set(`file${i}.cpp`, `// File ${i}\nint func${i}() { return ${i}; }`);
      mockFiles.set(`file${i}.h`, `#ifndef FILE${i}_H\n#define FILE${i}_H\nint func${i}();\n#endif`);
    }

    await mockFileSystemAccessAPI(page, { directoryName: 'large-project', files: mockFiles });

    await page.locator('button:has-text("Select Directory")').click();
    await expect(page.locator('text=Selected: large-project')).toBeVisible();

    await page.locator('button:has-text("Transpile Project")').click();

    await expect(page.locator('text=Transpilation completed')).toBeVisible({ timeout: 30000 });

    // Verify 20 files were found
    const fileCount = await page.locator('[data-testid="file-count"]').textContent();
    expect(fileCount).toContain('20');

    // Critical assertion: NO "File not found" errors
    const errors = await page.locator('[data-testid="error-list"]').allTextContents();
    const fileNotFoundErrors = errors.filter(e => e.includes('File not found'));

    expect(fileNotFoundErrors.length).toBe(0);
  });
});
