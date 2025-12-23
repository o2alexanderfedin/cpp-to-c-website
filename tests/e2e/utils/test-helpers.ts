import { Page, expect } from '@playwright/test';

export async function waitForReactHydration(page: Page): Promise<void> {
  // Wait for React to hydrate by checking for interactive elements
  await page.waitForLoadState('domcontentloaded');
  // Additional wait for client-side JavaScript to be ready
  await page.waitForTimeout(500);
}

export async function verifyNoConsoleErrors(page: Page): Promise<void> {
  const errors: string[] = [];

  page.on('console', (msg) => {
    if (msg.type() === 'error') {
      errors.push(msg.text());
    }
  });

  page.on('pageerror', (error) => {
    errors.push(error.message);
  });

  // Check for errors after page load
  await page.waitForLoadState('networkidle');
  expect(errors).toEqual([]);
}

export async function mockFileSystemAccessAPI(page: Page, mockData: {
  directoryName: string;
  files: Map<string, string>;
}): Promise<void> {
  await page.addInitScript(({ directoryName, filesObj }) => {
    // Convert object back to Map
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
    directoryName: mockData.directoryName,
    filesObj: Object.fromEntries(mockData.files),
  });
}
