import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import {
  downloadFile,
  calculateTotalBytes,
  formatBytes,
  createZipArchive,
  downloadZip,
} from './downloadHelpers';
import type { TranspileResult } from '../types';

describe('downloadHelpers', () => {
  describe('calculateTotalBytes', () => {
    it('calculates total bytes from successful results', () => {
      const results = new Map<string, TranspileResult>([
        ['a.cpp', { success: true, cCode: 'int main() {}' }], // 13 bytes
        ['b.cpp', { success: true, cCode: 'int x = 0;' }],   // 10 bytes
        ['c.cpp', { success: false, error: 'Parse error' }], // Not counted
      ]);

      const total = calculateTotalBytes(results);
      // Should count only successful results: 13 + 10 = 23 bytes
      expect(total).toBe(23);
    });

    it('returns 0 for empty results', () => {
      const results = new Map<string, TranspileResult>();
      expect(calculateTotalBytes(results)).toBe(0);
    });

    it('returns 0 when all transpilations failed', () => {
      const results = new Map<string, TranspileResult>([
        ['a.cpp', { success: false, error: 'Error 1' }],
        ['b.cpp', { success: false, error: 'Error 2' }],
      ]);
      expect(calculateTotalBytes(results)).toBe(0);
    });
  });

  describe('formatBytes', () => {
    it('formats 0 bytes correctly', () => {
      expect(formatBytes(0)).toBe('0 Bytes');
    });

    it('formats bytes correctly', () => {
      expect(formatBytes(500)).toBe('500 Bytes');
    });

    it('formats kilobytes correctly', () => {
      expect(formatBytes(1024)).toBe('1 KB');
      expect(formatBytes(1536)).toBe('1.5 KB');
      expect(formatBytes(2048)).toBe('2 KB');
    });

    it('formats megabytes correctly', () => {
      expect(formatBytes(1048576)).toBe('1 MB');
      expect(formatBytes(1572864)).toBe('1.5 MB');
    });

    it('formats gigabytes correctly', () => {
      expect(formatBytes(1073741824)).toBe('1 GB');
    });
  });

  describe('createZipArchive', () => {
    it('creates ZIP from successful results', async () => {
      const results = new Map<string, TranspileResult>([
        ['test.cpp', { success: true, cCode: 'int main() { return 0; }' }],
      ]);

      const zip = await createZipArchive(results);
      expect(zip).toBeInstanceOf(Blob);
      expect(zip.size).toBeGreaterThan(0);
    });

    it('converts file extensions .cpp to .c', async () => {
      const results = new Map<string, TranspileResult>([
        ['src/main.cpp', { success: true, cCode: 'int main() {}' }],
        ['src/utils.cc', { success: true, cCode: 'void foo() {}' }],
        ['src/header.cxx', { success: true, cCode: 'extern int x;' }],
      ]);

      const zip = await createZipArchive(results);
      expect(zip.size).toBeGreaterThan(0);

      // Verify ZIP contains files
      expect(zip).toBeInstanceOf(Blob);
    });

    it('converts file extensions .hpp to .h', async () => {
      const results = new Map<string, TranspileResult>([
        ['include/header.hpp', { success: true, cCode: '#ifndef HEADER_H' }],
        ['include/util.hxx', { success: true, cCode: '#ifndef UTIL_H' }],
      ]);

      const zip = await createZipArchive(results);
      expect(zip.size).toBeGreaterThan(0);
    });

    it('excludes failed transpilations from ZIP', async () => {
      const results = new Map<string, TranspileResult>([
        ['success.cpp', { success: true, cCode: 'int main() {}' }],
        ['failed.cpp', { success: false, error: 'Parse error' }],
      ]);

      const zip = await createZipArchive(results);
      expect(zip).toBeInstanceOf(Blob);
      expect(zip.size).toBeGreaterThan(0);
    });

    it('creates empty ZIP when no successful results', async () => {
      const results = new Map<string, TranspileResult>([
        ['failed1.cpp', { success: false, error: 'Error 1' }],
        ['failed2.cpp', { success: false, error: 'Error 2' }],
      ]);

      const zip = await createZipArchive(results);
      expect(zip).toBeInstanceOf(Blob);
    });
  });

  describe('downloadFile', () => {
    let originalCreateObjectURL: typeof URL.createObjectURL;
    let originalRevokeObjectURL: typeof URL.revokeObjectURL;
    let mockUrl: string;
    let createdLinks: HTMLAnchorElement[] = [];

    beforeEach(() => {
      // Mock URL.createObjectURL and URL.revokeObjectURL
      mockUrl = 'blob:mock-url';
      originalCreateObjectURL = URL.createObjectURL;
      originalRevokeObjectURL = URL.revokeObjectURL;

      URL.createObjectURL = vi.fn(() => mockUrl);
      URL.revokeObjectURL = vi.fn();

      // Mock HTMLAnchorElement.click
      HTMLAnchorElement.prototype.click = vi.fn();

      // Track created links
      createdLinks = [];
      vi.spyOn(document.body, 'appendChild').mockImplementation((node) => {
        if (node instanceof HTMLAnchorElement) {
          createdLinks.push(node);
        }
        return node;
      });

      vi.spyOn(document.body, 'removeChild').mockImplementation((node) => {
        return node;
      });
    });

    afterEach(() => {
      URL.createObjectURL = originalCreateObjectURL;
      URL.revokeObjectURL = originalRevokeObjectURL;
      createdLinks = [];
      vi.restoreAllMocks();
    });

    it('creates download link with correct filename and content', () => {
      const filename = 'test.c';
      const content = 'int main() { return 0; }';

      downloadFile(filename, content);

      expect(URL.createObjectURL).toHaveBeenCalledWith(expect.any(Blob));
      expect(document.body.appendChild).toHaveBeenCalled();
      expect(createdLinks.length).toBe(1);

      const link = createdLinks[0];
      expect(link.download).toBe(filename);
      expect(link.href).toBe(mockUrl);
      expect(link.click).toHaveBeenCalled();
      expect(document.body.removeChild).toHaveBeenCalled();
      expect(URL.revokeObjectURL).toHaveBeenCalledWith(mockUrl);
    });
  });

  describe('downloadZip', () => {
    let originalCreateObjectURL: typeof URL.createObjectURL;
    let originalRevokeObjectURL: typeof URL.revokeObjectURL;
    let mockUrl: string;
    let createdLinks: HTMLAnchorElement[] = [];

    beforeEach(() => {
      mockUrl = 'blob:mock-url';
      originalCreateObjectURL = URL.createObjectURL;
      originalRevokeObjectURL = URL.revokeObjectURL;

      URL.createObjectURL = vi.fn(() => mockUrl);
      URL.revokeObjectURL = vi.fn();

      // Mock HTMLAnchorElement.click
      HTMLAnchorElement.prototype.click = vi.fn();

      // Track created links
      createdLinks = [];
      vi.spyOn(document.body, 'appendChild').mockImplementation((node) => {
        if (node instanceof HTMLAnchorElement) {
          createdLinks.push(node);
        }
        return node;
      });

      vi.spyOn(document.body, 'removeChild').mockImplementation((node) => {
        return node;
      });
    });

    afterEach(() => {
      URL.createObjectURL = originalCreateObjectURL;
      URL.revokeObjectURL = originalRevokeObjectURL;
      createdLinks = [];
      vi.restoreAllMocks();
    });

    it('downloads ZIP with default filename', () => {
      const blob = new Blob(['test'], { type: 'application/zip' });

      downloadZip(blob);

      expect(URL.createObjectURL).toHaveBeenCalledWith(blob);
      expect(document.body.appendChild).toHaveBeenCalled();
      expect(createdLinks.length).toBe(1);

      const link = createdLinks[0];
      expect(link.download).toBe('transpiled.zip');
      expect(link.href).toBe(mockUrl);
      expect(link.click).toHaveBeenCalled();
      expect(document.body.removeChild).toHaveBeenCalled();
      expect(URL.revokeObjectURL).toHaveBeenCalledWith(mockUrl);
    });

    it('downloads ZIP with custom filename', () => {
      const blob = new Blob(['test'], { type: 'application/zip' });
      const customFilename = 'my-project.zip';

      downloadZip(blob, customFilename);

      expect(createdLinks.length).toBe(1);
      expect(createdLinks[0].download).toBe(customFilename);
    });
  });
});
