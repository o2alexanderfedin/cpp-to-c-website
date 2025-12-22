import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import JSZip from 'jszip';
import { downloadAsZip, isDownloadSupported } from './fileDownload';

// Mock DOM APIs
const mockCreateObjectURL = vi.fn();
const mockRevokeObjectURL = vi.fn();
const mockClick = vi.fn();
const mockAppendChild = vi.fn();
const mockRemoveChild = vi.fn();

describe('fileDownload', () => {
    beforeEach(() => {
        // Setup URL mock
        global.URL.createObjectURL = mockCreateObjectURL;
        global.URL.revokeObjectURL = mockRevokeObjectURL;
        mockCreateObjectURL.mockReturnValue('blob:mock-url');

        // Setup document mock
        const mockAnchor = {
            href: '',
            download: '',
            click: mockClick,
        } as any;

        vi.spyOn(document, 'createElement').mockReturnValue(mockAnchor);
        vi.spyOn(document.body, 'appendChild').mockImplementation(mockAppendChild);
        vi.spyOn(document.body, 'removeChild').mockImplementation(mockRemoveChild);
    });

    afterEach(() => {
        vi.clearAllMocks();
    });

    describe('downloadAsZip', () => {
        it('should create and download a ZIP file with single file', async () => {
            const files = new Map([['test.c', '#include <stdio.h>']]);

            await downloadAsZip(files, 'test-project');

            expect(mockCreateObjectURL).toHaveBeenCalledWith(expect.any(Blob));
            expect(mockClick).toHaveBeenCalledOnce();
            expect(mockRevokeObjectURL).toHaveBeenCalledWith('blob:mock-url');
            expect(mockAppendChild).toHaveBeenCalledOnce();
            expect(mockRemoveChild).toHaveBeenCalledOnce();
        });

        it('should create and download a ZIP file with multiple files', async () => {
            const files = new Map([
                ['main.c', '#include <stdio.h>\nint main() { return 0; }'],
                ['utils/helper.c', '#include "helper.h"\nvoid help() {}'],
                ['include/helper.h', '#ifndef HELPER_H\n#define HELPER_H\n#endif'],
            ]);

            await downloadAsZip(files, 'multi-file-project');

            expect(mockCreateObjectURL).toHaveBeenCalledWith(expect.any(Blob));
            expect(mockClick).toHaveBeenCalledOnce();
            expect(mockRevokeObjectURL).toHaveBeenCalledWith('blob:mock-url');
        });

        it('should preserve directory structure in ZIP', async () => {
            const files = new Map([
                ['src/main.c', 'main content'],
                ['src/utils/helper.c', 'helper content'],
                ['include/header.h', 'header content'],
            ]);

            await downloadAsZip(files, 'structured-project');

            // Verify the blob was created (JSZip handles structure internally)
            expect(mockCreateObjectURL).toHaveBeenCalledWith(expect.any(Blob));
        });

        it('should set correct download filename', async () => {
            const files = new Map([['test.c', 'content']]);
            const mockAnchor = document.createElement('a');

            await downloadAsZip(files, 'my-project');

            expect(mockAnchor.download).toBe('my-project.zip');
        });

        it('should throw error when no files provided', async () => {
            const emptyFiles = new Map<string, string>();

            await expect(downloadAsZip(emptyFiles, 'empty')).rejects.toThrow(
                'Cannot create ZIP: no files provided'
            );
        });

        it('should handle files with various extensions', async () => {
            const files = new Map([
                ['main.c', 'C code'],
                ['header.h', 'Header'],
                ['readme.txt', 'Documentation'],
                ['Makefile', 'Build file'],
            ]);

            await downloadAsZip(files, 'mixed-files');

            expect(mockCreateObjectURL).toHaveBeenCalledWith(expect.any(Blob));
            expect(mockClick).toHaveBeenCalledOnce();
        });

        it('should handle special characters in filenames', async () => {
            const files = new Map([
                ['file with spaces.c', 'content'],
                ['file-with-dashes.c', 'content'],
                ['file_with_underscores.c', 'content'],
            ]);

            await downloadAsZip(files, 'special-chars');

            expect(mockCreateObjectURL).toHaveBeenCalledWith(expect.any(Blob));
        });

        it('should clean up resources after download', async () => {
            const files = new Map([['test.c', 'content']]);

            await downloadAsZip(files, 'cleanup-test');

            expect(mockAppendChild).toHaveBeenCalledOnce();
            expect(mockRemoveChild).toHaveBeenCalledOnce();
            expect(mockRevokeObjectURL).toHaveBeenCalledWith('blob:mock-url');
        });

        it('should create valid ZIP structure', async () => {
            const files = new Map([
                ['src/main.c', 'main content'],
                ['include/header.h', 'header content'],
            ]);

            // Intercept the blob creation to verify ZIP structure
            let capturedBlob: Blob | null = null;
            mockCreateObjectURL.mockImplementation((blob: Blob) => {
                capturedBlob = blob;
                return 'blob:mock-url';
            });

            await downloadAsZip(files, 'structure-test');

            expect(capturedBlob).not.toBeNull();
            expect(capturedBlob).toBeInstanceOf(Blob);

            // Verify we can read the ZIP back
            if (capturedBlob) {
                const zip = await JSZip.loadAsync(capturedBlob);
                const zipFiles = Object.keys(zip.files);

                expect(zipFiles).toContain('src/main.c');
                expect(zipFiles).toContain('include/header.h');

                const mainContent = await zip.file('src/main.c')?.async('string');
                expect(mainContent).toBe('main content');

                const headerContent = await zip.file('include/header.h')?.async('string');
                expect(headerContent).toBe('header content');
            }
        });
    });

    describe('isDownloadSupported', () => {
        it('should return true when all APIs are supported', () => {
            expect(isDownloadSupported()).toBe(true);
        });

        it('should return false when URL is not defined', () => {
            const originalURL = global.URL;
            // @ts-expect-error - Testing undefined case
            global.URL = undefined;

            expect(isDownloadSupported()).toBe(false);

            global.URL = originalURL;
        });

        it('should return false when createObjectURL is not available', () => {
            const originalCreateObjectURL = URL.createObjectURL;
            // @ts-expect-error - Testing undefined case
            URL.createObjectURL = undefined;

            expect(isDownloadSupported()).toBe(false);

            URL.createObjectURL = originalCreateObjectURL;
        });

        it('should return false when document is not defined', () => {
            const originalDocument = global.document;
            // @ts-expect-error - Testing undefined case
            global.document = undefined;

            expect(isDownloadSupported()).toBe(false);

            global.document = originalDocument;
        });

        it('should return false when Blob is not defined', () => {
            const originalBlob = global.Blob;
            // @ts-expect-error - Testing undefined case
            global.Blob = undefined;

            expect(isDownloadSupported()).toBe(false);

            global.Blob = originalBlob;
        });
    });
});
