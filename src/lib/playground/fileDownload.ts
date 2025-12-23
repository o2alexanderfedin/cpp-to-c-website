import JSZip from 'jszip';

/**
 * Downloads a collection of files as a ZIP archive.
 *
 * @param files - Map of file paths to file contents
 * @param zipName - Name of the ZIP file (without .zip extension)
 * @returns Promise that resolves when download is triggered
 *
 * @example
 * ```typescript
 * const files = new Map([
 *   ['main.c', '#include <stdio.h>\nint main() { return 0; }'],
 *   ['utils/helper.c', '#include "helper.h"\nvoid help() {}']
 * ]);
 * await downloadAsZip(files, 'transpiled-project');
 * ```
 */
export async function downloadAsZip(
    files: Map<string, string>,
    zipName: string
): Promise<void> {
    if (files.size === 0) {
        throw new Error('Cannot create ZIP: no files provided');
    }

    const zip = new JSZip();

    // Add all files to ZIP, preserving directory structure
    for (const [path, content] of files.entries()) {
        zip.file(path, content);
    }

    // Generate ZIP blob
    const blob = await zip.generateAsync({
        type: 'blob',
        compression: 'DEFLATE',
        compressionOptions: {
            level: 6 // Balanced compression
        }
    });

    // Trigger browser download
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = `${zipName}.zip`;

    // For better browser compatibility
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);

    // Clean up the object URL
    URL.revokeObjectURL(url);
}

/**
 * Validates if the browser supports the required APIs for file download.
 *
 * @returns true if the browser supports file downloads, false otherwise
 */
export function isDownloadSupported(): boolean {
    return (
        typeof URL !== 'undefined' &&
        typeof URL.createObjectURL === 'function' &&
        typeof document !== 'undefined' &&
        typeof Blob !== 'undefined'
    );
}
