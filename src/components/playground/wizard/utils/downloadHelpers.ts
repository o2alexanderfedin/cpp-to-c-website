import JSZip from 'jszip';
import type { TranspileResult } from '../types';

/**
 * Download a single file as text
 * @param filename - Name for downloaded file
 * @param content - File content
 */
export function downloadFile(filename: string, content: string): void {
  const blob = new Blob([content], { type: 'text/plain;charset=utf-8' });
  const url = URL.createObjectURL(blob);
  const link = document.createElement('a');
  link.href = url;
  link.download = filename;
  document.body.appendChild(link);
  link.click();
  document.body.removeChild(link);
  URL.revokeObjectURL(url);
}

/**
 * Create ZIP archive of all transpiled files
 * @param results - Map of file paths to transpilation results
 * @returns ZIP blob
 */
export async function createZipArchive(
  results: Map<string, TranspileResult>
): Promise<Blob> {
  const zip = new JSZip();

  // Add successful transpilations to ZIP
  for (const [path, result] of results.entries()) {
    if (result.success) {
      // Add .h file if present
      if (result.hCode) {
        const hPath = path
          .replace(/\.(cpp|cc|cxx)$/i, '.h')
          .replace(/\.(hpp|hxx)$/i, '.h');
        zip.file(hPath, result.hCode);
      }

      // Add .c file if present
      if (result.cCode) {
        const cPath = path
          .replace(/\.(cpp|cc|cxx)$/i, '.c')
          .replace(/\.(hpp|hxx)$/i, '.h');
        zip.file(cPath, result.cCode);
      }
    }
  }

  return zip.generateAsync({ type: 'blob' });
}

/**
 * Download ZIP archive
 * @param blob - ZIP blob
 * @param filename - Archive filename
 */
export function downloadZip(blob: Blob, filename: string = 'transpiled.zip'): void {
  const url = URL.createObjectURL(blob);
  const link = document.createElement('a');
  link.href = url;
  link.download = filename;
  document.body.appendChild(link);
  link.click();
  document.body.removeChild(link);
  URL.revokeObjectURL(url);
}

/**
 * Calculate total bytes in transpilation results
 * @param results - Map of transpilation results
 * @returns Total bytes (C code and header files)
 */
export function calculateTotalBytes(results: Map<string, TranspileResult>): number {
  let total = 0;
  for (const result of results.values()) {
    if (result.success) {
      if (result.cCode) {
        total += new Blob([result.cCode]).size;
      }
      if (result.hCode) {
        total += new Blob([result.hCode]).size;
      }
    }
  }
  return total;
}

/**
 * Format bytes to human-readable string
 * @param bytes - Number of bytes
 * @returns Formatted string (e.g., "1.5 KB")
 */
export function formatBytes(bytes: number): string {
  if (bytes === 0) return '0 Bytes';

  const k = 1024;
  const sizes = ['Bytes', 'KB', 'MB', 'GB'];
  const i = Math.floor(Math.log(bytes) / Math.log(k));

  return `${parseFloat((bytes / Math.pow(k, i)).toFixed(2))} ${sizes[i]}`;
}
