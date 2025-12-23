import type { FileInfo } from '../types';

/**
 * Load text content from a FileSystemFileHandle
 * @param handle - File handle to read
 * @returns File content as string
 */
export async function loadFileContent(handle: FileSystemFileHandle): Promise<string> {
  try {
    const file = await handle.getFile();
    const content = await file.text();
    return content;
  } catch (error) {
    console.error('Failed to load file content:', error);
    throw new Error(`Failed to read file: ${handle.name}`);
  }
}

/**
 * Find FileInfo by path in file list
 * @param files - List of FileInfo objects
 * @param path - File path to find
 * @returns FileInfo or undefined
 */
export function findFileByPath(files: FileInfo[], path: string): FileInfo | undefined {
  return files.find(f => f.path === path);
}
