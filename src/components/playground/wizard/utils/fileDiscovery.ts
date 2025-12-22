import type { FileInfo } from '../types';

/**
 * C++ file extensions to discover
 */
const CPP_EXTENSIONS = [
  '.cpp', '.cc', '.cxx',  // Source files
  '.h', '.hpp', '.hxx'    // Header files
];

/**
 * Check if a file has a C++ extension
 */
export const isCppFile = (filename: string): boolean => {
  return CPP_EXTENSIONS.some(ext => filename.toLowerCase().endsWith(ext));
};

/**
 * Recursively discover all C++ files in a directory
 *
 * @param dirHandle - FileSystemDirectoryHandle to search
 * @param basePath - Base path for building relative paths (default: '')
 * @returns Promise resolving to array of FileInfo objects
 */
export const discoverCppFiles = async (
  dirHandle: FileSystemDirectoryHandle,
  basePath: string = ''
): Promise<FileInfo[]> => {
  const files: FileInfo[] = [];

  try {
    // Iterate through directory entries
    for await (const [name, handle] of dirHandle.entries()) {
      const relativePath = basePath ? `${basePath}/${name}` : name;

      if (handle.kind === 'file') {
        // Check if it's a C++ file
        if (isCppFile(name)) {
          const fileHandle = handle as FileSystemFileHandle;
          const file = await fileHandle.getFile();

          files.push({
            path: relativePath,
            name: name,
            handle: fileHandle,
            size: file.size
          });
        }
      } else if (handle.kind === 'directory') {
        // Recursively search subdirectories
        const subDirHandle = handle as FileSystemDirectoryHandle;
        const subFiles = await discoverCppFiles(subDirHandle, relativePath);
        files.push(...subFiles);
      }
    }
  } catch (error) {
    console.error(`Error discovering files in ${basePath}:`, error);
    // Continue processing other files even if one fails
  }

  return files;
};

/**
 * Calculate total size of files in bytes
 */
export const calculateTotalSize = (files: FileInfo[]): number => {
  return files.reduce((total, file) => total + file.size, 0);
};

/**
 * Format bytes to human-readable size
 *
 * @param bytes - Size in bytes
 * @returns Formatted string (e.g., "1.5 MB")
 */
export const formatFileSize = (bytes: number): string => {
  if (bytes === 0) return '0 Bytes';

  const k = 1024;
  const sizes = ['Bytes', 'KB', 'MB', 'GB'];
  const i = Math.floor(Math.log(bytes) / Math.log(k));

  return `${parseFloat((bytes / Math.pow(k, i)).toFixed(2))} ${sizes[i]}`;
};
