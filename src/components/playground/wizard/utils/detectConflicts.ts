import type { FileInfo } from '../types';

/**
 * Information about a detected file conflict
 */
export interface FileConflict {
  sourcePath: string;
  targetFileName: string;
  exists: boolean;
}

/**
 * Result of conflict detection
 */
export interface ConflictDetectionResult {
  conflicts: FileConflict[];
  totalFiles: number;
  conflictCount: number;
}

/**
 * Convert source file extension to target extension
 * @param fileName - Source file name (e.g., "main.cpp")
 * @returns Target file name (e.g., "main.c")
 */
export function convertToTargetFileName(fileName: string): string {
  // Map C++ extensions to .c
  const cppExtensions = ['.cpp', '.cc', '.cxx', '.C'];

  for (const ext of cppExtensions) {
    if (fileName.endsWith(ext)) {
      return fileName.slice(0, -ext.length) + '.c';
    }
  }

  // Header files: .hpp, .hxx -> .h
  if (fileName.endsWith('.hpp') || fileName.endsWith('.hxx')) {
    return fileName.slice(0, fileName.lastIndexOf('.')) + '.h';
  }

  // Already .h, .c or unknown extension, keep as-is
  return fileName;
}

/**
 * Detect conflicts between source files and target directory
 * @param sourceFiles - Array of source FileInfo objects
 * @param targetDir - Target directory handle
 * @returns Conflict detection result
 */
export async function detectConflicts(
  sourceFiles: FileInfo[],
  targetDir: FileSystemDirectoryHandle
): Promise<ConflictDetectionResult> {
  const conflicts: FileConflict[] = [];

  // Get list of existing files in target directory
  const existingFiles = new Set<string>();
  try {
    for await (const entry of targetDir.values()) {
      if (entry.kind === 'file') {
        existingFiles.add(entry.name);
      }
    }
  } catch (error) {
    console.error('Error reading target directory:', error);
    throw new Error('Failed to read target directory contents');
  }

  // Check each source file for conflicts
  for (const sourceFile of sourceFiles) {
    const targetFileName = convertToTargetFileName(sourceFile.name);
    const exists = existingFiles.has(targetFileName);

    conflicts.push({
      sourcePath: sourceFile.path,
      targetFileName,
      exists
    });
  }

  const conflictCount = conflicts.filter(c => c.exists).length;

  return {
    conflicts,
    totalFiles: sourceFiles.length,
    conflictCount
  };
}

/**
 * Get only the conflicting files (files that exist in target)
 * @param result - Conflict detection result
 * @returns Array of conflicting files
 */
export function getConflictingFiles(result: ConflictDetectionResult): FileConflict[] {
  return result.conflicts.filter(c => c.exists);
}
