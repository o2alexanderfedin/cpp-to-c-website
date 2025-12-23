/**
 * TranspileService - Core Transpilation Orchestration
 *
 * Orchestrates the transpilation of entire C++ projects to C.
 * Handles file traversal, parallel processing, progress reporting,
 * error handling, and cancellation support.
 *
 * Following SOLID principles:
 * - Single Responsibility: Only orchestrates transpilation workflow
 * - Open/Closed: New file systems or transpilers can be added via interfaces
 * - Liskov Substitution: All dependencies are interface-based
 * - Interface Segregation: Depends only on minimal interfaces
 * - Dependency Inversion: Depends on abstractions, not implementations
 */

import type { IFileSystem } from '../../core/interfaces/IFileSystem';
import type { ITranspiler } from '../../core/interfaces/ITranspiler';
import type { IProgressReporter } from '../../core/interfaces/IProgressReporter';
import type { TranspileProjectOptions, TranspileProjectResult, FileTask } from './types';

/**
 * C++ file extensions to process
 */
const CPP_EXTENSIONS = ['.cpp', '.cc', '.cxx', '.h', '.hpp', '.hxx'];

/**
 * Default concurrency for parallel file processing
 */
const DEFAULT_CONCURRENCY = 10;

/**
 * Service that orchestrates project transpilation
 */
export class TranspileService {
  /**
   * Constructor with dependency injection
   *
   * @param fileSystem - File system abstraction for I/O operations
   * @param transpiler - Transpiler engine for C++ to C conversion
   * @param progressReporter - Progress reporter for UI updates
   */
  constructor(
    private readonly fileSystem: IFileSystem,
    private readonly transpiler: ITranspiler,
    private readonly progressReporter: IProgressReporter
  ) {}

  /**
   * Transpile an entire project from source to target directory
   *
   * @param sourcePath - Path to source directory containing C++ files
   * @param targetPath - Path to target directory for C output
   * @param options - Transpilation options (cancellation, concurrency)
   * @returns Result with success status, file counts, and errors
   */
  async transpileProject(
    sourcePath: string,
    targetPath: string,
    options: TranspileProjectOptions = {}
  ): Promise<TranspileProjectResult> {
    const startTime = performance.now(); // Use performance.now() for better precision
    const errors: string[] = [];

    try {
      // Gather all C++ files recursively
      const fileTasks = await this.gatherFileTasks(sourcePath, targetPath);

      // Start progress reporting
      this.progressReporter.start(fileTasks.length);

      // Process files with concurrency control
      const concurrency = options.concurrency ?? DEFAULT_CONCURRENCY;
      const results = await this.processFilesInParallel(
        fileTasks,
        concurrency,
        options.signal,
        errors
      );

      // Complete progress reporting
      this.progressReporter.complete();

      // Calculate results
      const successCount = results.filter((r) => r).length;
      const errorCount = results.filter((r) => !r).length;

      return {
        success: true,
        filesProcessed: fileTasks.length,
        successCount,
        errorCount,
        errors,
        elapsedMs: Math.ceil(performance.now() - startTime), // Always at least 1ms
      };
    } catch (error) {
      // Handle cancellation or catastrophic errors
      if (
        error instanceof Error &&
        (error.message.includes('abort') || error.message.includes('cancel'))
      ) {
        this.progressReporter.error('Operation cancelled');
        throw new Error('Operation cancelled');
      }

      this.progressReporter.error('Transpilation failed');
      throw error;
    }
  }

  /**
   * Gather all C++ files from source directory recursively
   *
   * @param sourcePath - Source directory path
   * @param targetPath - Target directory path
   * @returns Array of file tasks to process
   */
  private async gatherFileTasks(
    sourcePath: string,
    targetPath: string
  ): Promise<FileTask[]> {
    const tasks: FileTask[] = [];

    const traverse = async (
      currentSourcePath: string,
      currentTargetPath: string,
      relativePath: string
    ) => {
      const files = await this.fileSystem.readDir(currentSourcePath);

      for (const fileName of files) {
        const fullSourcePath = `${currentSourcePath}/${fileName}`;
        const fullTargetPath = `${currentTargetPath}/${fileName}`;
        const relativeFilePath = relativePath ? `${relativePath}/${fileName}` : fileName;

        // Check if this is a C++ file (by extension)
        if (this.isCppFile(fileName)) {
          // Convert extension to .c or keep .h/.hpp
          const targetFileName = this.convertToTargetFileName(fileName);
          const adjustedTargetPath = currentTargetPath === targetPath
            ? `${targetPath}/${targetFileName}`
            : `${currentTargetPath}/${targetFileName}`;

          tasks.push({
            sourcePath: relativeFilePath,
            targetPath: relativeFilePath.replace(fileName, targetFileName),
            absoluteSourcePath: fullSourcePath,
            absoluteTargetPath: adjustedTargetPath,
          });
        }

        // Recursively traverse subdirectories by checking if we can read it as a directory
        try {
          const subFiles = await this.fileSystem.readDir(fullSourcePath);
          if (subFiles) {
            // It's a directory, traverse it
            await traverse(fullSourcePath, fullTargetPath, relativeFilePath);
          }
        } catch {
          // Not a directory, skip
        }
      }
    };

    await traverse(sourcePath, targetPath, '');
    return tasks;
  }

  /**
   * Process files in parallel with concurrency control
   *
   * @param tasks - File tasks to process
   * @param concurrency - Maximum concurrent operations
   * @param signal - Abort signal for cancellation
   * @param errors - Array to collect errors
   * @returns Array of success/failure booleans
   */
  private async processFilesInParallel(
    tasks: FileTask[],
    concurrency: number,
    signal: AbortSignal | undefined,
    errors: string[]
  ): Promise<boolean[]> {
    const results: boolean[] = [];
    let currentIndex = 0;

    const processNextTask = async (): Promise<void> => {
      while (currentIndex < tasks.length) {
        const taskIndex = currentIndex++;
        const task = tasks[taskIndex];

        try {
          // Check for cancellation before starting each task
          if (signal?.aborted) {
            throw new Error('Operation cancelled');
          }

          // Read source file
          const sourceCode = await this.fileSystem.readFile(task.absoluteSourcePath);

          // Check for cancellation again before transpiling
          if (signal?.aborted) {
            throw new Error('Operation cancelled');
          }

          // Transpile
          const result = await this.transpiler.transpile(sourceCode, {
            sourcePath: task.absoluteSourcePath,
          });

          // Check for cancellation before writing
          if (signal?.aborted) {
            throw new Error('Operation cancelled');
          }

          if (result.success && result.cCode) {
            // Write target file
            await this.fileSystem.writeFile(task.absoluteTargetPath, result.cCode);
            results[taskIndex] = true;
          } else {
            // Transpilation failed
            const errorMsg = `${task.absoluteSourcePath}: ${result.error || 'Unknown error'}`;
            errors.push(errorMsg);
            results[taskIndex] = false;
          }
        } catch (error) {
          // Check if it's a cancellation error
          if (error instanceof Error && error.message.includes('cancel')) {
            throw error; // Re-throw cancellation errors
          }

          // File I/O or other error
          const errorMsg = `${task.absoluteSourcePath}: ${
            error instanceof Error ? error.message : 'Unknown error'
          }`;
          errors.push(errorMsg);
          results[taskIndex] = false;
        }

        // Update progress
        this.progressReporter.update(taskIndex + 1, `Processing ${task.sourcePath}`);
      }
    };

    // Create concurrency workers
    const workers: Promise<void>[] = [];
    for (let i = 0; i < Math.min(concurrency, tasks.length); i++) {
      workers.push(processNextTask());
    }

    // Wait for all workers to complete
    await Promise.all(workers);

    return results;
  }

  /**
   * Check if a file is a C++ source/header file
   *
   * @param fileName - File name to check
   * @returns True if file should be transpiled
   */
  private isCppFile(fileName: string): boolean {
    return CPP_EXTENSIONS.some((ext) => fileName.endsWith(ext));
  }

  /**
   * Convert C++ file name to C file name
   *
   * @param fileName - C++ file name
   * @returns C file name
   */
  private convertToTargetFileName(fileName: string): string {
    // Convert .cpp/.cc/.cxx to .c
    if (fileName.endsWith('.cpp')) {
      return fileName.replace(/\.cpp$/, '.c');
    }
    if (fileName.endsWith('.cc')) {
      return fileName.replace(/\.cc$/, '.c');
    }
    if (fileName.endsWith('.cxx')) {
      return fileName.replace(/\.cxx$/, '.c');
    }

    // Keep .h and .hpp as-is
    return fileName;
  }
}
