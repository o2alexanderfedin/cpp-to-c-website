/**
 * Types specific to the Transpile feature
 */

/**
 * Options for transpileProject operation
 */
export interface TranspileProjectOptions {
  /**
   * Abort signal for cancellation support
   */
  signal?: AbortSignal;

  /**
   * Number of files to process in parallel
   * @default 10
   */
  concurrency?: number;
}

/**
 * Result of transpiling a project
 */
export interface TranspileProjectResult {
  /**
   * Whether the overall operation succeeded
   * (true even if individual files failed, as long as operation completed)
   */
  success: boolean;

  /**
   * Total number of files processed (attempted)
   */
  filesProcessed: number;

  /**
   * Number of files successfully transpiled
   */
  successCount: number;

  /**
   * Number of files that failed
   */
  errorCount: number;

  /**
   * Array of error messages (one per failed file)
   */
  errors: string[];

  /**
   * Time elapsed in milliseconds
   */
  elapsedMs: number;
}

/**
 * Internal file processing task
 */
export interface FileTask {
  /**
   * Source file path (relative to source root)
   */
  sourcePath: string;

  /**
   * Target file path (relative to target root)
   */
  targetPath: string;

  /**
   * Absolute source file path
   */
  absoluteSourcePath: string;

  /**
   * Absolute target file path
   */
  absoluteTargetPath: string;
}
