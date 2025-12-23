import { WasmTranspilerAdapter } from '../../../../adapters/WasmTranspilerAdapter';
import { WorkerPoolController } from '../../../../workers/WorkerPoolController';
import type { FileInfo, TranspileOptions, TranspileResult } from '../types';
import { convertToTargetFileName } from '../utils/detectConflicts';

/**
 * Transpilation progress event types
 */
export enum TranspilationEventType {
  STARTED = 'started',
  FILE_STARTED = 'file_started',
  FILE_COMPLETED = 'file_completed',
  FILE_ERROR = 'file_error',
  COMPLETED = 'completed',
  CANCELLED = 'cancelled',
  ERROR = 'error'
}

/**
 * Transpilation event data
 */
export interface TranspilationEvent {
  type: TranspilationEventType;
  filePath?: string;
  fileName?: string;
  result?: TranspileResult;
  progress?: {
    current: number;
    total: number;
    percentage: number;
  };
  metrics?: {
    elapsedMs: number;
    filesPerSecond: number;
    estimatedRemainingMs: number;
  };
  error?: string;
}

/**
 * Event listener type
 */
export type TranspilationEventListener = (event: TranspilationEvent) => void;

/**
 * Transpilation execution mode
 */
type ExecutionMode = 'parallel' | 'sequential';

/**
 * Transpilation controller
 * Orchestrates file transpilation with automatic parallelization
 *
 * Architecture:
 * - Parallel mode: Uses WorkerPoolController for multi-threaded execution
 * - Sequential mode: Fallback to WasmTranspilerAdapter on main thread
 * - Auto-detection: Tries parallel, falls back to sequential if workers unavailable
 */
export class TranspilationController {
  private workerPool: WorkerPoolController | null = null;
  private fallbackAdapter: WasmTranspilerAdapter | null = null;
  private listeners: Set<TranspilationEventListener> = new Set();
  private abortController: AbortController | null = null;
  private isPaused: boolean = false;
  private startTime: number = 0;
  private completedFiles: number = 0;
  private pauseStartTime: number = 0;
  private totalPausedTime: number = 0;
  private executionMode: ExecutionMode | null = null;
  private sourceFiles: FileInfo[] = [];

  constructor() {
    // Mode will be determined on first transpilation
  }

  /**
   * Add event listener
   */
  on(listener: TranspilationEventListener): void {
    this.listeners.add(listener);
  }

  /**
   * Remove event listener
   */
  off(listener: TranspilationEventListener): void {
    this.listeners.delete(listener);
  }

  /**
   * Emit event to all listeners
   */
  private emit(event: TranspilationEvent): void {
    this.listeners.forEach(listener => listener(event));
  }

  /**
   * Detect if web workers are supported
   */
  private supportsWorkers(): boolean {
    try {
      return typeof Worker !== 'undefined' && typeof navigator.hardwareConcurrency !== 'undefined';
    } catch {
      return false;
    }
  }

  /**
   * Initialize execution mode (parallel or sequential fallback)
   */
  private async initializeExecutionMode(): Promise<void> {
    if (this.executionMode !== null) {
      return; // Already initialized
    }

    // Try parallel mode first
    if (this.supportsWorkers()) {
      try {
        this.workerPool = new WorkerPoolController();
        await this.workerPool.initialize();
        this.executionMode = 'parallel';
        console.log('✅ Parallel transpilation enabled');
        return;
      } catch (error) {
        console.warn('⚠️  Worker pool initialization failed, falling back to sequential mode:', error);
        this.workerPool?.dispose();
        this.workerPool = null;
      }
    }

    // Fallback to sequential mode
    this.fallbackAdapter = new WasmTranspilerAdapter();
    this.executionMode = 'sequential';
    console.log('ℹ️  Sequential transpilation mode (main thread)');
  }

  /**
   * Calculate current metrics (excluding pause time)
   */
  private calculateMetrics(current: number, total: number): TranspilationEvent['metrics'] {
    const now = Date.now();
    const activeTime = this.isPaused
      ? (this.pauseStartTime - this.startTime - this.totalPausedTime)
      : (now - this.startTime - this.totalPausedTime);

    const elapsedMs = Math.max(0, activeTime);
    const filesPerSecond = current > 0 ? (current / elapsedMs) * 1000 : 0;
    const remainingFiles = total - current;
    const estimatedRemainingMs = filesPerSecond > 0 ? (remainingFiles / filesPerSecond) * 1000 : 0;

    return {
      elapsedMs,
      filesPerSecond,
      estimatedRemainingMs
    };
  }

  /**
   * Get current progress (used for parallel mode events)
   */
  private getCurrentProgress(): TranspilationEvent['progress'] {
    const total = this.sourceFiles.length;
    const current = this.completedFiles;
    return {
      current,
      total,
      percentage: total > 0 ? (current / total) * 100 : 0
    };
  }

  /**
   * Get current metrics (used for parallel mode events)
   */
  private getCurrentMetrics(): TranspilationEvent['metrics'] {
    return this.calculateMetrics(this.completedFiles, this.sourceFiles.length);
  }

  /**
   * Pause transpilation
   */
  pause(): void {
    if (!this.isPaused) {
      this.isPaused = true;
      this.pauseStartTime = Date.now();
    }
  }

  /**
   * Resume transpilation
   */
  resume(): void {
    if (this.isPaused) {
      this.isPaused = false;
      const pauseDuration = Date.now() - this.pauseStartTime;
      this.totalPausedTime += pauseDuration;
      this.pauseStartTime = 0;
    }
  }

  /**
   * Cancel transpilation
   */
  async cancel(): Promise<void> {
    if (this.abortController) {
      this.abortController.abort();
    }

    if (this.workerPool) {
      await this.workerPool.cancel();
    }

    this.emit({
      type: TranspilationEventType.CANCELLED
    });
  }

  /**
   * Start transpilation process (parallel or sequential based on mode)
   */
  async transpile(
    sourceFiles: FileInfo[],
    targetDir: FileSystemDirectoryHandle,
    options: TranspileOptions
  ): Promise<void> {
    // Initialize execution mode on first run
    await this.initializeExecutionMode();

    // Reset state including pause tracking
    this.sourceFiles = sourceFiles;
    this.abortController = new AbortController();
    this.isPaused = false;
    this.startTime = Date.now();
    this.completedFiles = 0;
    this.pauseStartTime = 0;
    this.totalPausedTime = 0;

    // Emit started event
    this.emit({
      type: TranspilationEventType.STARTED,
      progress: {
        current: 0,
        total: sourceFiles.length,
        percentage: 0
      },
      metrics: this.calculateMetrics(0, sourceFiles.length)
    });

    try {
      if (this.executionMode === 'parallel' && this.workerPool) {
        await this.transpileParallel(sourceFiles, targetDir, options);
      } else {
        await this.transpileSequential(sourceFiles, targetDir, options);
      }

      // Emit completed event
      this.emit({
        type: TranspilationEventType.COMPLETED,
        progress: {
          current: this.completedFiles,
          total: sourceFiles.length,
          percentage: 100
        },
        metrics: this.calculateMetrics(this.completedFiles, sourceFiles.length)
      });
    } catch (error) {
      if (error instanceof Error && error.name === 'AbortError') {
        // Already emitted CANCELLED event
        return;
      }

      this.emit({
        type: TranspilationEventType.ERROR,
        error: error instanceof Error ? error.message : String(error)
      });
      throw error;
    }
  }

  /**
   * Transpile using worker pool (parallel mode)
   */
  private async transpileParallel(
    sourceFiles: FileInfo[],
    targetDir: FileSystemDirectoryHandle,
    options: TranspileOptions
  ): Promise<void> {
    if (!this.workerPool) {
      throw new Error('Worker pool not initialized');
    }

    // Read all file contents first
    const sources = new Map<string, string>();
    for (const file of sourceFiles) {
      const fileHandle = await file.handle.getFile();
      const content = await fileHandle.text();
      sources.set(file.path, content);
    }

    // Set up overall progress tracking
    this.workerPool.onOverallProgress((event) => {
      this.completedFiles = event.completed;

      // Emit progress update for real-time UI updates during parallel transpilation
      // This fires as files complete, providing accurate progress during execution
      this.emit({
        type: TranspilationEventType.FILE_COMPLETED,
        progress: {
          current: event.completed,
          total: event.total,
          percentage: event.percentage
        },
        metrics: this.calculateMetrics(event.completed, event.total)
      });
    });

    // Set up per-file progress tracking
    this.workerPool.onProgress((event) => {
      this.emit({
        type: TranspilationEventType.FILE_STARTED,
        filePath: event.file.path,
        fileName: event.file.name,
        progress: {
          current: this.completedFiles,
          total: sourceFiles.length,
          percentage: (this.completedFiles / sourceFiles.length) * 100
        },
        metrics: this.getCurrentMetrics()
      });
    });

    // Transpile all files in parallel
    const results = await this.workerPool.transpileAll(sourceFiles, sources, options);

    // Write results to target directory
    for (const [filePath, result] of results.entries()) {
      // Parse directory path from file.path to preserve structure
      const pathParts = filePath.split('/');
      const fileName = pathParts.pop()!;

      // Create nested directories if needed
      let currentDir = targetDir;
      for (const dirName of pathParts) {
        if (dirName) {
          currentDir = await currentDir.getDirectoryHandle(dirName, { create: true });
        }
      }

      const targetFileName = convertToTargetFileName(fileName);

      if (result.success && result.cCode) {
        // Write transpiled file
        const fileHandle = await currentDir.getFileHandle(targetFileName, { create: true });
        const writable = await fileHandle.createWritable();
        await writable.write(result.cCode);
        await writable.close();

        this.emit({
          type: TranspilationEventType.FILE_COMPLETED,
          filePath,
          fileName: targetFileName,
          result,
          progress: this.getCurrentProgress(),
          metrics: this.getCurrentMetrics()
        });
      } else {
        this.emit({
          type: TranspilationEventType.FILE_ERROR,
          filePath,
          fileName: targetFileName,
          result,
          error: result.error,
          progress: this.getCurrentProgress(),
          metrics: this.getCurrentMetrics()
        });
      }
    }
  }

  /**
   * Transpile sequentially (fallback mode)
   */
  private async transpileSequential(
    sourceFiles: FileInfo[],
    targetDir: FileSystemDirectoryHandle,
    options: TranspileOptions
  ): Promise<void> {
    if (!this.fallbackAdapter) {
      throw new Error('Fallback adapter not initialized');
    }

    for (let i = 0; i < sourceFiles.length; i++) {
      // Check for cancellation
      if (this.abortController?.signal.aborted) {
        throw new Error('Transpilation cancelled');
      }

      // Handle pause
      while (this.isPaused && !this.abortController?.signal.aborted) {
        await new Promise(resolve => setTimeout(resolve, 100));
      }

      const file = sourceFiles[i];

      // Emit file started event
      this.emit({
        type: TranspilationEventType.FILE_STARTED,
        filePath: file.path,
        fileName: file.name,
        progress: {
          current: i,
          total: sourceFiles.length,
          percentage: (i / sourceFiles.length) * 100
        },
        metrics: this.calculateMetrics(i, sourceFiles.length)
      });

      try {
        // Read file content
        const fileHandle = await file.handle.getFile();
        const content = await fileHandle.text();

        // Transpile
        const result = await this.fallbackAdapter.transpile(content, {
          ...options,
          sourcePath: file.path
        });

        // Parse directory path from file.path to preserve structure
        const pathParts = file.path.split('/');
        const fileName = pathParts.pop()!;

        // Create nested directories if needed
        let currentDir = targetDir;
        for (const dirName of pathParts) {
          if (dirName) {
            currentDir = await currentDir.getDirectoryHandle(dirName, { create: true });
          }
        }

        // Write to target directory if successful
        if (result.success && result.cCode) {
          const targetFileName = convertToTargetFileName(fileName);
          const targetFileHandle = await currentDir.getFileHandle(targetFileName, { create: true });
          const writable = await targetFileHandle.createWritable();
          await writable.write(result.cCode);
          await writable.close();
        }

        // Emit file completed event
        this.completedFiles++;
        this.emit({
          type: TranspilationEventType.FILE_COMPLETED,
          filePath: file.path,
          fileName: file.name,
          result,
          progress: {
            current: this.completedFiles,
            total: sourceFiles.length,
            percentage: (this.completedFiles / sourceFiles.length) * 100
          },
          metrics: this.calculateMetrics(this.completedFiles, sourceFiles.length)
        });
      } catch (error) {
        // Emit file error event
        this.completedFiles++;
        this.emit({
          type: TranspilationEventType.FILE_ERROR,
          filePath: file.path,
          fileName: file.name,
          error: error instanceof Error ? error.message : String(error),
          progress: {
            current: this.completedFiles,
            total: sourceFiles.length,
            percentage: (this.completedFiles / sourceFiles.length) * 100
          },
          metrics: this.calculateMetrics(this.completedFiles, sourceFiles.length)
        });
      }
    }
  }

  /**
   * Get current pause state
   */
  isPausedState(): boolean {
    return this.isPaused;
  }

  /**
   * Get current execution mode
   */
  getExecutionMode(): ExecutionMode | null {
    return this.executionMode;
  }

  /**
   * Clean up resources
   */
  dispose(): void {
    this.workerPool?.dispose();
    this.fallbackAdapter?.dispose?.();
    this.listeners.clear();
  }
}
