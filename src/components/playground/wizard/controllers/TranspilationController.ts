import { WasmTranspilerAdapter } from '../../../../adapters/WasmTranspilerAdapter';
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
 * Transpilation controller
 * Orchestrates sequential file transpilation with progress tracking
 */
export class TranspilationController {
  private transpiler: WasmTranspilerAdapter;
  private listeners: Set<TranspilationEventListener> = new Set();
  private abortController: AbortController | null = null;
  private isPaused: boolean = false;
  private startTime: number = 0;
  private completedFiles: number = 0;
  private pauseStartTime: number = 0;
  private totalPausedTime: number = 0;

  constructor() {
    this.transpiler = new WasmTranspilerAdapter();
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
   * Start transpilation process
   */
  async transpile(
    sourceFiles: FileInfo[],
    targetDir: FileSystemDirectoryHandle,
    options: TranspileOptions
  ): Promise<void> {
    // Reset state including pause tracking
    this.abortController = new AbortController();
    this.isPaused = false;
    this.startTime = Date.now();
    this.completedFiles = 0;
    this.pauseStartTime = 0;
    this.totalPausedTime = 0;

    const total = sourceFiles.length;

    // Emit started event
    this.emit({
      type: TranspilationEventType.STARTED,
      progress: { current: 0, total, percentage: 0 },
      metrics: { elapsedMs: 0, filesPerSecond: 0, estimatedRemainingMs: 0 }
    });

    try {
      // Process each file sequentially
      for (let i = 0; i < sourceFiles.length; i++) {
        // Check for cancellation
        if (this.abortController.signal.aborted) {
          this.emit({
            type: TranspilationEventType.CANCELLED,
            progress: { current: i, total, percentage: (i / total) * 100 }
          });
          return;
        }

        // Wait if paused
        while (this.isPaused && !this.abortController.signal.aborted) {
          await new Promise(resolve => setTimeout(resolve, 100));
        }

        const file = sourceFiles[i];
        const current = i + 1;

        // Emit file started event
        this.emit({
          type: TranspilationEventType.FILE_STARTED,
          filePath: file.path,
          fileName: file.name,
          progress: {
            current,
            total,
            percentage: (current / total) * 100
          },
          metrics: this.calculateMetrics(current - 1, total)
        });

        try {
          // Read source file content
          const fileHandle = file.handle;
          const fileData = await fileHandle.getFile();
          const sourceCode = await fileData.text();

          // Transpile using WASM adapter
          const result = await this.transpiler.transpile(sourceCode, {
            ...options,
            sourcePath: file.path
          });

          // Write result to target directory if successful
          if (result.success && result.cCode) {
            const targetFileName = convertToTargetFileName(file.name);
            const targetFileHandle = await targetDir.getFileHandle(targetFileName, { create: true });
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
              current,
              total,
              percentage: (current / total) * 100
            },
            metrics: this.calculateMetrics(current, total)
          });

        } catch (error) {
          // Emit file error event (but continue with other files)
          const errorMessage = error instanceof Error ? error.message : String(error);

          this.emit({
            type: TranspilationEventType.FILE_ERROR,
            filePath: file.path,
            fileName: file.name,
            result: {
              success: false,
              error: errorMessage,
              sourcePath: file.path
            },
            progress: {
              current,
              total,
              percentage: (current / total) * 100
            },
            error: errorMessage
          });

          this.completedFiles++;
        }
      }

      // Emit completed event
      this.emit({
        type: TranspilationEventType.COMPLETED,
        progress: { current: total, total, percentage: 100 },
        metrics: this.calculateMetrics(total, total)
      });

    } catch (error) {
      // Emit global error event
      const errorMessage = error instanceof Error ? error.message : String(error);

      this.emit({
        type: TranspilationEventType.ERROR,
        error: errorMessage
      });
    }
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
  cancel(): void {
    if (this.abortController) {
      this.abortController.abort();
    }
  }

  /**
   * Get current pause state
   */
  isPausedState(): boolean {
    return this.isPaused;
  }

  /**
   * Clean up resources
   */
  dispose(): void {
    this.cancel();
    this.listeners.clear();
    this.transpiler.dispose();
  }
}
