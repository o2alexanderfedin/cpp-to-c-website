import type { FileInfo, TranspileOptions, TranspileResult } from '../components/playground/wizard/types';
import type { WorkerRequest, WorkerResponse } from './types';

/**
 * Task in the queue
 */
interface TranspileTask {
  id: string;
  file: FileInfo;
  source: string;
  options: TranspileOptions;
  resolve: (result: TranspileResult) => void;
  reject: (error: Error) => void;
  retryCount: number;
}

/**
 * Progress event listener type
 */
export type ProgressListener = (event: {
  file: FileInfo;
  progress: number;
  stage?: string;
}) => void;

/**
 * Overall progress listener type
 */
export type OverallProgressListener = (event: {
  completed: number;
  total: number;
  percentage: number;
  currentFiles: FileInfo[];
}) => void;

/**
 * Worker Pool Controller
 * Manages multiple web workers for parallel transpilation
 *
 * Architecture:
 * - Pre-warmed worker pool (WASM loaded upfront)
 * - Dynamic task assignment (work-stealing pattern)
 * - Worker error recovery with task retry
 * - Progress aggregation
 * - Graceful degradation
 */
export class WorkerPoolController {
  private workers: Worker[] = [];
  private taskQueue: TranspileTask[] = [];
  private activeTasksByWorker = new Map<Worker, TranspileTask>();
  private workerReady = new Set<Worker>();
  private initPromise: Promise<void> | null = null;
  private disposed = false;
  private progressListeners: Set<ProgressListener> = new Set();
  private overallProgressListeners: Set<OverallProgressListener> = new Set();
  private completedCount = 0;
  private totalCount = 0;

  constructor(private workerCount?: number) {
    this.workerCount = workerCount || this.getOptimalWorkerCount();
  }

  /**
   * Get optimal worker count based on CPU cores
   */
  private getOptimalWorkerCount(): number {
    const cores = navigator.hardwareConcurrency || 4;

    // For CPU-intensive tasks:
    // - Use cores - 1 (leave one for UI thread)
    // - Cap at 8 to avoid diminishing returns
    // - Minimum of 2 for parallel benefit
    return Math.min(8, Math.max(2, cores - 1));
  }

  /**
   * Initialize worker pool (pre-warm WASM)
   */
  async initialize(): Promise<void> {
    if (this.initPromise) return this.initPromise;
    if (this.disposed) throw new Error('Controller already disposed');

    this.initPromise = (async () => {
      // Create workers
      this.workers = Array(this.workerCount!)
        .fill(null)
        .map(() =>
          new Worker(new URL('./transpiler.worker.ts', import.meta.url), {
            type: 'module'
          })
        );

      // Set up message handlers
      this.workers.forEach((worker, index) => {
        worker.onmessage = (e) => this.handleWorkerMessage(e, worker);
        worker.onerror = (e) => this.handleWorkerError(e, worker, index);
      });

      // Initialize all workers (pre-warm WASM)
      await Promise.all(
        this.workers.map(
          (worker) =>
            new Promise<void>((resolve, reject) => {
              const timeout = setTimeout(() => {
                reject(new Error('Worker initialization timeout'));
              }, 10000); // 10 second timeout

              const handler = (e: MessageEvent<WorkerResponse>) => {
                if (e.data.type === 'READY') {
                  this.workerReady.add(worker);
                  worker.removeEventListener('message', handler);
                  clearTimeout(timeout);
                  resolve();
                } else if (e.data.type === 'ERROR') {
                  worker.removeEventListener('message', handler);
                  clearTimeout(timeout);
                  reject(new Error(e.data.error));
                }
              };

              worker.addEventListener('message', handler);
              worker.postMessage({ type: 'INIT' } as WorkerRequest);
            })
        )
      );
    })();

    return this.initPromise;
  }

  /**
   * Transpile a single file
   */
  async transpile(
    file: FileInfo,
    source: string,
    options: TranspileOptions
  ): Promise<TranspileResult> {
    await this.initialize();

    if (this.disposed) {
      throw new Error('Controller already disposed');
    }

    return new Promise<TranspileResult>((resolve, reject) => {
      const task: TranspileTask = {
        id: crypto.randomUUID(),
        file,
        source,
        options,
        resolve,
        reject,
        retryCount: 0
      };

      this.taskQueue.push(task);
      this.assignTasks();
    });
  }

  /**
   * Transpile multiple files in parallel
   */
  async transpileAll(
    files: FileInfo[],
    sources: Map<string, string>,
    options: TranspileOptions
  ): Promise<Map<string, TranspileResult>> {
    await this.initialize();

    // Reset progress tracking
    this.completedCount = 0;
    this.totalCount = files.length;
    this.emitOverallProgress();

    const results = new Map<string, TranspileResult>();

    // Create promises for all files
    const promises = files.map(async (file) => {
      const source = sources.get(file.path);
      if (!source) {
        throw new Error(`No source found for file: ${file.path}`);
      }

      const result = await this.transpile(file, source, options);
      results.set(file.path, result);
    });

    // Wait for all to complete
    await Promise.all(promises);

    return results;
  }

  /**
   * Assign tasks to available workers (dynamic load balancing)
   */
  private assignTasks(): void {
    for (const worker of this.workers) {
      // Check if worker is available
      if (!this.activeTasksByWorker.has(worker) && this.taskQueue.length > 0) {
        const task = this.taskQueue.shift()!;
        this.activeTasksByWorker.set(worker, task);

        // Send transpilation request to worker (source already provided)
        worker.postMessage({
          type: 'TRANSPILE',
          taskId: task.id,
          source: task.source,
          options: task.options
        } as WorkerRequest);
      }
    }
  }

  /**
   * Handle message from worker
   */
  private handleWorkerMessage(e: MessageEvent<WorkerResponse>, worker: Worker): void {
    const msg = e.data;

    switch (msg.type) {
      case 'SUCCESS': {
        const task = this.activeTasksByWorker.get(worker);
        if (task && task.id === msg.taskId) {
          this.completedCount++;
          task.resolve(msg.result);
          this.activeTasksByWorker.delete(worker);
          this.emitOverallProgress();
          this.assignTasks(); // Assign next task to this worker
        }
        break;
      }

      case 'ERROR': {
        const task = this.activeTasksByWorker.get(worker);
        if (task && task.id === msg.taskId) {
          this.completedCount++;
          task.reject(new Error(msg.error));
          this.activeTasksByWorker.delete(worker);
          this.emitOverallProgress();
          this.assignTasks(); // Assign next task to this worker
        }
        break;
      }

      case 'PROGRESS': {
        const task = this.activeTasksByWorker.get(worker);
        if (task && task.id === msg.taskId) {
          this.emitProgress(task.file, msg.progress, msg.stage);
        }
        break;
      }

      case 'READY': {
        // Worker became ready
        this.workerReady.add(worker);
        break;
      }
    }
  }

  /**
   * Handle worker error (crash recovery)
   */
  private async handleWorkerError(
    error: ErrorEvent,
    worker: Worker,
    index: number
  ): Promise<void> {
    console.error(`Worker ${index} crashed:`, error.message);

    // Get task that was running on this worker
    const task = this.activeTasksByWorker.get(worker);
    this.activeTasksByWorker.delete(worker);
    this.workerReady.delete(worker);

    // Terminate broken worker
    worker.terminate();

    try {
      // Create replacement worker
      const newWorker = new Worker(
        new URL('./transpiler.worker.ts', import.meta.url),
        { type: 'module' }
      );

      this.workers[index] = newWorker;
      newWorker.onmessage = (e) => this.handleWorkerMessage(e, newWorker);
      newWorker.onerror = (e) => this.handleWorkerError(e, newWorker, index);

      // Reinitialize worker
      await new Promise<void>((resolve, reject) => {
        const timeout = setTimeout(() => {
          reject(new Error('Worker re-initialization timeout'));
        }, 10000);

        const handler = (e: MessageEvent<WorkerResponse>) => {
          if (e.data.type === 'READY') {
            this.workerReady.add(newWorker);
            newWorker.removeEventListener('message', handler);
            clearTimeout(timeout);
            resolve();
          }
        };

        newWorker.addEventListener('message', handler);
        newWorker.postMessage({ type: 'INIT' } as WorkerRequest);
      });

      // Retry task if retry limit not exceeded
      if (task) {
        if (task.retryCount < 3) {
          task.retryCount++;
          this.taskQueue.unshift(task); // Add to front of queue
          this.assignTasks();
        } else {
          // Max retries exceeded
          task.reject(
            new Error(
              `Worker crashed while processing ${task.file.path} (max retries exceeded)`
            )
          );
        }
      }
    } catch (recoveryError) {
      console.error(`Failed to recover worker ${index}:`, recoveryError);

      // Report task failure if there was one
      if (task) {
        task.reject(
          new Error(
            `Worker crashed and recovery failed for ${task.file.path}: ${
              recoveryError instanceof Error ? recoveryError.message : String(recoveryError)
            }`
          )
        );
      }
    }
  }

  /**
   * Cancel all pending tasks
   */
  async cancel(): Promise<void> {
    // Reject all pending tasks
    while (this.taskQueue.length > 0) {
      const task = this.taskQueue.shift()!;
      task.reject(new Error('Transpilation cancelled'));
    }

    // Send cancel to all active workers
    for (const [worker, task] of this.activeTasksByWorker.entries()) {
      worker.postMessage({
        type: 'CANCEL',
        taskId: task.id
      } as WorkerRequest);
    }

    // Wait for all workers to finish current task
    await this.waitForAllWorkersIdle();
  }

  /**
   * Wait for all workers to become idle
   */
  private async waitForAllWorkersIdle(): Promise<void> {
    return new Promise((resolve) => {
      const check = setInterval(() => {
        if (this.activeTasksByWorker.size === 0) {
          clearInterval(check);
          resolve();
        }
      }, 100);
    });
  }

  /**
   * Dispose worker pool
   */
  dispose(): void {
    if (this.disposed) return;

    // Clear task queue
    while (this.taskQueue.length > 0) {
      const task = this.taskQueue.shift()!;
      task.reject(new Error('Controller disposed'));
    }

    // Terminate all workers
    this.workers.forEach((worker) => {
      worker.postMessage({ type: 'DISPOSE' } as WorkerRequest);
      worker.terminate();
    });

    this.workers = [];
    this.activeTasksByWorker.clear();
    this.workerReady.clear();
    this.disposed = true;
    this.initPromise = null;
  }

  /**
   * Get worker pool stats
   */
  getStats(): {
    workerCount: number;
    readyWorkers: number;
    activeWorkers: number;
    queuedTasks: number;
  } {
    return {
      workerCount: this.workers.length,
      readyWorkers: this.workerReady.size,
      activeWorkers: this.activeTasksByWorker.size,
      queuedTasks: this.taskQueue.length
    };
  }

  /**
   * Add progress listener (per-file progress)
   */
  onProgress(listener: ProgressListener): void {
    this.progressListeners.add(listener);
  }

  /**
   * Remove progress listener
   */
  offProgress(listener: ProgressListener): void {
    this.progressListeners.delete(listener);
  }

  /**
   * Add overall progress listener (aggregate progress)
   */
  onOverallProgress(listener: OverallProgressListener): void {
    this.overallProgressListeners.add(listener);
  }

  /**
   * Remove overall progress listener
   */
  offOverallProgress(listener: OverallProgressListener): void {
    this.overallProgressListeners.delete(listener);
  }

  /**
   * Emit progress event
   */
  private emitProgress(file: FileInfo, progress: number, stage?: string): void {
    this.progressListeners.forEach((listener) =>
      listener({ file, progress, stage })
    );
  }

  /**
   * Emit overall progress event
   */
  private emitOverallProgress(): void {
    const currentFiles = Array.from(this.activeTasksByWorker.values()).map(
      (task) => task.file
    );

    this.overallProgressListeners.forEach((listener) =>
      listener({
        completed: this.completedCount,
        total: this.totalCount,
        percentage: this.totalCount > 0 ? (this.completedCount / this.totalCount) * 100 : 0,
        currentFiles
      })
    );
  }
}
