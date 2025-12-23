import { useEffect, useRef, useCallback } from 'react';
import { TranspilationController, TranspilationEventType } from '../controllers/TranspilationController';
import type { TranspilationEvent } from '../controllers/TranspilationController';
import type { FileInfo, TranspileOptions, TranspileResult } from '../types';

/**
 * Hook interface for transpilation state updates
 */
interface UseTranspilationCallbacks {
  onFileStarted?: (filePath: string) => void;
  onFileCompleted?: (filePath: string, result: TranspileResult) => void;
  onFileError?: (filePath: string, error: string) => void;
  onProgress?: (current: number, total: number, percentage: number) => void;
  onMetrics?: (elapsedMs: number, filesPerSecond: number, estimatedRemainingMs: number) => void;
  onCompleted?: () => void;
  onCancelled?: () => void;
  onError?: (error: string) => void;
}

/**
 * Custom hook for transpilation controller
 */
export function useTranspilation(callbacks: UseTranspilationCallbacks) {
  const controllerRef = useRef<TranspilationController | null>(null);

  // Initialize controller
  useEffect(() => {
    controllerRef.current = new TranspilationController();

    return () => {
      if (controllerRef.current) {
        controllerRef.current.dispose();
      }
    };
  }, []);

  // Set up event listeners
  useEffect(() => {
    const controller = controllerRef.current;
    if (!controller) return;

    const handleEvent = (event: TranspilationEvent) => {
      switch (event.type) {
        case TranspilationEventType.FILE_STARTED:
          if (event.filePath) {
            callbacks.onFileStarted?.(event.filePath);
          }
          break;

        case TranspilationEventType.FILE_COMPLETED:
          if (event.filePath && event.result) {
            callbacks.onFileCompleted?.(event.filePath, event.result);
          }
          break;

        case TranspilationEventType.FILE_ERROR:
          if (event.filePath && event.error) {
            callbacks.onFileError?.(event.filePath, event.error);
          }
          break;

        case TranspilationEventType.COMPLETED:
          callbacks.onCompleted?.();
          break;

        case TranspilationEventType.CANCELLED:
          callbacks.onCancelled?.();
          break;

        case TranspilationEventType.ERROR:
          if (event.error) {
            callbacks.onError?.(event.error);
          }
          break;
      }

      // Update progress and metrics for all events that have them
      if (event.progress) {
        callbacks.onProgress?.(
          event.progress.current,
          event.progress.total,
          event.progress.percentage
        );
      }

      if (event.metrics) {
        callbacks.onMetrics?.(
          event.metrics.elapsedMs,
          event.metrics.filesPerSecond,
          event.metrics.estimatedRemainingMs
        );
      }
    };

    controller.on(handleEvent);

    return () => {
      controller.off(handleEvent);
    };
  }, [callbacks]);

  // Start transpilation
  const start = useCallback(
    async (
      sourceFiles: FileInfo[],
      targetDir: FileSystemDirectoryHandle,
      options: TranspileOptions
    ) => {
      if (controllerRef.current) {
        await controllerRef.current.transpile(sourceFiles, targetDir, options);
      }
    },
    []
  );

  // Pause transpilation
  const pause = useCallback(() => {
    controllerRef.current?.pause();
  }, []);

  // Resume transpilation
  const resume = useCallback(() => {
    controllerRef.current?.resume();
  }, []);

  // Cancel transpilation
  const cancel = useCallback(() => {
    controllerRef.current?.cancel();
  }, []);

  // Get pause state
  const isPaused = useCallback(() => {
    return controllerRef.current?.isPausedState() ?? false;
  }, []);

  // Get execution mode
  const getExecutionMode = useCallback(() => {
    return controllerRef.current?.getExecutionMode() ?? null;
  }, []);

  return {
    start,
    pause,
    resume,
    cancel,
    isPaused,
    getExecutionMode
  };
}
