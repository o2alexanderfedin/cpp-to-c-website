import { renderHook, act, waitFor } from '@testing-library/react';
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { useTranspilation } from './useTranspilation';
import type { FileInfo } from '../types';

// Mock TranspilationController
const mockController = {
  on: vi.fn(),
  off: vi.fn(),
  transpile: vi.fn(),
  pause: vi.fn(),
  resume: vi.fn(),
  cancel: vi.fn(),
  isPausedState: vi.fn().mockReturnValue(false),
  dispose: vi.fn()
};

vi.mock('../controllers/TranspilationController', () => ({
  TranspilationController: vi.fn().mockImplementation(() => mockController),
  TranspilationEventType: {
    STARTED: 'started',
    FILE_STARTED: 'file_started',
    FILE_COMPLETED: 'file_completed',
    FILE_ERROR: 'file_error',
    COMPLETED: 'completed',
    CANCELLED: 'cancelled',
    ERROR: 'error'
  }
}));

describe('useTranspilation', () => {
  beforeEach(() => {
    vi.clearAllMocks();
  });

  it('provides start, pause, resume, cancel, isPaused functions', () => {
    const { result } = renderHook(() => useTranspilation({}));

    expect(result.current.start).toBeDefined();
    expect(result.current.pause).toBeDefined();
    expect(result.current.resume).toBeDefined();
    expect(result.current.cancel).toBeDefined();
    expect(result.current.isPaused).toBeDefined();
  });

  it('initializes controller on mount', () => {
    renderHook(() => useTranspilation({}));

    // TranspilationController should be instantiated
    expect(mockController).toBeDefined();
  });

  it('disposes controller on unmount', () => {
    const { unmount } = renderHook(() => useTranspilation({}));

    unmount();

    expect(mockController.dispose).toHaveBeenCalled();
  });

  it('registers event listener on mount', () => {
    renderHook(() => useTranspilation({}));

    expect(mockController.on).toHaveBeenCalled();
  });

  it('unregisters event listener on unmount', () => {
    const { unmount } = renderHook(() => useTranspilation({}));

    unmount();

    expect(mockController.off).toHaveBeenCalled();
  });

  it('calls start on controller when start is invoked', async () => {
    const { result } = renderHook(() => useTranspilation({}));

    const mockFiles: FileInfo[] = [
      { path: 'test.cpp', name: 'test.cpp', handle: {} as any, size: 100 }
    ];
    const mockTargetDir = {} as FileSystemDirectoryHandle;
    const mockOptions = { targetStandard: 'c99' as const, includeACSL: true };

    await act(async () => {
      await result.current.start(mockFiles, mockTargetDir, mockOptions);
    });

    expect(mockController.transpile).toHaveBeenCalledWith(mockFiles, mockTargetDir, mockOptions);
  });

  it('calls pause on controller when pause is invoked', () => {
    const { result } = renderHook(() => useTranspilation({}));

    act(() => {
      result.current.pause();
    });

    expect(mockController.pause).toHaveBeenCalled();
  });

  it('calls resume on controller when resume is invoked', () => {
    const { result } = renderHook(() => useTranspilation({}));

    act(() => {
      result.current.resume();
    });

    expect(mockController.resume).toHaveBeenCalled();
  });

  it('calls cancel on controller when cancel is invoked', () => {
    const { result } = renderHook(() => useTranspilation({}));

    act(() => {
      result.current.cancel();
    });

    expect(mockController.cancel).toHaveBeenCalled();
  });

  it('calls isPausedState on controller when isPaused is invoked', () => {
    const { result } = renderHook(() => useTranspilation({}));

    const isPaused = result.current.isPaused();

    expect(mockController.isPausedState).toHaveBeenCalled();
    expect(isPaused).toBe(false);
  });

  it('invokes onFileStarted callback when FILE_STARTED event occurs', () => {
    const onFileStarted = vi.fn();
    renderHook(() => useTranspilation({ onFileStarted }));

    // Get the event handler that was registered
    const eventHandler = mockController.on.mock.calls[0][0];

    // Simulate FILE_STARTED event
    act(() => {
      eventHandler({
        type: 'file_started',
        filePath: 'test.cpp',
        fileName: 'test.cpp'
      });
    });

    expect(onFileStarted).toHaveBeenCalledWith('test.cpp');
  });

  it('invokes onFileCompleted callback when FILE_COMPLETED event occurs', () => {
    const onFileCompleted = vi.fn();
    renderHook(() => useTranspilation({ onFileCompleted }));

    const eventHandler = mockController.on.mock.calls[0][0];

    const mockResult = { success: true, cCode: '// code' };
    act(() => {
      eventHandler({
        type: 'file_completed',
        filePath: 'test.cpp',
        result: mockResult
      });
    });

    expect(onFileCompleted).toHaveBeenCalledWith('test.cpp', mockResult);
  });

  it('invokes onFileError callback when FILE_ERROR event occurs', () => {
    const onFileError = vi.fn();
    renderHook(() => useTranspilation({ onFileError }));

    const eventHandler = mockController.on.mock.calls[0][0];

    act(() => {
      eventHandler({
        type: 'file_error',
        filePath: 'test.cpp',
        error: 'Test error'
      });
    });

    expect(onFileError).toHaveBeenCalledWith('test.cpp', 'Test error');
  });

  it('invokes onProgress callback for events with progress', () => {
    const onProgress = vi.fn();
    renderHook(() => useTranspilation({ onProgress }));

    const eventHandler = mockController.on.mock.calls[0][0];

    act(() => {
      eventHandler({
        type: 'file_started',
        filePath: 'test.cpp',
        progress: { current: 1, total: 10, percentage: 10 }
      });
    });

    expect(onProgress).toHaveBeenCalledWith(1, 10, 10);
  });

  it('invokes onMetrics callback for events with metrics', () => {
    const onMetrics = vi.fn();
    renderHook(() => useTranspilation({ onMetrics }));

    const eventHandler = mockController.on.mock.calls[0][0];

    act(() => {
      eventHandler({
        type: 'file_started',
        filePath: 'test.cpp',
        metrics: { elapsedMs: 1000, filesPerSecond: 2.5, estimatedRemainingMs: 3000 }
      });
    });

    expect(onMetrics).toHaveBeenCalledWith(1000, 2.5, 3000);
  });

  it('invokes onCompleted callback when COMPLETED event occurs', () => {
    const onCompleted = vi.fn();
    renderHook(() => useTranspilation({ onCompleted }));

    const eventHandler = mockController.on.mock.calls[0][0];

    act(() => {
      eventHandler({
        type: 'completed'
      });
    });

    expect(onCompleted).toHaveBeenCalled();
  });

  it('invokes onCancelled callback when CANCELLED event occurs', () => {
    const onCancelled = vi.fn();
    renderHook(() => useTranspilation({ onCancelled }));

    const eventHandler = mockController.on.mock.calls[0][0];

    act(() => {
      eventHandler({
        type: 'cancelled'
      });
    });

    expect(onCancelled).toHaveBeenCalled();
  });

  it('invokes onError callback when ERROR event occurs', () => {
    const onError = vi.fn();
    renderHook(() => useTranspilation({ onError }));

    const eventHandler = mockController.on.mock.calls[0][0];

    act(() => {
      eventHandler({
        type: 'error',
        error: 'Global error'
      });
    });

    expect(onError).toHaveBeenCalledWith('Global error');
  });

  it('does not error if callbacks are not provided', () => {
    renderHook(() => useTranspilation({}));

    const eventHandler = mockController.on.mock.calls[0][0];

    // Should not throw when callbacks are undefined
    expect(() => {
      act(() => {
        eventHandler({ type: 'file_started', filePath: 'test.cpp' });
        eventHandler({ type: 'file_completed', filePath: 'test.cpp', result: { success: true } });
        eventHandler({ type: 'completed' });
      });
    }).not.toThrow();
  });
});
