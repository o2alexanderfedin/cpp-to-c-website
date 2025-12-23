import { renderHook, act } from '@testing-library/react';
import { describe, it, expect } from 'vitest';
import { useWizardState } from './useWizardState';
import type { FileInfo, TranspileResult } from './types';

describe('useWizardState', () => {
  it('initializes with default state', () => {
    const { result } = renderHook(() => useWizardState());

    expect(result.current.state.sourceDir).toBeNull();
    expect(result.current.state.sourceFiles).toEqual([]);
    expect(result.current.state.targetDir).toBeNull();
    expect(result.current.state.targetOptions).toEqual({
      targetStandard: 'c99',
      includeACSL: true
    });
    expect(result.current.state.transpilationResults.size).toBe(0);
    expect(result.current.state.isTranspiling).toBe(false);
  });

  it('sets source directory and files', () => {
    const { result } = renderHook(() => useWizardState());
    const mockDir = {} as FileSystemDirectoryHandle;
    const mockFiles: FileInfo[] = [
      { path: 'test.cpp', name: 'test.cpp', handle: {} as FileSystemFileHandle, size: 100 }
    ];

    act(() => {
      result.current.handlers.setSourceDir(mockDir, mockFiles);
    });

    expect(result.current.state.sourceDir).toBe(mockDir);
    expect(result.current.state.sourceFiles).toEqual(mockFiles);
  });

  it('validates step 2 navigation requires source dir', () => {
    const { result } = renderHook(() => useWizardState());

    // Initially can't navigate (no source dir)
    expect(result.current.validation.canNavigateToStep2()).toBe(false);

    // After setting source dir, can navigate
    act(() => {
      result.current.handlers.setSourceDir(
        {} as FileSystemDirectoryHandle,
        [{ path: 'test.cpp', name: 'test.cpp', handle: {} as FileSystemFileHandle, size: 100 }]
      );
    });

    expect(result.current.validation.canNavigateToStep2()).toBe(true);
  });

  it('validates step 3 navigation requires target dir', () => {
    const { result } = renderHook(() => useWizardState());

    expect(result.current.validation.canNavigateToStep3()).toBe(false);

    act(() => {
      result.current.handlers.setTargetDir({} as FileSystemDirectoryHandle);
    });

    expect(result.current.validation.canNavigateToStep3()).toBe(true);
  });

  it('validates step 4 navigation requires completed transpilation', () => {
    const { result } = renderHook(() => useWizardState());

    expect(result.current.validation.canNavigateToStep4()).toBe(false);

    // Start transpilation
    act(() => {
      result.current.handlers.startTranspilation();
    });

    // Still can't navigate while transpiling
    expect(result.current.validation.canNavigateToStep4()).toBe(false);

    // Add result
    act(() => {
      const mockResult: TranspileResult = { success: true, cCode: '// code' };
      result.current.handlers.addTranspilationResult('test.cpp', mockResult);
    });

    // Still can't navigate while isTranspiling is true
    expect(result.current.validation.canNavigateToStep4()).toBe(false);

    // Stop transpilation
    act(() => {
      result.current.handlers.stopTranspilation();
    });

    // Now can navigate
    expect(result.current.validation.canNavigateToStep4()).toBe(true);
  });

  it('updates target options', () => {
    const { result } = renderHook(() => useWizardState());

    act(() => {
      result.current.handlers.setTargetOptions({
        targetStandard: 'c11',
        includeACSL: false
      });
    });

    expect(result.current.state.targetOptions).toEqual({
      targetStandard: 'c11',
      includeACSL: false
    });
  });

  it('tracks current file during transpilation', () => {
    const { result } = renderHook(() => useWizardState());

    act(() => {
      result.current.handlers.setCurrentFile('test.cpp');
    });

    expect(result.current.state.currentFile).toBe('test.cpp');

    act(() => {
      result.current.handlers.setCurrentFile(null);
    });

    expect(result.current.state.currentFile).toBeNull();
  });

  it('accumulates transpilation results', () => {
    const { result } = renderHook(() => useWizardState());

    const result1: TranspileResult = { success: true, cCode: '// file1' };
    const result2: TranspileResult = { success: false, error: 'Parse error' };

    act(() => {
      result.current.handlers.addTranspilationResult('file1.cpp', result1);
      result.current.handlers.addTranspilationResult('file2.cpp', result2);
    });

    expect(result.current.state.transpilationResults.size).toBe(2);
    expect(result.current.state.transpilationResults.get('file1.cpp')).toEqual(result1);
    expect(result.current.state.transpilationResults.get('file2.cpp')).toEqual(result2);
  });

  it('clears results when starting new transpilation', () => {
    const { result } = renderHook(() => useWizardState());

    // Add some results
    act(() => {
      result.current.handlers.addTranspilationResult('test.cpp', { success: true });
    });

    expect(result.current.state.transpilationResults.size).toBe(1);

    // Start new transpilation
    act(() => {
      result.current.handlers.startTranspilation();
    });

    expect(result.current.state.transpilationResults.size).toBe(0);
    expect(result.current.state.isTranspiling).toBe(true);
  });
});
