import { useState, useCallback } from 'react';
import type { WizardState, FileInfo, TranspileOptions, TranspileResult } from './types';

/**
 * Custom hook for wizard state management
 *
 * Provides centralized state and state update functions for all wizard steps
 */
export const useWizardState = () => {
  const [state, setState] = useState<WizardState>({
    sourceDir: null,
    sourceFiles: [],
    targetDir: null,
    targetOptions: {
      targetStandard: 'c99',
      includeACSL: true
    },
    transpilationResults: new Map(),
    currentFile: null,
    isTranspiling: false,
    selectedPreviewFile: null
  });

  // Step 1: Source directory handlers
  const setSourceDir = useCallback((dir: FileSystemDirectoryHandle, files: FileInfo[]) => {
    setState(prev => ({
      ...prev,
      sourceDir: dir,
      sourceFiles: files
    }));
  }, []);

  // Step 2: Target directory handlers
  const setTargetDir = useCallback((dir: FileSystemDirectoryHandle) => {
    setState(prev => ({
      ...prev,
      targetDir: dir
    }));
  }, []);

  const setTargetOptions = useCallback((options: TranspileOptions) => {
    setState(prev => ({
      ...prev,
      targetOptions: options
    }));
  }, []);

  // Step 3: Transpilation handlers
  const startTranspilation = useCallback(() => {
    setState(prev => ({
      ...prev,
      isTranspiling: true,
      transpilationResults: new Map(),
      currentFile: null
    }));
  }, []);

  const setCurrentFile = useCallback((filePath: string | null) => {
    setState(prev => ({
      ...prev,
      currentFile: filePath
    }));
  }, []);

  const addTranspilationResult = useCallback((filePath: string, result: TranspileResult) => {
    setState(prev => {
      const newResults = new Map(prev.transpilationResults);
      newResults.set(filePath, result);
      return {
        ...prev,
        transpilationResults: newResults
      };
    });
  }, []);

  const stopTranspilation = useCallback(() => {
    setState(prev => ({
      ...prev,
      isTranspiling: false,
      currentFile: null
    }));
  }, []);

  // Step 4: Results handlers
  const setSelectedPreviewFile = useCallback((filePath: string | null) => {
    setState(prev => ({
      ...prev,
      selectedPreviewFile: filePath
    }));
  }, []);

  // Validation functions
  const canNavigateToStep2 = useCallback(() => {
    return state.sourceDir !== null && state.sourceFiles.length > 0;
  }, [state.sourceDir, state.sourceFiles.length]);

  const canNavigateToStep3 = useCallback(() => {
    return state.targetDir !== null;
  }, [state.targetDir]);

  const canNavigateToStep4 = useCallback(() => {
    return state.transpilationResults.size > 0 && !state.isTranspiling;
  }, [state.transpilationResults.size, state.isTranspiling]);

  return {
    state,
    handlers: {
      setSourceDir,
      setTargetDir,
      setTargetOptions,
      startTranspilation,
      setCurrentFile,
      addTranspilationResult,
      stopTranspilation,
      setSelectedPreviewFile
    },
    validation: {
      canNavigateToStep2,
      canNavigateToStep3,
      canNavigateToStep4
    }
  };
};
