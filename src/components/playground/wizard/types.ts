/**
 * Wizard state interface
 */
export interface WizardState {
  // Step 1: Source directory
  sourceDir: FileSystemDirectoryHandle | null;
  sourceFiles: FileInfo[];

  // Step 2: Target directory
  targetDir: FileSystemDirectoryHandle | null;
  targetOptions: TranspileOptions;

  // Step 3: Transpilation progress
  transpilationResults: Map<string, TranspileResult>;
  currentFile: string | null;
  isTranspiling: boolean;

  // Step 4: Results
  selectedPreviewFile: string | null;
}

/**
 * File information
 */
export interface FileInfo {
  path: string;
  name: string;
  handle: FileSystemFileHandle;
  size: number;
}

/**
 * Transpilation options
 */
export interface TranspileOptions {
  targetStandard: 'c99' | 'c11';
  includeACSL: boolean;
}

/**
 * Transpilation result
 */
export interface TranspileResult {
  success: boolean;
  cCode?: string;
  error?: string;
  diagnostics?: string[];
}
