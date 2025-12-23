/**
 * Core Interfaces - Public API
 *
 * Central export point for all core interfaces and types.
 * Use this for clean imports: `import { IFileSystem, ITranspiler } from '@/core/interfaces'`
 */

// Core Interfaces
export type { IFileSystem } from './IFileSystem';
export type { ITranspiler } from './ITranspiler';
export type { IProgressReporter } from './IProgressReporter';

// Type Definitions
export type {
  TranspileOptions,
  TranspileResult,
  ValidationResult,
  ProgressState,
  FileInfo,
  DirectoryHandle,
  FileHandle,
} from './types';
