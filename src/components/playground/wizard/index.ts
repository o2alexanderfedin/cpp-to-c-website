// Components
export { WizardStepper } from './WizardStepper';
export { PlaygroundWizard } from './PlaygroundWizard';
export { Step1SourceSelection } from './Step1SourceSelection';
export { Step2TargetSelection } from './Step2TargetSelection';
export { Step3Transpilation } from './Step3Transpilation';
export { Step4Results } from './Step4Results';
export { FileTreeView, FileStatus } from './FileTreeView';
export { FileStatistics } from './FileStatistics';
export { FileContentDisplay } from './FileContentDisplay';
export { DualPaneViewer } from './DualPaneViewer';
export { TabbedCodeViewer } from './TabbedCodeViewer';
export { SyntaxHighlighter } from './SyntaxHighlighter';
export { PermissionIndicator } from './PermissionIndicator';
export { ConflictWarning } from './ConflictWarning';
export { DownloadOptions } from './DownloadOptions';
export { ErrorSummary } from './ErrorSummary';

// Controllers
export { TranspilationController, TranspilationEventType } from './controllers/TranspilationController';

// Hooks
export { useTranspilation } from './hooks/useTranspilation';

// State management
export { useWizardState } from './useWizardState';

// Utilities
export {
  discoverCppFiles,
  isCppFile,
  calculateTotalSize,
  formatFileSize
} from './utils/fileDiscovery';
export {
  checkDirectoryPermissions,
  requestWritePermission
} from './utils/checkDirectoryPermissions';
export {
  detectConflicts,
  convertToTargetFileName,
  getConflictingFiles
} from './utils/detectConflicts';
export {
  downloadFile,
  createZipArchive,
  downloadZip,
  calculateTotalBytes,
  formatBytes
} from './utils/downloadHelpers';

// Types
export type {
  WizardState,
  FileInfo,
  TranspileOptions,
  TranspileResult
} from './types';
export type { FileTreeViewProps } from './FileTreeView';
export type { TreeNode } from './utils/buildTreeData';
export type { FileContentDisplayProps } from './FileContentDisplay';
export type { DualPaneViewerProps } from './DualPaneViewer';
export type { TabbedCodeViewerProps } from './TabbedCodeViewer';
export type { SyntaxHighlighterProps } from './SyntaxHighlighter';
export type { PermissionIndicatorProps } from './PermissionIndicator';
export type { ConflictWarningProps } from './ConflictWarning';
export type { DownloadOptionsProps } from './DownloadOptions';
export type { ErrorSummaryProps } from './ErrorSummary';
export type { PermissionStatus } from './utils/checkDirectoryPermissions';
export type { FileConflict, ConflictDetectionResult } from './utils/detectConflicts';
export type { TranspilationEvent, TranspilationEventListener } from './controllers/TranspilationController';
