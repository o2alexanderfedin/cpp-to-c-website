import React, { useEffect, useRef } from 'react';
import { Tree, type NodeRendererProps } from 'react-arborist';
import type { FileInfo } from './types';
import type { TreeNode } from './utils/buildTreeData';
import { buildTreeData } from './utils/buildTreeData';

/**
 * File status for visual indication
 */
export enum FileStatus {
  PENDING = 'pending',
  IN_PROGRESS = 'in_progress',
  SUCCESS = 'success',
  ERROR = 'error'
}

/**
 * FileTreeView - Virtualized tree component for displaying directory structures
 *
 * @example Basic usage
 * ```tsx
 * <FileTreeView files={sourceFiles} />
 * ```
 *
 * @example With selection and click handler
 * ```tsx
 * <FileTreeView
 *   files={sourceFiles}
 *   selectedFile={currentFilePath}
 *   onFileSelect={(file) => previewFile(file)}
 *   height={500}
 * />
 * ```
 *
 * @example With status tracking
 * ```tsx
 * <FileTreeView
 *   files={sourceFiles}
 *   selectedFile={currentFile}
 *   fileStatuses={fileStatusMap}
 *   autoScroll={true}
 * />
 * ```
 */
export interface FileTreeViewProps {
  files: FileInfo[];
  selectedFile?: string; // Path of highlighted file (for Step 3 & 4)
  fileStatuses?: Map<string, FileStatus>; // Status for each file path
  onFileSelect?: (file: FileInfo) => void; // Click handler (for Step 4)
  height?: number; // Tree height in pixels (default: 400)
  showRoot?: boolean; // Show root node (default: false)
  autoScroll?: boolean; // Auto-scroll to selected file (default: false)
}

export const FileTreeView: React.FC<FileTreeViewProps> = ({
  files,
  selectedFile,
  fileStatuses = new Map(),
  onFileSelect,
  height = 400,
  showRoot = false,
  autoScroll = false
}) => {
  const treeRef = useRef<any>(null);

  // Build tree data from flat file list
  const treeData = React.useMemo(() => {
    const root = buildTreeData(files);
    return showRoot ? [root] : root.children || [];
  }, [files, showRoot, fileStatuses]);

  // Auto-scroll to selected file
  useEffect(() => {
    if (autoScroll && selectedFile && treeRef.current) {
      // Find the node for the selected file
      // react-arborist provides scrollTo functionality via the Tree ref
      const tree = treeRef.current;
      if (tree && tree.scrollTo) {
        tree.scrollTo(selectedFile);
      }
    }
  }, [selectedFile, autoScroll]);

  // Get status icon for file
  const getStatusIcon = (filePath: string): string => {
    const status = fileStatuses.get(filePath);
    switch (status) {
      case FileStatus.PENDING:
        return '⏳';
      case FileStatus.IN_PROGRESS:
        return '🔄';
      case FileStatus.SUCCESS:
        return '✓';
      case FileStatus.ERROR:
        return '✗';
      default:
        return '📄';
    }
  };

  // Get status class for styling
  const getStatusClass = (filePath: string): string => {
    const status = fileStatuses.get(filePath);
    return status ? `status-${status}` : '';
  };

  // Node renderer component
  const Node = ({ node, style, dragHandle }: NodeRendererProps<TreeNode>) => {
    const isSelected = !node.data.isFolder && node.data.fileInfo?.path === selectedFile;
    const filePath = node.data.fileInfo?.path || '';
    const statusClass = getStatusClass(filePath);

    return (
      <div
        style={style}
        ref={dragHandle}
        className={`tree-node ${isSelected ? 'selected' : ''} ${statusClass}`}
        onClick={() => {
          if (!node.data.isFolder && onFileSelect && node.data.fileInfo) {
            onFileSelect(node.data.fileInfo);
          }
        }}
      >
        {/* Folder/file icon with status */}
        <span className="tree-icon">
          {node.data.isFolder
            ? (node.isOpen ? '📂' : '📁')
            : getStatusIcon(filePath)
          }
        </span>

        {/* Node name */}
        <span className="tree-name">{node.data.name}</span>
      </div>
    );
  };

  return (
    <div className="file-tree-view">
      <Tree
        ref={treeRef}
        data={treeData}
        openByDefault={true}
        width="100%"
        height={height}
        indent={24}
        rowHeight={32}
        overscanCount={10}
      >
        {Node}
      </Tree>

      <style>{`
        .file-tree-view {
          border: 1px solid #ddd;
          border-radius: 4px;
          background-color: #fff;
          overflow: hidden;
        }

        .tree-node {
          display: flex;
          align-items: center;
          padding: 0.25rem 0.5rem;
          cursor: pointer;
          user-select: none;
          transition: background-color 0.15s;
        }

        .tree-node:hover {
          background-color: #f5f5f5;
        }

        .tree-node.selected {
          background-color: #e3f2fd;
          border-left: 3px solid #4A90E2;
        }

        /* Status-specific styling */
        .tree-node.status-pending {
          opacity: 0.6;
        }

        .tree-node.status-in_progress {
          background-color: #fff3cd;
          border-left: 3px solid #ffc107;
          font-weight: 500;
        }

        .tree-node.status-success {
          opacity: 0.8;
        }

        .tree-node.status-success .tree-icon {
          color: #28a745;
          font-weight: bold;
        }

        .tree-node.status-error {
          background-color: #f8d7da;
          border-left: 3px solid #dc3545;
        }

        .tree-node.status-error .tree-icon {
          color: #dc3545;
          font-weight: bold;
        }

        .tree-icon {
          margin-right: 0.5rem;
          font-size: 1.25rem;
          flex-shrink: 0;
          transition: all 0.15s;
        }

        .tree-name {
          font-size: 0.9rem;
          color: #333;
          overflow: hidden;
          text-overflow: ellipsis;
          white-space: nowrap;
        }

        .tree-node.selected .tree-name {
          font-weight: 600;
          color: #1976d2;
        }

        /* Animation for status changes */
        @keyframes pulse {
          0%, 100% {
            opacity: 1;
          }
          50% {
            opacity: 0.5;
          }
        }

        .tree-node.status-in_progress .tree-icon {
          animation: pulse 1.5s ease-in-out infinite;
        }
      `}</style>
    </div>
  );
};
