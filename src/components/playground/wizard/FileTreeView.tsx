import React from 'react';
import { Tree, type NodeRendererProps } from 'react-arborist';
import type { FileInfo } from './types';
import type { TreeNode } from './utils/buildTreeData';
import { buildTreeData } from './utils/buildTreeData';

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
 */
export interface FileTreeViewProps {
  files: FileInfo[];
  selectedFile?: string; // Path of highlighted file (for Step 3 & 4)
  onFileSelect?: (file: FileInfo) => void; // Click handler (for Step 4)
  height?: number; // Tree height in pixels (default: 400)
  showRoot?: boolean; // Show root node (default: false)
}

export const FileTreeView: React.FC<FileTreeViewProps> = ({
  files,
  selectedFile,
  onFileSelect,
  height = 400,
  showRoot = false,
}) => {
  // Build tree data from flat file list
  const treeData = React.useMemo(() => {
    const root = buildTreeData(files);
    return showRoot ? [root] : root.children || [];
  }, [files, showRoot]);

  // Node renderer component
  const Node = ({ node, style, dragHandle }: NodeRendererProps<TreeNode>) => {
    const isSelected = !node.data.isFolder && node.data.fileInfo?.path === selectedFile;

    return (
      <div
        style={style}
        ref={dragHandle}
        className={`tree-node ${isSelected ? 'selected' : ''}`}
        onClick={() => {
          if (!node.data.isFolder && onFileSelect && node.data.fileInfo) {
            onFileSelect(node.data.fileInfo);
          }
        }}
      >
        {/* Folder/file icon */}
        <span className="tree-icon">
          {node.data.isFolder ? (node.isOpen ? '📂' : '📁') : '📄'}
        </span>

        {/* Node name */}
        <span className="tree-name">{node.data.name}</span>
      </div>
    );
  };

  return (
    <div className="file-tree-view">
      <Tree
        data={treeData}
        openByDefault={false}
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

        .tree-icon {
          margin-right: 0.5rem;
          font-size: 1.25rem;
          flex-shrink: 0;
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
      `}</style>
    </div>
  );
};
