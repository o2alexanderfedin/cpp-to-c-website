import type { FileInfo } from '../types';

/**
 * Tree node structure for react-arborist
 */
export interface TreeNode {
  id: string;
  name: string;
  children?: TreeNode[];
  isFolder: boolean;
  fileInfo?: FileInfo; // Leaf nodes only
}

/**
 * Build tree structure from flat file list
 * @param files - Flat list of FileInfo objects
 * @returns Root tree node with nested children
 */
export function buildTreeData(files: FileInfo[]): TreeNode {
  // Create root node
  const root: TreeNode = {
    id: 'root',
    name: 'Source Files',
    isFolder: true,
    children: [],
  };

  if (files.length === 0) {
    return root;
  }

  // Sort files by path for consistent tree order
  const sortedFiles = [...files].sort((a, b) => a.path.localeCompare(b.path));

  // Map of path -> node for efficient lookups
  const pathToNode = new Map<string, TreeNode>();
  pathToNode.set('root', root);

  // Build tree by splitting paths and creating nested structure
  for (const file of sortedFiles) {
    const pathParts = file.path.split('/');
    let currentPath = 'root';
    let currentNode = root;

    // Process each part of the path
    for (let i = 0; i < pathParts.length; i++) {
      const part = pathParts[i];
      const isLastPart = i === pathParts.length - 1;
      const nextPath = currentPath === 'root' ? part : `${currentPath}/${part}`;

      if (isLastPart) {
        // This is a file (leaf node)
        const fileNode: TreeNode = {
          id: nextPath,
          name: part,
          isFolder: false,
          fileInfo: file,
        };
        currentNode.children = currentNode.children || [];
        currentNode.children.push(fileNode);
        pathToNode.set(nextPath, fileNode);
      } else {
        // This is a folder (intermediate node)
        let folderNode = pathToNode.get(nextPath);
        if (!folderNode) {
          folderNode = {
            id: nextPath,
            name: part,
            isFolder: true,
            children: [],
          };
          currentNode.children = currentNode.children || [];
          currentNode.children.push(folderNode);
          pathToNode.set(nextPath, folderNode);
        }
        currentNode = folderNode;
        currentPath = nextPath;
      }
    }
  }

  // Sort children: folders first, then files, both alphabetically
  sortChildren(root);

  return root;
}

/**
 * Recursively sort children (folders before files, alphabetically)
 */
function sortChildren(node: TreeNode): void {
  if (!node.children || node.children.length === 0) {
    return;
  }

  node.children.sort((a, b) => {
    // Folders come before files
    if (a.isFolder && !b.isFolder) return -1;
    if (!a.isFolder && b.isFolder) return 1;

    // Both are folders or both are files - sort alphabetically
    return a.name.localeCompare(b.name);
  });

  // Recursively sort children of folders
  for (const child of node.children) {
    if (child.isFolder) {
      sortChildren(child);
    }
  }
}
