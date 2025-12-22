import { describe, it, expect } from 'vitest';
import { render } from '@testing-library/react';
import { FileTreeView } from './FileTreeView';
import type { FileInfo } from './types';

/**
 * Performance tests for FileTreeView component
 * Tests virtualization and rendering performance with large datasets
 */
describe('FileTreeView Performance', () => {
  const generateLargeFileSet = (count: number, useFolders = false): FileInfo[] => {
    return Array.from({ length: count }, (_, i) => {
      const folderPrefix = useFolders ? `folder-${Math.floor(i / 10)}/` : '';
      return {
        path: `${folderPrefix}file-${i}.cpp`,
        name: `file-${i}.cpp`,
        handle: {} as FileSystemFileHandle,
        size: Math.floor(Math.random() * 10000) + 100,
      };
    });
  };

  const generateNestedStructure = (
    depth: number,
    filesPerLevel: number,
    currentPath = ''
  ): FileInfo[] => {
    const files: FileInfo[] = [];

    if (depth === 0) {
      // Generate files at this level
      for (let i = 0; i < filesPerLevel; i++) {
        files.push({
          path: `${currentPath}/file-${i}.cpp`,
          name: `file-${i}.cpp`,
          handle: {} as FileSystemFileHandle,
          size: 1024,
        });
      }
    } else {
      // Generate folders and recurse
      for (let i = 0; i < 3; i++) {
        const folderPath = currentPath
          ? `${currentPath}/level-${depth}-${i}`
          : `level-${depth}-${i}`;
        files.push(...generateNestedStructure(depth - 1, filesPerLevel, folderPath));
      }
    }

    return files;
  };

  describe('rendering performance', () => {
    it('renders 500 files in <150ms', () => {
      const data = generateLargeFileSet(500);

      const startTime = performance.now();
      render(<FileTreeView files={data} height={600} />);
      const endTime = performance.now();

      const renderTime = endTime - startTime;
      console.log(`500 files rendered in ${renderTime.toFixed(2)}ms`);
      expect(renderTime).toBeLessThan(150);
    });

    it('renders 1000 files in <250ms', () => {
      const data = generateLargeFileSet(1000, true);

      const startTime = performance.now();
      render(<FileTreeView files={data} height={600} />);
      const endTime = performance.now();

      const renderTime = endTime - startTime;
      console.log(`1000 files rendered in ${renderTime.toFixed(2)}ms`);
      expect(renderTime).toBeLessThan(250);
    });

    it('renders 2000 files in <400ms', () => {
      const data = generateLargeFileSet(2000, true);

      const startTime = performance.now();
      render(<FileTreeView files={data} height={600} />);
      const endTime = performance.now();

      const renderTime = endTime - startTime;
      console.log(`2000 files rendered in ${renderTime.toFixed(2)}ms`);
      expect(renderTime).toBeLessThan(400);
    });

    it('renders 5000 files in <800ms', () => {
      const data = generateLargeFileSet(5000, true);

      const startTime = performance.now();
      render(<FileTreeView files={data} height={600} />);
      const endTime = performance.now();

      const renderTime = endTime - startTime;
      console.log(`5000 files rendered in ${renderTime.toFixed(2)}ms`);
      expect(renderTime).toBeLessThan(800);
    });
  });

  describe('nested structure performance', () => {
    it('handles 3 levels of nesting efficiently', () => {
      const data = generateNestedStructure(3, 10);

      const startTime = performance.now();
      render(<FileTreeView files={data} height={600} />);
      const endTime = performance.now();

      const renderTime = endTime - startTime;
      console.log(`3-level nested structure (${data.length} files) rendered in ${renderTime.toFixed(2)}ms`);
      expect(renderTime).toBeLessThan(200);
    });

    it('handles 5 levels of nesting efficiently', () => {
      const data = generateNestedStructure(5, 5);

      const startTime = performance.now();
      render(<FileTreeView files={data} height={600} />);
      const endTime = performance.now();

      const renderTime = endTime - startTime;
      console.log(`5-level nested structure (${data.length} files) rendered in ${renderTime.toFixed(2)}ms`);
      expect(renderTime).toBeLessThan(300);
    });

    it('handles 7 levels of nesting efficiently', () => {
      const data = generateNestedStructure(7, 3);

      const startTime = performance.now();
      render(<FileTreeView files={data} height={600} />);
      const endTime = performance.now();

      const renderTime = endTime - startTime;
      console.log(`7-level nested structure (${data.length} files) rendered in ${renderTime.toFixed(2)}ms`);
      expect(renderTime).toBeLessThan(400);
    });
  });

  describe('virtualization efficiency', () => {
    it('virtualizes large flat list efficiently', () => {
      const data = generateLargeFileSet(2000);

      const { container } = render(<FileTreeView files={data} height={600} />);

      // react-arborist uses virtualization internally
      // We can verify the component renders without hanging
      const treeView = container.querySelector('.file-tree-view');
      expect(treeView).toBeInTheDocument();

      // Tree should render quickly despite large dataset
      const treeNodes = container.querySelectorAll('.tree-node');
      // Due to virtualization, only visible nodes are rendered
      // Typically much less than total file count
      console.log(`Rendered ${treeNodes.length} visible nodes out of 2000 total files`);
    });

    it('maintains responsiveness with nested structure', () => {
      const data = generateNestedStructure(5, 10);

      const startTime = performance.now();
      const { container, rerender } = render(<FileTreeView files={data} height={600} />);
      const initialRenderTime = performance.now() - startTime;

      // Re-render with same data
      const rerenderStartTime = performance.now();
      rerender(<FileTreeView files={data} height={600} />);
      const rerenderTime = performance.now() - rerenderStartTime;

      console.log(`Initial render: ${initialRenderTime.toFixed(2)}ms, Re-render: ${rerenderTime.toFixed(2)}ms`);

      // Re-renders should be faster than initial render
      expect(rerenderTime).toBeLessThan(initialRenderTime);
      expect(rerenderTime).toBeLessThan(100);
    });
  });

  describe('height variations', () => {
    it('handles small viewport efficiently', () => {
      const data = generateLargeFileSet(1000, true);

      const startTime = performance.now();
      render(<FileTreeView files={data} height={300} />);
      const endTime = performance.now();

      const renderTime = endTime - startTime;
      console.log(`1000 files with 300px height rendered in ${renderTime.toFixed(2)}ms`);
      expect(renderTime).toBeLessThan(200);
    });

    it('handles large viewport efficiently', () => {
      const data = generateLargeFileSet(1000, true);

      const startTime = performance.now();
      render(<FileTreeView files={data} height={1000} />);
      const endTime = performance.now();

      const renderTime = endTime - startTime;
      console.log(`1000 files with 1000px height rendered in ${renderTime.toFixed(2)}ms`);
      expect(renderTime).toBeLessThan(300);
    });
  });

  describe('real-world scenarios', () => {
    it('handles typical C++ project (200 files, moderate nesting)', () => {
      // Simulate a typical C++ project structure
      const files: FileInfo[] = [
        ...generateNestedStructure(3, 10, 'src'),
        ...generateNestedStructure(2, 15, 'include'),
        ...generateNestedStructure(2, 10, 'tests'),
        ...Array.from({ length: 20 }, (_, i) => ({
          path: `lib/external-${i}.cpp`,
          name: `external-${i}.cpp`,
          handle: {} as FileSystemFileHandle,
          size: 5000,
        })),
      ];

      const startTime = performance.now();
      render(<FileTreeView files={files} height={600} />);
      const endTime = performance.now();

      const renderTime = endTime - startTime;
      console.log(`Typical C++ project (${files.length} files) rendered in ${renderTime.toFixed(2)}ms`);
      expect(renderTime).toBeLessThan(250);
    });

    it('handles large monorepo (1500 files, deep nesting)', () => {
      // Simulate a large monorepo
      const files: FileInfo[] = [
        ...generateNestedStructure(4, 8, 'packages/core'),
        ...generateNestedStructure(4, 8, 'packages/utils'),
        ...generateNestedStructure(3, 10, 'packages/ui'),
        ...generateNestedStructure(3, 10, 'apps/backend'),
        ...generateNestedStructure(3, 10, 'apps/frontend'),
      ];

      const startTime = performance.now();
      render(<FileTreeView files={files} height={600} />);
      const endTime = performance.now();

      const renderTime = endTime - startTime;
      console.log(`Large monorepo (${files.length} files) rendered in ${renderTime.toFixed(2)}ms`);
      expect(renderTime).toBeLessThan(500);
    });
  });

  describe('memory efficiency', () => {
    it('does not create excessive DOM nodes with large dataset', () => {
      const data = generateLargeFileSet(3000, true);

      const { container } = render(<FileTreeView files={data} height={600} />);

      // Count actual rendered DOM nodes
      const treeNodes = container.querySelectorAll('.tree-node');

      // With virtualization, only visible nodes should be rendered
      // For 600px height with ~32px row height, expect ~20-30 visible nodes + overscan
      console.log(`DOM nodes rendered: ${treeNodes.length} out of ~3000+ potential nodes`);
      expect(treeNodes.length).toBeLessThan(100);
    });

    it('maintains low memory footprint during re-renders', () => {
      const data = generateLargeFileSet(1000, true);

      const { container, rerender } = render(<FileTreeView files={data} height={600} />);

      const initialNodeCount = container.querySelectorAll('.tree-node').length;

      // Re-render multiple times
      for (let i = 0; i < 5; i++) {
        rerender(<FileTreeView files={data} height={600} />);
      }

      const finalNodeCount = container.querySelectorAll('.tree-node').length;

      // Node count should remain consistent (no memory leaks)
      console.log(`Initial nodes: ${initialNodeCount}, Final nodes: ${finalNodeCount}`);
      expect(Math.abs(finalNodeCount - initialNodeCount)).toBeLessThan(10);
    });
  });

  describe('stress tests', () => {
    it('handles extreme file count (10000 files)', () => {
      const data = generateLargeFileSet(10000, true);

      const startTime = performance.now();
      render(<FileTreeView files={data} height={600} />);
      const endTime = performance.now();

      const renderTime = endTime - startTime;
      console.log(`10000 files rendered in ${renderTime.toFixed(2)}ms`);
      // Allow more time for extreme dataset, but should still complete
      expect(renderTime).toBeLessThan(2000);
    });

    it('handles very deep nesting (10 levels)', () => {
      const data = generateNestedStructure(10, 2);

      const startTime = performance.now();
      render(<FileTreeView files={data} height={600} />);
      const endTime = performance.now();

      const renderTime = endTime - startTime;
      console.log(`10-level nested structure (${data.length} files) rendered in ${renderTime.toFixed(2)}ms`);
      expect(renderTime).toBeLessThan(800);
    });
  });
});
