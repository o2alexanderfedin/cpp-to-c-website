import { describe, it, expect } from 'vitest';
import { buildTreeData, type TreeNode } from './buildTreeData';
import type { FileInfo } from '../types';

describe('buildTreeData', () => {
  const createMockFileInfo = (path: string, name: string): FileInfo => ({
    path,
    name,
    handle: {} as FileSystemFileHandle,
    size: 1024,
  });

  it('creates nested structure from flat file list', () => {
    const files: FileInfo[] = [
      createMockFileInfo('src/main.cpp', 'main.cpp'),
      createMockFileInfo('src/utils/helper.cpp', 'helper.cpp'),
      createMockFileInfo('include/common.h', 'common.h'),
    ];

    const result = buildTreeData(files);

    expect(result.id).toBe('root');
    expect(result.name).toBe('Source Files');
    expect(result.isFolder).toBe(true);
    expect(result.children).toHaveLength(2);

    // Check that we have 'include' and 'src' folders
    const folderNames = result.children!.map(child => child.name).sort();
    expect(folderNames).toEqual(['include', 'src']);

    // Check 'src' folder
    const srcFolder = result.children!.find(child => child.name === 'src');
    expect(srcFolder?.isFolder).toBe(true);
    expect(srcFolder?.children).toHaveLength(2); // main.cpp and utils folder

    // Check 'src/utils' folder
    const utilsFolder = srcFolder?.children!.find(child => child.name === 'utils');
    expect(utilsFolder?.isFolder).toBe(true);
    expect(utilsFolder?.children).toHaveLength(1);
    expect(utilsFolder?.children![0].name).toBe('helper.cpp');
    expect(utilsFolder?.children![0].isFolder).toBe(false);

    // Check 'include' folder
    const includeFolder = result.children!.find(child => child.name === 'include');
    expect(includeFolder?.isFolder).toBe(true);
    expect(includeFolder?.children).toHaveLength(1);
    expect(includeFolder?.children![0].name).toBe('common.h');
  });

  it('handles files in root directory', () => {
    const files: FileInfo[] = [
      createMockFileInfo('main.cpp', 'main.cpp'),
      createMockFileInfo('config.h', 'config.h'),
    ];

    const result = buildTreeData(files);

    expect(result.children).toHaveLength(2);
    expect(result.children![0].name).toBe('config.h');
    expect(result.children![0].isFolder).toBe(false);
    expect(result.children![1].name).toBe('main.cpp');
    expect(result.children![1].isFolder).toBe(false);
  });

  it('sorts folders before files', () => {
    const files: FileInfo[] = [
      createMockFileInfo('zzz.cpp', 'zzz.cpp'),
      createMockFileInfo('aaa/file.cpp', 'file.cpp'),
      createMockFileInfo('main.cpp', 'main.cpp'),
      createMockFileInfo('bbb/file.h', 'file.h'),
    ];

    const result = buildTreeData(files);

    expect(result.children).toHaveLength(4);

    // First two should be folders (aaa, bbb), next two should be files (main.cpp, zzz.cpp)
    expect(result.children![0].isFolder).toBe(true);
    expect(result.children![0].name).toBe('aaa');
    expect(result.children![1].isFolder).toBe(true);
    expect(result.children![1].name).toBe('bbb');
    expect(result.children![2].isFolder).toBe(false);
    expect(result.children![2].name).toBe('main.cpp');
    expect(result.children![3].isFolder).toBe(false);
    expect(result.children![3].name).toBe('zzz.cpp');
  });

  it('handles empty input', () => {
    const result = buildTreeData([]);

    expect(result.id).toBe('root');
    expect(result.name).toBe('Source Files');
    expect(result.isFolder).toBe(true);
    expect(result.children).toEqual([]);
  });

  it('assigns unique IDs based on full path', () => {
    const files: FileInfo[] = [
      createMockFileInfo('src/main.cpp', 'main.cpp'),
      createMockFileInfo('src/utils/helper.cpp', 'helper.cpp'),
    ];

    const result = buildTreeData(files);

    const srcFolder = result.children!.find(child => child.name === 'src');
    expect(srcFolder?.id).toBe('src');

    const utilsFolder = srcFolder?.children!.find(child => child.name === 'utils');
    expect(utilsFolder?.id).toBe('src/utils');

    const helperFile = utilsFolder?.children![0];
    expect(helperFile?.id).toBe('src/utils/helper.cpp');
  });

  it('preserves fileInfo on leaf nodes', () => {
    const files: FileInfo[] = [
      createMockFileInfo('src/main.cpp', 'main.cpp'),
    ];

    const result = buildTreeData(files);
    const srcFolder = result.children![0];
    const mainFile = srcFolder.children![0];

    expect(mainFile.fileInfo).toBeDefined();
    expect(mainFile.fileInfo?.path).toBe('src/main.cpp');
    expect(mainFile.fileInfo?.name).toBe('main.cpp');
    expect(mainFile.fileInfo?.size).toBe(1024);
  });

  it('does not add fileInfo to folder nodes', () => {
    const files: FileInfo[] = [
      createMockFileInfo('src/main.cpp', 'main.cpp'),
    ];

    const result = buildTreeData(files);
    const srcFolder = result.children![0];

    expect(srcFolder.isFolder).toBe(true);
    expect(srcFolder.fileInfo).toBeUndefined();
  });

  it('handles deeply nested paths', () => {
    const files: FileInfo[] = [
      createMockFileInfo('a/b/c/d/e/file.cpp', 'file.cpp'),
    ];

    const result = buildTreeData(files);

    let current = result;
    const expectedPath = ['a', 'b', 'c', 'd', 'e'];

    for (const folder of expectedPath) {
      expect(current.children).toHaveLength(1);
      current = current.children![0];
      expect(current.name).toBe(folder);
      expect(current.isFolder).toBe(true);
    }

    // Final level should have the file
    expect(current.children).toHaveLength(1);
    expect(current.children![0].name).toBe('file.cpp');
    expect(current.children![0].isFolder).toBe(false);
  });

  it('handles special characters in file names', () => {
    const files: FileInfo[] = [
      createMockFileInfo('src/file-name.cpp', 'file-name.cpp'),
      createMockFileInfo('src/file_name.h', 'file_name.h'),
      createMockFileInfo('src/file.name.hpp', 'file.name.hpp'),
    ];

    const result = buildTreeData(files);

    const srcFolder = result.children![0];
    expect(srcFolder.children).toHaveLength(3);

    const fileNames = srcFolder.children!.map(child => child.name).sort();
    expect(fileNames).toEqual(['file-name.cpp', 'file.name.hpp', 'file_name.h']);
  });

  it('maintains consistent order with multiple calls', () => {
    const files: FileInfo[] = [
      createMockFileInfo('src/b.cpp', 'b.cpp'),
      createMockFileInfo('src/a.cpp', 'a.cpp'),
      createMockFileInfo('src/c.cpp', 'c.cpp'),
    ];

    const result1 = buildTreeData(files);
    const result2 = buildTreeData(files);

    const getChildNames = (node: TreeNode) =>
      node.children?.map(child => child.name) || [];

    expect(getChildNames(result1.children![0])).toEqual(getChildNames(result2.children![0]));
  });
});
