import { describe, it, expect } from 'vitest';
import {
  isCppFile,
  calculateTotalSize,
  formatFileSize
} from './fileDiscovery';
import type { FileInfo } from '../types';

describe('fileDiscovery utils', () => {
  describe('isCppFile', () => {
    it('identifies C++ source files', () => {
      expect(isCppFile('main.cpp')).toBe(true);
      expect(isCppFile('utils.cc')).toBe(true);
      expect(isCppFile('helper.cxx')).toBe(true);
    });

    it('identifies C++ header files', () => {
      expect(isCppFile('header.h')).toBe(true);
      expect(isCppFile('class.hpp')).toBe(true);
      expect(isCppFile('interface.hxx')).toBe(true);
    });

    it('rejects non-C++ files', () => {
      expect(isCppFile('readme.md')).toBe(false);
      expect(isCppFile('script.js')).toBe(false);
      expect(isCppFile('style.css')).toBe(false);
      expect(isCppFile('data.json')).toBe(false);
    });

    it('is case-insensitive', () => {
      expect(isCppFile('Main.CPP')).toBe(true);
      expect(isCppFile('Header.HPP')).toBe(true);
      expect(isCppFile('UTILS.CC')).toBe(true);
    });

    it('requires exact extension match', () => {
      expect(isCppFile('test.cpp.bak')).toBe(false);
      expect(isCppFile('notcpp')).toBe(false);
      expect(isCppFile('.cpp')).toBe(true); // edge case
    });
  });

  describe('calculateTotalSize', () => {
    it('sums file sizes correctly', () => {
      const files: FileInfo[] = [
        { path: 'a.cpp', name: 'a.cpp', handle: {} as any, size: 100 },
        { path: 'b.cpp', name: 'b.cpp', handle: {} as any, size: 200 },
        { path: 'c.h', name: 'c.h', handle: {} as any, size: 50 }
      ];

      expect(calculateTotalSize(files)).toBe(350);
    });

    it('returns 0 for empty array', () => {
      expect(calculateTotalSize([])).toBe(0);
    });

    it('handles single file', () => {
      const files: FileInfo[] = [
        { path: 'test.cpp', name: 'test.cpp', handle: {} as any, size: 1024 }
      ];

      expect(calculateTotalSize(files)).toBe(1024);
    });
  });

  describe('formatFileSize', () => {
    it('formats bytes correctly', () => {
      expect(formatFileSize(0)).toBe('0 Bytes');
      expect(formatFileSize(100)).toBe('100 Bytes');
      expect(formatFileSize(999)).toBe('999 Bytes');
    });

    it('formats kilobytes correctly', () => {
      expect(formatFileSize(1024)).toBe('1 KB');
      expect(formatFileSize(1536)).toBe('1.5 KB');
      expect(formatFileSize(10240)).toBe('10 KB');
    });

    it('formats megabytes correctly', () => {
      expect(formatFileSize(1048576)).toBe('1 MB');
      expect(formatFileSize(1572864)).toBe('1.5 MB');
      expect(formatFileSize(10485760)).toBe('10 MB');
    });

    it('formats gigabytes correctly', () => {
      expect(formatFileSize(1073741824)).toBe('1 GB');
      expect(formatFileSize(1610612736)).toBe('1.5 GB');
    });
  });
});
