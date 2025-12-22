/**
 * MockTranspiler Implementation Tests
 * Tests for the mock transpiler adapter beyond interface contracts
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { MockTranspiler } from './MockTranspiler';

describe('MockTranspiler', () => {
  let transpiler: MockTranspiler;

  beforeEach(() => {
    transpiler = new MockTranspiler();
  });

  describe('C++ to C conversion', () => {
    it('should replace iostream with stdio.h', async () => {
      const cppCode = '#include <iostream>\nint main() { return 0; }';

      const result = await transpiler.transpile(cppCode);

      expect(result.success).toBe(true);
      expect(result.cCode).toContain('#include <stdio.h>');
      expect(result.cCode).not.toContain('iostream');
    });

    it('should add mock transpilation header', async () => {
      const cppCode = 'int main() { return 0; }';

      const result = await transpiler.transpile(cppCode);

      expect(result.success).toBe(true);
      expect(result.cCode).toContain('/* Transpiled from C++ to C (Mock) */');
    });

    it('should include ACSL annotations by default', async () => {
      const cppCode = 'int main() { return 0; }';

      const result = await transpiler.transpile(cppCode);

      expect(result.success).toBe(true);
      expect(result.cCode).toContain('/*@ ensures');
    });

    it('should exclude ACSL annotations when disabled', async () => {
      const cppCode = 'int main() { return 0; }';

      const result = await transpiler.transpile(cppCode, {
        includeACSL: false,
      });

      expect(result.success).toBe(true);
      expect(result.cCode).not.toContain('/*@ ensures');
    });

    it('should include target standard comment', async () => {
      const cppCode = 'int main() { return 0; }';

      const result = await transpiler.transpile(cppCode, {
        targetStandard: 'c11',
      });

      expect(result.success).toBe(true);
      expect(result.cCode).toContain('/* Target: c11 */');
    });
  });

  describe('validation', () => {
    it('should detect invalid C++ syntax', async () => {
      const result = await transpiler.validateInput('this is not valid C++');

      expect(result.valid).toBe(false);
      expect(result.errors).toBeDefined();
      expect(result.errors![0]).toContain('Syntax error');
    });

    it('should warn about unused variables', async () => {
      const result = await transpiler.validateInput('int main() { int unused; return 0; }');

      expect(result.valid).toBe(true);
      expect(result.warnings).toBeDefined();
      expect(result.warnings![0]).toContain('Unused variable');
    });

    it('should validate correct code', async () => {
      const result = await transpiler.validateInput('int main() { return 0; }');

      expect(result.valid).toBe(true);
      expect(result.errors).toBeUndefined();
    });
  });

  describe('error handling', () => {
    it('should return error for empty source', async () => {
      const result = await transpiler.transpile('');

      expect(result.success).toBe(false);
      expect(result.error).toBe('Empty source code');
    });

    it('should return error for whitespace-only source', async () => {
      const result = await transpiler.transpile('   \n  \t  ');

      expect(result.success).toBe(false);
      expect(result.error).toBe('Empty source code');
    });

    it('should propagate validation errors to transpile result', async () => {
      const invalidCode = 'this is not valid C++';

      const result = await transpiler.transpile(invalidCode);

      expect(result.success).toBe(false);
      expect(result.error).toContain('Syntax error');
      expect(result.diagnostics).toBeDefined();
    });
  });

  describe('options handling', () => {
    it('should preserve source path in result', async () => {
      const result = await transpiler.transpile('int main() { return 0; }', {
        sourcePath: '/path/to/source.cpp',
      });

      expect(result.sourcePath).toBe('/path/to/source.cpp');
    });

    it('should preserve source path in error result', async () => {
      const result = await transpiler.transpile('', {
        sourcePath: '/path/to/empty.cpp',
      });

      expect(result.success).toBe(false);
      expect(result.sourcePath).toBe('/path/to/empty.cpp');
    });

    it('should handle missing options', async () => {
      const result = await transpiler.transpile('int main() { return 0; }');

      expect(result.success).toBe(true);
      expect(result.cCode).toBeDefined();
    });
  });

  describe('test helpers', () => {
    it('should allow custom transpilation behavior', async () => {
      transpiler.setCustomBehavior(async (source) => ({
        success: true,
        cCode: `custom output for: ${source}`,
      }));

      const result = await transpiler.transpile('test');

      expect(result.success).toBe(true);
      expect(result.cCode).toBe('custom output for: test');
    });

    it('should allow custom validation behavior', async () => {
      transpiler.setCustomValidation(async () => ({
        valid: false,
        errors: ['Custom error'],
      }));

      const result = await transpiler.validateInput('any code');

      expect(result.valid).toBe(false);
      expect(result.errors).toEqual(['Custom error']);
    });
  });
});
