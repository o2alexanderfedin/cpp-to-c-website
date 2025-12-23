/**
 * ITranspiler Interface Contract Tests
 * TDD Phase: RED - Write failing tests first
 */

import { describe, it, expect, beforeEach } from 'vitest';
import type { ITranspiler } from './ITranspiler';
import { MockTranspiler } from '../../adapters/MockTranspiler';

describe('ITranspiler', () => {
  describe('contract', () => {
    let transpiler: ITranspiler;

    beforeEach(() => {
      transpiler = new MockTranspiler();
    });

    it('should have transpile method', () => {
      expect(typeof transpiler.transpile).toBe('function');
    });

    it('should have validateInput method', () => {
      expect(typeof transpiler.validateInput).toBe('function');
    });
  });

  describe('behavior', () => {
    let transpiler: ITranspiler;

    beforeEach(() => {
      transpiler = new MockTranspiler();
    });

    it('should transpile simple C++ code successfully', async () => {
      const cppCode = 'int main() { return 0; }';

      const result = await transpiler.transpile(cppCode);

      expect(result.success).toBe(true);
      expect(result.cCode).toBeDefined();
      expect(result.cCode).toBeTruthy();
      expect(result.error).toBeUndefined();
    });

    it('should return error for invalid C++ code', async () => {
      const invalidCode = 'this is not valid C++';

      const result = await transpiler.transpile(invalidCode);

      expect(result.success).toBe(false);
      expect(result.error).toBeDefined();
      expect(result.error).toBeTruthy();
      expect(result.cCode).toBeUndefined();
    });

    it('should accept transpile options', async () => {
      const cppCode = 'int main() { return 0; }';

      const result = await transpiler.transpile(cppCode, {
        sourcePath: '/test/main.cpp',
        includeACSL: false,
        targetStandard: 'c99',
      });

      expect(result.success).toBe(true);
      expect(result.sourcePath).toBe('/test/main.cpp');
    });

    it('should include diagnostics in result', async () => {
      const cppCode = 'int main() { int unused; return 0; }';

      const result = await transpiler.transpile(cppCode);

      expect(result.diagnostics).toBeDefined();
      expect(Array.isArray(result.diagnostics)).toBe(true);
    });

    it('should validate valid C++ input', async () => {
      const validCode = 'int main() { return 0; }';

      const result = await transpiler.validateInput(validCode);

      expect(result.valid).toBe(true);
      expect(result.errors).toBeUndefined();
    });

    it('should validate invalid C++ input', async () => {
      const invalidCode = 'this is not valid C++';

      const result = await transpiler.validateInput(invalidCode);

      expect(result.valid).toBe(false);
      expect(result.errors).toBeDefined();
      expect(result.errors!.length).toBeGreaterThan(0);
    });

    it('should include warnings in validation result', async () => {
      const codeWithWarning = 'int main() { int unused; return 0; }';

      const result = await transpiler.validateInput(codeWithWarning);

      expect(result.valid).toBe(true);
      expect(result.warnings).toBeDefined();
    });

    it('should handle empty input', async () => {
      const result = await transpiler.transpile('');

      expect(result.success).toBe(false);
      expect(result.error).toBeDefined();
    });

    it('should transpile code with includes', async () => {
      const cppCode = '#include <iostream>\nint main() { return 0; }';

      const result = await transpiler.transpile(cppCode);

      expect(result.success).toBe(true);
      expect(result.cCode).toBeDefined();
    });

    it('should handle options with defaults', async () => {
      const cppCode = 'int main() { return 0; }';

      const result = await transpiler.transpile(cppCode, {});

      expect(result.success).toBe(true);
    });
  });
});
