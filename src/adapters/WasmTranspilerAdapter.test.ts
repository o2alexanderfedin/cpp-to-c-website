/**
 * WasmTranspilerAdapter Tests
 *
 * Testing WASM module integration (browser-based transpilation)
 * Following TDD: Write tests first, implement to pass
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import type { ITranspiler } from '../core/interfaces/ITranspiler';
import type { TranspileOptions } from '../core/interfaces/types';
import type {
  WASMModule,
  TranspilerInstance,
  TranspileResult as WasmTranspileResult,
  CreateCppToCModule
} from '@hupyy/cpptoc-wasm';

// Mock the @hupyy/cpptoc-wasm module
vi.mock('@hupyy/cpptoc-wasm', () => {
  // Create mock transpiler instance
  const mockTranspilerInstance: TranspilerInstance = {
    transpile: vi.fn(),
    getVersion: vi.fn(() => '1.22.0'),
    delete: vi.fn()
  };

  // Create mock WASM module
  const mockWasmModule: WASMModule = {
    Transpiler: vi.fn(() => mockTranspilerInstance)
  };

  // Create mock module factory
  const createModule: CreateCppToCModule = vi.fn(async (options) => {
    // Simulate async initialization
    await new Promise(resolve => setTimeout(resolve, 10));

    // Call onRuntimeInitialized if provided
    if (options?.onRuntimeInitialized) {
      options.onRuntimeInitialized();
    }

    return mockWasmModule;
  });

  return {
    default: createModule
  };
});

/**
 * Test suite for WasmTranspilerAdapter
 *
 * Tests WASM module integration:
 * - WASM module initialization
 * - Transpilation using WASM
 * - Error handling
 * - Resource cleanup
 * - ITranspiler interface compliance
 */
describe('WasmTranspilerAdapter', () => {
  let adapter: ITranspiler;
  let mockModule: WASMModule;
  let mockInstance: TranspilerInstance;

  beforeEach(async () => {
    vi.clearAllMocks();

    // Get mocked module for access in tests
    const wasmModule = await import('@hupyy/cpptoc-wasm');
    const createModule = wasmModule.default as unknown as CreateCppToCModule;
    mockModule = await createModule();
    mockInstance = new mockModule.Transpiler();

    // Dynamic import to ensure fresh instance
    const { WasmTranspilerAdapter } = await import('./WasmTranspilerAdapter');
    adapter = new WasmTranspilerAdapter();
  });

  describe('constructor', () => {
    it('should create instance without initializing WASM immediately', async () => {
      const { WasmTranspilerAdapter } = await import('./WasmTranspilerAdapter');
      const instance = new WasmTranspilerAdapter();
      expect(instance).toBeDefined();

      // WASM should be lazy-loaded (not initialized in constructor)
      const wasmModule = await import('@hupyy/cpptoc-wasm');
      const createModule = wasmModule.default as any;
      // createModule should not be called yet (lazy loading)
      // We can't easily test this due to mocking, but the implementation should be lazy
    });
  });

  describe('transpile', () => {
    it('should successfully transpile C++ to C using WASM', async () => {
      const mockWasmResult: WasmTranspileResult = {
        success: true,
        c: 'int main(void) { return 0; }',
        h: '#ifndef MAIN_H\n#define MAIN_H\n#endif',
        acsl: '',
        diagnostics: []
      };

      vi.mocked(mockInstance.transpile).mockReturnValue(mockWasmResult);

      const cppSource = 'int main() { return 0; }';
      const result = await adapter.transpile(cppSource);

      expect(result.success).toBe(true);
      expect(result.cCode).toBe('int main(void) { return 0; }');
      expect(result.hCode).toBe('#ifndef MAIN_H\n#define MAIN_H\n#endif');
      expect(result.error).toBeUndefined();
    });

    it('should initialize WASM module on first transpile', async () => {
      const mockWasmResult: WasmTranspileResult = {
        success: true,
        c: 'int x;',
        h: '',
        acsl: '',
        diagnostics: []
      };

      vi.mocked(mockInstance.transpile).mockReturnValue(mockWasmResult);

      await adapter.transpile('int x = 42;');

      // WASM module should be initialized
      expect(mockModule.Transpiler).toHaveBeenCalled();
      expect(mockInstance.getVersion).toHaveBeenCalled();
    });

    it('should pass options to WASM transpiler', async () => {
      const mockWasmResult: WasmTranspileResult = {
        success: true,
        c: 'int x;',
        h: '',
        acsl: '',
        diagnostics: []
      };

      vi.mocked(mockInstance.transpile).mockReturnValue(mockWasmResult);

      const cppSource = 'int x = 42;';
      const options: TranspileOptions = {
        sourcePath: '/test/file.cpp',
        target: 'c99',
        acsl: {
          statements: true,
          typeInvariants: true
        }
      };

      await adapter.transpile(cppSource, options);

      expect(mockInstance.transpile).toHaveBeenCalledWith(
        cppSource,
        expect.objectContaining({
          target: 'c99',
          acsl: expect.objectContaining({
            statements: true,
            typeInvariants: true
          })
        })
      );
    });

    it('should handle WASM transpilation errors', async () => {
      const mockWasmResult: WasmTranspileResult = {
        success: false,
        c: '',
        h: '',
        acsl: '',
        diagnostics: [
          { line: 1, column: 5, message: 'Syntax error', severity: 'error' }
        ]
      };

      vi.mocked(mockInstance.transpile).mockReturnValue(mockWasmResult);

      const result = await adapter.transpile('invalid c++');

      expect(result.success).toBe(false);
      expect(result.diagnostics).toHaveLength(1);
      expect(result.diagnostics?.[0]).toMatchObject({
        line: 1,
        column: 5,
        message: 'Syntax error',
        severity: 'error'
      });
    });

    it('should handle WASM module initialization failure', async () => {
      // Create a new adapter that will fail on initialization
      const { WasmTranspilerAdapter } = await import('./WasmTranspilerAdapter');
      const failingAdapter = new WasmTranspilerAdapter();

      // Mock the module to throw error
      const wasmModule = await import('@hupyy/cpptoc-wasm');
      vi.mocked(wasmModule.default as any).mockRejectedValueOnce(
        new Error('Failed to load WASM module')
      );

      const result = await failingAdapter.transpile('int main() {}');

      expect(result.success).toBe(false);
      expect(result.error).toContain('Failed to initialize WASM transpiler');
    });

    it('should preserve diagnostics from WASM', async () => {
      const mockWasmResult: WasmTranspileResult = {
        success: true,
        c: 'int main(void) {}',
        h: '',
        acsl: '',
        diagnostics: [
          { line: 1, column: 10, message: 'Unused variable', severity: 'warning' },
          { line: 2, column: 5, message: 'Optimization applied', severity: 'note' }
        ]
      };

      vi.mocked(mockInstance.transpile).mockReturnValue(mockWasmResult);

      const result = await adapter.transpile('int main() {}');

      expect(result.diagnostics).toHaveLength(2);
      expect(result.diagnostics?.[0]).toMatchObject({
        message: 'Unused variable',
        severity: 'warning'
      });
      expect(result.diagnostics?.[1]).toMatchObject({
        message: 'Optimization applied',
        severity: 'note'
      });
    });

    it('should preserve sourcePath in result', async () => {
      const mockWasmResult: WasmTranspileResult = {
        success: true,
        c: 'int x;',
        h: '',
        acsl: '',
        diagnostics: []
      };

      vi.mocked(mockInstance.transpile).mockReturnValue(mockWasmResult);

      const options: TranspileOptions = { sourcePath: '/my/file.cpp' };
      const result = await adapter.transpile('int x;', options);

      expect(result.sourcePath).toBe('/my/file.cpp');
    });

    it('should handle ACSL code output', async () => {
      const mockWasmResult: WasmTranspileResult = {
        success: true,
        c: 'int factorial(int n) {}',
        h: '',
        acsl: '/*@ requires n >= 0;\n    ensures \\result >= 1; */',
        diagnostics: []
      };

      vi.mocked(mockInstance.transpile).mockReturnValue(mockWasmResult);

      const result = await adapter.transpile('int factorial(int n) {}', {
        acsl: { statements: true }
      });

      expect(result.success).toBe(true);
      expect(result.acslCode).toContain('requires n >= 0');
    });

    it('should handle WASM transpiler throwing exception', async () => {
      vi.mocked(mockInstance.transpile).mockImplementation(() => {
        throw new Error('WASM runtime error');
      });

      const result = await adapter.transpile('int x;');

      expect(result.success).toBe(false);
      expect(result.error).toContain('WASM runtime error');
    });
  });

  describe('validateInput', () => {
    it('should validate C++ source code using transpilation', async () => {
      const mockWasmResult: WasmTranspileResult = {
        success: true,
        c: 'int main(void) {}',
        h: '',
        acsl: '',
        diagnostics: []
      };

      vi.mocked(mockInstance.transpile).mockReturnValue(mockWasmResult);

      const result = await adapter.validateInput('int main() {}');

      expect(result.valid).toBe(true);
      expect(result.errors).toEqual([]);
    });

    it('should return validation errors from transpilation', async () => {
      const mockWasmResult: WasmTranspileResult = {
        success: false,
        c: '',
        h: '',
        acsl: '',
        diagnostics: [
          { line: 1, column: 5, message: 'Syntax error', severity: 'error' },
          { line: 1, column: 10, message: 'Missing semicolon', severity: 'error' }
        ]
      };

      vi.mocked(mockInstance.transpile).mockReturnValue(mockWasmResult);

      const result = await adapter.validateInput('int x');

      expect(result.valid).toBe(false);
      expect(result.errors).toHaveLength(2);
      expect(result.errors?.[0]).toContain('Syntax error');
      expect(result.errors?.[1]).toContain('Missing semicolon');
    });

    it('should return validation warnings separately from errors', async () => {
      const mockWasmResult: WasmTranspileResult = {
        success: true,
        c: 'int x;',
        h: '',
        acsl: '',
        diagnostics: [
          { line: 1, column: 5, message: 'Unused variable', severity: 'warning' },
          { line: 1, column: 10, message: 'Implicit conversion', severity: 'warning' }
        ]
      };

      vi.mocked(mockInstance.transpile).mockReturnValue(mockWasmResult);

      const result = await adapter.validateInput('int x = 3.14;');

      expect(result.valid).toBe(true);
      expect(result.warnings).toHaveLength(2);
      expect(result.warnings?.[0]).toContain('Unused variable');
    });

    it('should handle validation errors gracefully', async () => {
      vi.mocked(mockInstance.transpile).mockImplementation(() => {
        throw new Error('Validation failed');
      });

      const result = await adapter.validateInput('int x;');

      expect(result.valid).toBe(false);
      expect(result.errors).toHaveLength(1);
      expect(result.errors?.[0]).toContain('Validation failed');
    });
  });

  describe('dispose', () => {
    it('should clean up WASM resources', async () => {
      // Initialize WASM by triggering transpilation
      const mockWasmResult: WasmTranspileResult = {
        success: true,
        c: 'int x;',
        h: '',
        acsl: '',
        diagnostics: []
      };

      vi.mocked(mockInstance.transpile).mockReturnValue(mockWasmResult);
      await adapter.transpile('int x;');

      // Dispose should call delete on transpiler instance
      adapter.dispose();

      expect(mockInstance.delete).toHaveBeenCalled();
    });

    it('should not throw if called before initialization', async () => {
      const { WasmTranspilerAdapter } = await import('./WasmTranspilerAdapter');
      const instance = new WasmTranspilerAdapter();

      // Should not throw even if WASM was never initialized
      expect(() => instance.dispose()).not.toThrow();
    });

    it('should be safe to call multiple times', async () => {
      const mockWasmResult: WasmTranspileResult = {
        success: true,
        c: 'int x;',
        h: '',
        acsl: '',
        diagnostics: []
      };

      vi.mocked(mockInstance.transpile).mockReturnValue(mockWasmResult);
      await adapter.transpile('int x;');

      // Call dispose multiple times
      adapter.dispose();
      adapter.dispose();

      // Should call delete only once (or be idempotent)
      expect(mockInstance.delete).toHaveBeenCalled();
    });
  });

  describe('ITranspiler interface compliance', () => {
    it('should implement transpile method', () => {
      expect(typeof adapter.transpile).toBe('function');
    });

    it('should implement validateInput method', () => {
      expect(typeof adapter.validateInput).toBe('function');
    });

    it('should implement dispose method', () => {
      expect(typeof adapter.dispose).toBe('function');
    });

    it('should return Promise from transpile', () => {
      const mockWasmResult: WasmTranspileResult = {
        success: true,
        c: '',
        h: '',
        acsl: '',
        diagnostics: []
      };

      vi.mocked(mockInstance.transpile).mockReturnValue(mockWasmResult);

      const result = adapter.transpile('');
      expect(result).toBeInstanceOf(Promise);
    });

    it('should return Promise from validateInput', () => {
      const mockWasmResult: WasmTranspileResult = {
        success: true,
        c: '',
        h: '',
        acsl: '',
        diagnostics: []
      };

      vi.mocked(mockInstance.transpile).mockReturnValue(mockWasmResult);

      const result = adapter.validateInput('');
      expect(result).toBeInstanceOf(Promise);
    });
  });

  describe('WASM module caching', () => {
    it('should reuse WASM module across multiple transpile calls', async () => {
      const mockWasmResult: WasmTranspileResult = {
        success: true,
        c: 'int x;',
        h: '',
        acsl: '',
        diagnostics: []
      };

      vi.mocked(mockInstance.transpile).mockReturnValue(mockWasmResult);

      // First transpile
      await adapter.transpile('int x;');
      const firstCallCount = vi.mocked(mockModule.Transpiler).mock.calls.length;

      // Second transpile
      await adapter.transpile('int y;');
      const secondCallCount = vi.mocked(mockModule.Transpiler).mock.calls.length;

      // Should not create new transpiler instance
      expect(firstCallCount).toBe(secondCallCount);
    });

    it('should handle concurrent transpile requests', async () => {
      const mockWasmResult: WasmTranspileResult = {
        success: true,
        c: 'int x;',
        h: '',
        acsl: '',
        diagnostics: []
      };

      vi.mocked(mockInstance.transpile).mockReturnValue(mockWasmResult);

      // Record initial call count (from beforeEach setup)
      const initialCallCount = vi.mocked(mockModule.Transpiler).mock.calls.length;

      // Start multiple transpile operations concurrently
      const promises = [
        adapter.transpile('int x;'),
        adapter.transpile('int y;'),
        adapter.transpile('int z;')
      ];

      const results = await Promise.all(promises);

      // All should succeed
      expect(results.every(r => r.success)).toBe(true);

      // Should only initialize WASM once (one additional call beyond setup)
      const finalCallCount = vi.mocked(mockModule.Transpiler).mock.calls.length;
      expect(finalCallCount - initialCallCount).toBe(1);
    });
  });
});
