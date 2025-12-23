/**
 * WasmTranspilerAdapter Tests
 *
 * Testing HTTP integration (formerly WASM-based)
 * Following TDD: Write tests first, implement to pass
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import type { ITranspiler } from '../core/interfaces/ITranspiler';
import type { TranspileOptions } from '../core/interfaces/types';

// Mock API configuration
vi.mock('../config/api', () => ({
  getApiBaseUrl: () => 'http://localhost:3001',
  getApiTimeout: () => 30000
}));

// Mock fetch globally
global.fetch = vi.fn();

/**
 * Test suite for WasmTranspilerAdapter
 *
 * Tests HTTP communication with backend transpiler service:
 * - Successful transpilation
 * - Server errors (500, 400)
 * - Network errors
 * - Timeout errors
 * - Error response parsing
 * - Request payload validation
 * - Backward compatibility with WASM interface
 */
describe('WasmTranspilerAdapter', () => {
  let adapter: ITranspiler;
  const mockFetch = global.fetch as ReturnType<typeof vi.fn>;
  const testApiUrl = 'http://localhost:3001';

  beforeEach(async () => {
    vi.clearAllMocks();
    // Dynamic import to ensure fresh instance
    const { WasmTranspilerAdapter } = await import('./WasmTranspilerAdapter');
    adapter = new WasmTranspilerAdapter();
  });

  describe('constructor', () => {
    it('should create instance with API configuration', async () => {
      const { WasmTranspilerAdapter } = await import('./WasmTranspilerAdapter');
      const instance = new WasmTranspilerAdapter();
      expect(instance).toBeDefined();
    });
  });

  describe('transpile', () => {
    it('should successfully transpile C++ to C', async () => {
      const mockResponse = {
        success: true,
        cCode: 'int main(void) { return 0; }',
        diagnostics: []
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => mockResponse
      } as Response);

      const cppSource = 'int main() { return 0; }';
      const result = await adapter.transpile(cppSource);

      expect(result.success).toBe(true);
      expect(result.cCode).toBe('int main(void) { return 0; }');
      expect(result.error).toBeUndefined();
    });

    it('should send correct request payload', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({ success: true, cCode: 'int x;' })
      } as Response);

      const cppSource = 'int x = 42;';
      const options: TranspileOptions = {
        sourcePath: '/test/file.cpp',
        includeACSL: true,
        targetStandard: 'c99'
      };

      await adapter.transpile(cppSource, options);

      expect(mockFetch).toHaveBeenCalledWith(
        `${testApiUrl}/api/transpile`,
        expect.objectContaining({
          method: 'POST',
          headers: {
            'Content-Type': 'application/json'
          },
          body: expect.stringContaining('"source":"int x = 42;"')
        })
      );
    });

    it('should handle server error (500)', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 500,
        statusText: 'Internal Server Error',
        json: async () => ({ error: 'Server error occurred' })
      } as Response);

      const result = await adapter.transpile('int main() {}');

      expect(result.success).toBe(false);
      expect(result.error).toContain('Server error');
      expect(result.cCode).toBeUndefined();
    });

    it('should handle network error', async () => {
      mockFetch.mockRejectedValueOnce(new Error('Failed to fetch'));

      const result = await adapter.transpile('int main() {}');

      expect(result.success).toBe(false);
      expect(result.error).toContain('Network error');
    });

    it('should handle timeout error', async () => {
      mockFetch.mockRejectedValueOnce(new DOMException('The operation was aborted', 'AbortError'));

      const result = await adapter.transpile('int main() {}');

      expect(result.success).toBe(false);
      expect(result.error).toContain('timeout');
    });

    it('should preserve diagnostics from backend', async () => {
      const mockResponse = {
        success: true,
        cCode: 'int main(void) {}',
        diagnostics: ['Warning: unused variable', 'Note: optimization applied']
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => mockResponse
      } as Response);

      const result = await adapter.transpile('int main() {}');

      expect(result.diagnostics).toEqual([
        'Warning: unused variable',
        'Note: optimization applied'
      ]);
    });

    it('should preserve sourcePath in result', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({ success: true, cCode: 'int x;' })
      } as Response);

      const options: TranspileOptions = { sourcePath: '/my/file.cpp' };
      const result = await adapter.transpile('int x;', options);

      expect(result.sourcePath).toBe('/my/file.cpp');
    });

    it('should handle malformed JSON response', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => {
          throw new Error('Invalid JSON');
        }
      } as Response);

      const result = await adapter.transpile('int main() {}');

      expect(result.success).toBe(false);
      expect(result.error).toContain('Invalid response from server');
    });
  });

  describe('validateInput', () => {
    it('should validate C++ source code', async () => {
      const mockResponse = {
        valid: true,
        errors: [],
        warnings: []
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => mockResponse
      } as Response);

      const result = await adapter.validateInput('int main() {}');

      expect(result.valid).toBe(true);
      expect(result.errors).toEqual([]);
    });

    it('should return validation errors', async () => {
      const mockResponse = {
        valid: false,
        errors: ['Syntax error on line 1', 'Missing semicolon'],
        warnings: []
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => mockResponse
      } as Response);

      const result = await adapter.validateInput('int x');

      expect(result.valid).toBe(false);
      expect(result.errors).toContain('Syntax error on line 1');
      expect(result.errors).toContain('Missing semicolon');
    });

    it('should send validation request to correct endpoint', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({ valid: true, errors: [], warnings: [] })
      } as Response);

      await adapter.validateInput('int x;');

      expect(mockFetch).toHaveBeenCalledWith(
        `${testApiUrl}/api/validate`,
        expect.objectContaining({
          method: 'POST',
          headers: {
            'Content-Type': 'application/json'
          },
          body: expect.stringContaining('"source":"int x;"')
        })
      );
    });

    it('should handle network error in validation', async () => {
      mockFetch.mockRejectedValueOnce(new Error('Failed to fetch'));

      const result = await adapter.validateInput('int x;');

      expect(result.valid).toBe(false);
      expect(result.errors?.length).toBeGreaterThan(0);
      expect(result.errors?.[0]).toContain('Network error');
    });
  });

  describe('cancel', () => {
    it('should cancel ongoing request', async () => {
      const { WasmTranspilerAdapter } = await import('./WasmTranspilerAdapter');
      const instance = new WasmTranspilerAdapter();

      // Should not throw
      expect(() => instance.cancel()).not.toThrow();
    });
  });

  describe('dispose', () => {
    it('should clean up resources', async () => {
      const { WasmTranspilerAdapter } = await import('./WasmTranspilerAdapter');
      const instance = new WasmTranspilerAdapter();

      // Should not throw
      expect(() => instance.dispose()).not.toThrow();
    });
  });

  describe('ITranspiler interface compliance', () => {
    it('should implement transpile method', () => {
      expect(typeof adapter.transpile).toBe('function');
    });

    it('should implement validateInput method', () => {
      expect(typeof adapter.validateInput).toBe('function');
    });

    it('should return Promise from transpile', () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({ success: true, cCode: '' })
      } as Response);

      const result = adapter.transpile('');
      expect(result).toBeInstanceOf(Promise);
    });

    it('should return Promise from validateInput', () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({ valid: true, errors: [], warnings: [] })
      } as Response);

      const result = adapter.validateInput('');
      expect(result).toBeInstanceOf(Promise);
    });
  });
});
