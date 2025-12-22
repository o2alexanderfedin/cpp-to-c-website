/**
 * BackendTranspilerAdapter Tests
 *
 * Testing HTTP integration with backend transpilation API
 * Following TDD: Write tests first, implement to pass
 */

import { describe, it, expect, beforeEach, vi } from 'vitest';
import type { ITranspiler } from '../core/interfaces/ITranspiler';
import type { TranspileOptions, TranspileResult, ValidationResult } from '../core/interfaces/types';

// Mock fetch globally
global.fetch = vi.fn();

/**
 * Test suite for BackendTranspilerAdapter
 *
 * Tests HTTP communication with backend transpiler service:
 * - Successful transpilation
 * - Server errors (500, 400)
 * - Network errors
 * - Timeout errors
 * - Error response parsing
 * - Request payload validation
 */
describe('BackendTranspilerAdapter', () => {
  let adapter: ITranspiler;
  const mockFetch = global.fetch as ReturnType<typeof vi.fn>;
  const testApiUrl = 'https://api.example.com';

  beforeEach(async () => {
    vi.clearAllMocks();
    // Dynamic import to ensure fresh instance
    const { BackendTranspilerAdapter } = await import('./BackendTranspilerAdapter');
    adapter = new BackendTranspilerAdapter(testApiUrl);
  });

  describe('constructor', () => {
    it('should create instance with API URL', async () => {
      const { BackendTranspilerAdapter } = await import('./BackendTranspilerAdapter');
      const instance = new BackendTranspilerAdapter('https://test.com');
      expect(instance).toBeDefined();
    });

    it('should handle missing trailing slash in URL', async () => {
      const { BackendTranspilerAdapter } = await import('./BackendTranspilerAdapter');
      const instance = new BackendTranspilerAdapter('https://test.com/');
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

    it('should include options in request', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({ success: true, cCode: 'int x;' })
      } as Response);

      const options: TranspileOptions = {
        sourcePath: '/test.cpp',
        includeACSL: false,
        targetStandard: 'c11'
      };

      await adapter.transpile('int x;', options);

      const callBody = JSON.parse((mockFetch.mock.calls[0][1] as RequestInit).body as string);
      expect(callBody.options).toEqual(options);
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

    it('should handle bad request (400)', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 400,
        statusText: 'Bad Request',
        json: async () => ({ error: 'Invalid source code' })
      } as Response);

      const result = await adapter.transpile('invalid c++');

      expect(result.success).toBe(false);
      expect(result.error).toContain('Invalid source code');
    });

    it('should handle network error', async () => {
      mockFetch.mockRejectedValueOnce(new Error('Network error'));

      const result = await adapter.transpile('int main() {}');

      expect(result.success).toBe(false);
      expect(result.error).toContain('Network error');
    });

    it('should handle timeout error', async () => {
      mockFetch.mockRejectedValueOnce(new Error('Request timeout'));

      const result = await adapter.transpile('int main() {}');

      expect(result.success).toBe(false);
      expect(result.error).toContain('timeout');
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
      expect(result.error).toContain('Invalid JSON');
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

    it('should handle empty source code', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({ success: true, cCode: '' })
      } as Response);

      const result = await adapter.transpile('');

      expect(result.success).toBe(true);
      expect(result.cCode).toBe('');
    });

    it('should handle very long source code', async () => {
      const longSource = 'int x;\n'.repeat(10000);

      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({ success: true, cCode: longSource })
      } as Response);

      const result = await adapter.transpile(longSource);

      expect(result.success).toBe(true);
      expect(result.cCode).toBe(longSource);
    });

    it('should handle special characters in source', async () => {
      const specialSource = 'char* str = "Hello\\nWorld\\t!";';

      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => ({ success: true, cCode: specialSource })
      } as Response);

      const result = await adapter.transpile(specialSource);

      expect(result.success).toBe(true);
      expect(mockFetch).toHaveBeenCalledWith(
        expect.any(String),
        expect.objectContaining({
          body: expect.stringContaining('Hello\\\\nWorld\\\\t!')
        })
      );
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

    it('should return validation warnings', async () => {
      const mockResponse = {
        valid: true,
        errors: [],
        warnings: ['Unused variable', 'Implicit conversion']
      };

      mockFetch.mockResolvedValueOnce({
        ok: true,
        status: 200,
        json: async () => mockResponse
      } as Response);

      const result = await adapter.validateInput('int x = 3.14;');

      expect(result.valid).toBe(true);
      expect(result.warnings).toContain('Unused variable');
      expect(result.warnings).toContain('Implicit conversion');
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
      mockFetch.mockRejectedValueOnce(new Error('Network error'));

      const result = await adapter.validateInput('int x;');

      expect(result.valid).toBe(false);
      expect(result.errors).toContain('Network error');
    });

    it('should handle server error in validation', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 500,
        statusText: 'Internal Server Error',
        json: async () => ({ error: 'Server error' })
      } as Response);

      const result = await adapter.validateInput('int x;');

      expect(result.valid).toBe(false);
      expect(result.errors).toContain('Server error');
    });
  });

  describe('error handling', () => {
    it('should convert fetch abort to timeout error', async () => {
      mockFetch.mockRejectedValueOnce(new DOMException('The operation was aborted', 'AbortError'));

      const result = await adapter.transpile('int x;');

      expect(result.success).toBe(false);
      expect(result.error).toContain('timeout');
    });

    it('should handle missing error message gracefully', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 500,
        statusText: 'Internal Server Error',
        json: async () => ({})
      } as Response);

      const result = await adapter.transpile('int x;');

      expect(result.success).toBe(false);
      expect(result.error).toBeDefined();
    });

    it('should include HTTP status in error message', async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 503,
        statusText: 'Service Unavailable',
        json: async () => ({ error: 'Service temporarily unavailable' })
      } as Response);

      const result = await adapter.transpile('int x;');

      expect(result.success).toBe(false);
      expect(result.error).toContain('503');
    });

    it('should handle non-Error thrown values', async () => {
      mockFetch.mockRejectedValueOnce('string error');

      const result = await adapter.transpile('int x;');

      expect(result.success).toBe(false);
      expect(result.error).toBe('Unknown error occurred');
    });

    it('should handle null thrown values', async () => {
      mockFetch.mockRejectedValueOnce(null);

      const result = await adapter.transpile('int x;');

      expect(result.success).toBe(false);
      expect(result.error).toBe('Unknown error occurred');
    });

    it('should handle generic Error with message', async () => {
      mockFetch.mockRejectedValueOnce(new Error('Generic error message'));

      const result = await adapter.transpile('int x;');

      expect(result.success).toBe(false);
      expect(result.error).toBe('Generic error message');
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
