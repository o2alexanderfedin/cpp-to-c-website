import { test, expect } from '@playwright/test';

test.describe('API Tests', () => {
  test('POST /api/transpile - valid C++ code', async ({ request }) => {
    const response = await request.post('/api/transpile', {
      data: {
        source: 'int main() { return 0; }',
        options: { targetStandard: 'c99' },
      },
    });

    // Should return 200 or handle appropriately
    const status = response.status();
    expect([200, 201]).toContain(status);

    const json = await response.json();
    expect(json).toHaveProperty('success');
  });

  test('POST /api/transpile - invalid C++ code', async ({ request }) => {
    const response = await request.post('/api/transpile', {
      data: {
        source: 'invalid C++ code !@#$%',
      },
    });

    // Should handle errors gracefully
    const json = await response.json();
    expect(json).toHaveProperty('success');
  });

  test('POST /api/transpile - empty code', async ({ request }) => {
    const response = await request.post('/api/transpile', {
      data: {
        source: '',
      },
    });

    const json = await response.json();
    expect(json).toHaveProperty('success');
  });

  test('POST /api/transpile - large code input', async ({ request }) => {
    const largeCode = `
      #include <iostream>

      int main() {
        ${'std::cout << "test" << std::endl;'.repeat(100)}
        return 0;
      }
    `;

    const response = await request.post('/api/transpile', {
      data: {
        source: largeCode,
      },
    });

    const status = response.status();
    expect([200, 201, 400, 413]).toContain(status);
  });

  test('API response time should be reasonable', async ({ request }) => {
    const startTime = Date.now();

    await request.post('/api/transpile', {
      data: {
        source: 'int main() { return 0; }',
      },
    });

    const responseTime = Date.now() - startTime;
    expect(responseTime).toBeLessThan(5000); // 5 seconds max
  });
});
