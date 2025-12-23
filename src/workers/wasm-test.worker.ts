/**
 * Isolated WASM Loading Test Worker
 *
 * Tests different approaches for loading WASM files in Web Worker context
 * to debug 404 errors in WasmTranspilerAdapter
 */

// Test different base URL approaches
const tests = {
  // Approach 1: Vite BASE_URL (may be undefined in worker context)
  viteBaseUrl: (typeof import.meta.env !== 'undefined' && import.meta.env.BASE_URL) ? import.meta.env.BASE_URL : '/',

  // Approach 2: self.location (for debugging what we get)
  selfLocation: self.location.href,
  selfPathname: self.location.pathname,
  selfOrigin: self.location.origin,

  // Approach 3: Hard-coded paths to test
  hardcodedWithBase: '/cpp-to-c-website/wasm/cpptoc.js',
  hardcodedWithoutBase: '/wasm/cpptoc.js',

  // Approach 4: Relative paths
  relativeFromRoot: 'wasm/cpptoc.js',
  relativeWithDots: '../public/wasm/cpptoc.js'
};

// Function to test a single path
async function testPath(name: string, path: string): Promise<{ name: string; path: string; success: boolean; status?: number; error?: string }> {
  try {
    console.log(`[WASM Test] Testing ${name}: ${path}`);
    const response = await fetch(path);

    if (response.ok) {
      const text = await response.text();
      console.log(`[WASM Test] ✅ ${name} SUCCESS - loaded ${text.length} bytes`);
      return { name, path, success: true, status: response.status };
    } else {
      console.log(`[WASM Test] ❌ ${name} FAILED - ${response.status} ${response.statusText}`);
      return { name, path, success: false, status: response.status, error: response.statusText };
    }
  } catch (error) {
    const errorMsg = error instanceof Error ? error.message : String(error);
    console.log(`[WASM Test] ❌ ${name} ERROR - ${errorMsg}`);
    return { name, path, success: false, error: errorMsg };
  }
}

// Run all tests
async function runTests(): Promise<void> {
  console.log('[WASM Test] Starting WASM path resolution tests...');
  console.log('[WASM Test] Environment info:', {
    viteBaseUrl: tests.viteBaseUrl,
    selfLocation: tests.selfLocation,
    selfPathname: tests.selfPathname,
    selfOrigin: tests.selfOrigin
  });

  const results = [];

  // Test Vite BASE_URL approach
  results.push(await testPath('Vite BASE_URL', `${tests.viteBaseUrl}wasm/cpptoc.js`));

  // Test hard-coded paths
  results.push(await testPath('Hard-coded with base', tests.hardcodedWithBase));
  results.push(await testPath('Hard-coded without base', tests.hardcodedWithoutBase));

  // Test relative paths
  results.push(await testPath('Relative from root', tests.relativeFromRoot));

  // Test origin + base combinations
  results.push(await testPath('Origin + /cpp-to-c-website', `${tests.selfOrigin}/cpp-to-c-website/wasm/cpptoc.js`));
  results.push(await testPath('Origin + /wasm', `${tests.selfOrigin}/wasm/cpptoc.js`));

  // Summary
  const successCount = results.filter(r => r.success).length;
  console.log(`[WASM Test] Summary: ${successCount}/${results.length} tests passed`);

  // Send results back to main thread
  self.postMessage({
    type: 'TEST_RESULTS',
    results,
    summary: {
      total: results.length,
      passed: successCount,
      failed: results.length - successCount
    }
  });
}

// Start tests immediately when worker loads
runTests().catch(error => {
  console.error('[WASM Test] Fatal error:', error);
  self.postMessage({
    type: 'TEST_ERROR',
    error: error instanceof Error ? error.message : String(error)
  });
});
