/**
 * Manual test file for transpile API endpoint
 *
 * This is a TypeScript file that can be run with ts-node to test the endpoint logic
 * without starting the full Astro dev server.
 */

import { existsSync } from 'fs';

const TRANSPILER_PATH = '/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/build/cpptoc';

console.log('Checking transpiler binary...');
console.log(`Path: ${TRANSPILER_PATH}`);
console.log(`Exists: ${existsSync(TRANSPILER_PATH)}`);

if (existsSync(TRANSPILER_PATH)) {
  console.log('✓ Transpiler binary found');
} else {
  console.log('✗ Transpiler binary NOT found');
  console.log('  Please ensure the transpiler is built:');
  console.log('  cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c');
  console.log('  mkdir -p build && cd build');
  console.log('  cmake .. && make');
}

// Test simple C++ code
const testSource = `
#include <iostream>

int main() {
    std::cout << "Hello, World!" << std::endl;
    return 0;
}
`;

console.log('\nTest C++ source:');
console.log('---');
console.log(testSource);
console.log('---');

console.log('\nAPI endpoints created:');
console.log('  POST /api/transpile - Transpile C++ to C');
console.log('  POST /api/validate - Validate C++ syntax');
console.log('\nTo test, start the dev server and run:');
console.log('  npm run dev');
console.log('  ./test-api.sh');
