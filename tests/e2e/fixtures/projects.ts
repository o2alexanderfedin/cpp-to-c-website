/**
 * Test project fixtures for E2E tests
 */

export interface TestFile {
  path: string;
  name: string;
  content: string;
}

export interface TestProject {
  name: string;
  files: TestFile[];
}

/**
 * Small project with 3 files
 */
export const smallProject: TestProject = {
  name: 'small-project',
  files: [
    {
      path: 'main.cpp',
      name: 'main.cpp',
      content: `#include <iostream>

int main() {
    std::cout << "Hello, World!" << std::endl;
    return 0;
}`,
    },
    {
      path: 'helper.cpp',
      name: 'helper.cpp',
      content: `#include "helper.h"

int add(int a, int b) {
    return a + b;
}`,
    },
    {
      path: 'helper.h',
      name: 'helper.h',
      content: `#ifndef HELPER_H
#define HELPER_H

int add(int a, int b);

#endif`,
    },
  ],
};

/**
 * Larger project with nested directories
 */
export const largeProject: TestProject = {
  name: 'large-project',
  files: [
    {
      path: 'src/main.cpp',
      name: 'main.cpp',
      content: `#include <iostream>
#include "core/engine.h"

int main() {
    Engine engine;
    engine.run();
    return 0;
}`,
    },
    {
      path: 'src/core/engine.cpp',
      name: 'engine.cpp',
      content: `#include "engine.h"
#include <iostream>

void Engine::run() {
    std::cout << "Engine running" << std::endl;
}`,
    },
    {
      path: 'src/core/engine.h',
      name: 'engine.h',
      content: `#ifndef ENGINE_H
#define ENGINE_H

class Engine {
public:
    void run();
};

#endif`,
    },
  ],
};

/**
 * Project with intentional errors
 */
export const errorProject: TestProject = {
  name: 'error-project',
  files: [
    {
      path: 'valid.cpp',
      name: 'valid.cpp',
      content: `int main() { return 0; }`,
    },
    {
      path: 'invalid.cpp',
      name: 'invalid.cpp',
      content: `// This will cause a transpilation error
#error "Intentional error for testing"
int main() { return 0; }`,
    },
  ],
};

/**
 * Generate a large project with N files
 */
export function generateLargeProject(fileCount: number): TestProject {
  const files: TestFile[] = [];

  for (let i = 0; i < fileCount; i++) {
    const dirIndex = Math.floor(i / 10);
    const path = `src/dir${dirIndex}/file${i}.cpp`;
    const name = `file${i}.cpp`;
    const content = `// File ${i}
int function${i}() {
    return ${i};
}`;

    files.push({ path, name, content });
  }

  return {
    name: `large-project-${fileCount}`,
    files,
  };
}
