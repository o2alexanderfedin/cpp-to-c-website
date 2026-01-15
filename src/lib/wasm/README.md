# WASM Transpiler Integration

This module provides a clean, type-safe API for integrating the `@hupyy/cpptoc-wasm` transpiler into the website playground.

## Architecture

The integration follows the **Adapter Pattern** and **SOLID principles**:

```
Browser File System → WasmTranspilerAdapter → WASM Module → C Code
```

### Components

1. **Loader** (`loader.ts`)
   - Singleton WASM module loader
   - Lazy loading (load on first use)
   - State management (idle → loading → ready/error)
   - Event subscription for state changes

2. **React Hooks** (`hooks.ts`)
   - `useWasmModule()` - Load and track WASM module state
   - `useTranspiler()` - Create and manage transpiler instance
   - `useWasmLoadingState()` - Render based on loading state

3. **API Wrapper** (`api.ts`)
   - `transpile()` - Transpile single file
   - `transpileFiles()` - Transpile multiple files
   - Type-safe Result pattern (no exceptions for expected errors)

4. **Types** (`types.ts`)
   - Re-exports from `@hupyy/cpptoc-wasm`
   - Additional helper types

## Usage

### Basic Transpilation

```tsx
import { transpile } from '@/lib/wasm';

async function transpileCode(cppCode: string) {
  const result = await transpile(cppCode, {
    target: 'c99',
    enableACSL: true
  });

  if (result.success) {
    console.log('C code:', result.cCode);
    console.log('Header:', result.hCode);
  } else {
    console.error('Error:', result.error);
    result.diagnostics.forEach(d => {
      console.error(`${d.severity}: ${d.message}`);
    });
  }
}
```

### React Component with Loading State

```tsx
import { useWasmModule } from '@/lib/wasm';

function TranspilerUI() {
  const { isLoading, isReady, error, module } = useWasmModule();

  if (isLoading) {
    return <div>Loading transpiler...</div>;
  }

  if (error) {
    return <div>Error: {error.message}</div>;
  }

  if (!isReady) {
    return null;
  }

  // Use module...
  return <div>Transpiler ready!</div>;
}
```

### Using Transpiler Instance

```tsx
import { useTranspiler } from '@/lib/wasm';

function TranspileButton({ code }: { code: string }) {
  const { instance, isReady } = useTranspiler();

  const handleClick = () => {
    if (!instance) return;

    const result = instance.transpile(code, {
      target: 'c99',
      enableACSL: true
    });

    console.log(result);
  };

  return (
    <button onClick={handleClick} disabled={!isReady}>
      Transpile
    </button>
  );
}
```

### Multiple Files

```tsx
import { transpileFiles } from '@/lib/wasm';

async function transpileProject(files: Map<string, string>) {
  const results = await transpileFiles(files, {
    target: 'c11',
    optimize: true
  });

  for (const [filename, result] of results) {
    if (result.success) {
      console.log(`${filename}: ✓`);
    } else {
      console.error(`${filename}: ${result.error}`);
    }
  }
}
```

## Integration with Existing Adapters

The `WasmTranspilerAdapter` class in `src/adapters/` uses this WASM module:

```ts
// Old (SimpleTranspiler - manual parser)
import { SimpleTranspiler } from '../lib/simple-transpiler';
const transpiler = new SimpleTranspiler();

// New (@hupyy/cpptoc-wasm - real transpiler)
import type { WASMModule } from '@hupyy/cpptoc-wasm';
const module = await loadWasmModule();
const transpiler = new module.Transpiler();
```

## Worker Integration

The `WorkerPoolController` automatically uses the WASM transpiler through `WasmTranspilerAdapter`:

```
Main Thread                    Worker Thread
-----------                    -------------
WizardComponent
    ↓
TranspilationController
    ↓
WorkerPoolController  ------>  transpiler.worker.ts
    ↓                              ↓
(assigns tasks)              WasmTranspilerAdapter
    ↓                              ↓
(receives results)           WASM Transpiler
```

## Performance Considerations

1. **Lazy Loading**: WASM module is loaded on first use, not on page load
2. **Singleton Pattern**: One WASM module instance shared across app
3. **Worker Pools**: Parallel transpilation using Web Workers
4. **Memory Management**: Transpiler instances are properly disposed via `.delete()`

## Error Handling

The API uses **Result pattern** instead of exceptions:

```ts
// ✓ Good - Type-safe error handling
const result = await transpile(code);
if (result.success) {
  // TypeScript knows: result.cCode exists
  console.log(result.cCode);
} else {
  // TypeScript knows: result.error exists
  console.error(result.error);
}

// ✗ Bad - Don't use try/catch for expected errors
try {
  const result = await transpile(code);
} catch (error) {
  // This won't catch transpilation errors!
  // Only catches unexpected errors (WASM loading failures, etc.)
}
```

## Type Safety

All types are strictly typed:

- No `any` types
- Discriminated unions for Result types
- Proper null checks (no `!` assertions)
- Type guards for runtime validation

## Testing

Unit tests: `test/wasm/`
- `loader.test.ts` - Loader state management
- `api.test.ts` - API wrapper (basic tests)

Integration tests: `tests/` (Playwright E2E)
- Full transpilation flow
- Worker pool integration
- Playground UI integration

## Troubleshooting

### WASM module fails to load

```
Error: Failed to initialize WASM transpiler
```

**Solutions:**
1. Check browser console for detailed error
2. Verify `@hupyy/cpptoc-wasm` is in `node_modules`
3. Check network tab for WASM file loading
4. Ensure Vite/bundler is configured for WASM

### TypeScript errors

```
Cannot find module '@hupyy/cpptoc-wasm'
```

**Solution:**
```bash
cd website
npm install
```

### Worker errors

```
Worker failed to initialize
```

**Solutions:**
1. Check if Web Workers are supported
2. Verify worker file is being built correctly
3. Check browser console in worker context

## Migration from SimpleTranspiler

If you're migrating from the old `SimpleTranspiler`:

```ts
// Before
import { SimpleTranspiler } from '@/lib/simple-transpiler';
const transpiler = new SimpleTranspiler();
await transpiler.initialize();
const result = await transpiler.transpile(code);

// After
import { transpile } from '@/lib/wasm';
const result = await transpile(code);
```

The new API is simpler and handles initialization automatically.
