# C++ to C Transpiler API Endpoints

Backend API endpoints for the C++ to C transpiler playground.

## Endpoints

### POST /api/transpile

Transpile C++ source code to C.

**Request:**
```json
{
  "source": "int main() { return 0; }",
  "options": {
    "sourcePath": "main.cpp",
    "includeACSL": true,
    "acslLevel": "basic",
    "enableExceptions": true,
    "enableRTTI": true
  }
}
```

**Request Fields:**
- `source` (required): C++ source code as a string
- `options` (optional): Transpilation options
  - `sourcePath` (optional): Original file path for error reporting
  - `includeACSL` (optional): Generate ACSL annotations (default: false)
  - `acslLevel` (optional): ACSL annotation level - "basic" or "full" (default: "basic")
  - `enableExceptions` (optional): Enable exception handling translation (default: true)
  - `enableRTTI` (optional): Enable RTTI translation (default: true)

**Success Response (200 OK):**
```json
{
  "success": true,
  "cCode": "/* Transpiled C code */",
  "diagnostics": [
    "warning: unused variable 'x'"
  ]
}
```

**Error Response (500 Internal Server Error):**
```json
{
  "success": false,
  "error": "Transpilation failed: syntax error at line 5"
}
```

**Timeout Response (408 Request Timeout):**
```json
{
  "success": false,
  "error": "Transpilation timeout (exceeded 30000ms)"
}
```

### POST /api/validate

Validate C++ source code syntax without transpiling.

**Request:**
```json
{
  "source": "int main() { return 0; }"
}
```

**Success Response (200 OK):**
```json
{
  "valid": true,
  "warnings": [
    "note: unused variable 'x' at line 3"
  ]
}
```

**Validation Failed Response (200 OK):**
```json
{
  "valid": false,
  "errors": [
    "error: expected ';' at line 5"
  ],
  "warnings": [
    "warning: implicit conversion from int to float"
  ]
}
```

**Error Response (500 Internal Server Error):**
```json
{
  "valid": false,
  "errors": [
    "Internal server error: transpiler binary not found"
  ]
}
```

## Implementation Details

### Transpiler Binary

The API uses the `cpptoc` transpiler binary located at:
```
/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/build/cpptoc
```

Ensure the transpiler is built before starting the API server:
```bash
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c
mkdir -p build && cd build
cmake ..
make cpptoc
```

### Temporary Files

Both endpoints create temporary files in the system temp directory:
- Input files: `/tmp/cpptoc-{timestamp}/input.cpp`
- Output files: `/tmp/cpptoc-{timestamp}/input.c`

Files are automatically cleaned up after each request.

### Timeouts

- Transpile endpoint: 30 seconds
- Validate endpoint: 10 seconds

### CORS

Both endpoints support CORS with the following headers:
- `Access-Control-Allow-Origin: *`
- `Access-Control-Allow-Methods: POST, OPTIONS`
- `Access-Control-Allow-Headers: Content-Type`

## Testing

### Using curl

**Transpile:**
```bash
curl -X POST http://localhost:4321/api/transpile \
  -H "Content-Type: application/json" \
  -d '{
    "source": "#include <iostream>\nint main() { std::cout << \"Hello!\" << std::endl; return 0; }"
  }'
```

**Validate:**
```bash
curl -X POST http://localhost:4321/api/validate \
  -H "Content-Type: application/json" \
  -d '{
    "source": "int main() { return 0; }"
  }'
```

### Using test script

A comprehensive test script is provided:
```bash
npm run dev  # Start dev server in one terminal
./test-api.sh  # Run tests in another terminal
```

### Using TypeScript

```typescript
const response = await fetch('http://localhost:4321/api/transpile', {
  method: 'POST',
  headers: { 'Content-Type': 'application/json' },
  body: JSON.stringify({
    source: 'int main() { return 0; }',
    options: { includeACSL: true }
  })
});

const result = await response.json();
if (result.success) {
  console.log('Transpiled code:', result.cCode);
} else {
  console.error('Error:', result.error);
}
```

## Error Handling

The API handles the following error cases:

1. **Invalid request body**: Returns 400 Bad Request
2. **Transpiler binary not found**: Returns 500 Internal Server Error
3. **Syntax errors**: Returns 500 with error details in response body
4. **Timeout**: Returns 408 Request Timeout
5. **File I/O errors**: Returns 500 with error message

## Integration with Frontend

The `BackendTranspilerAdapter` in `src/adapters/BackendTranspilerAdapter.ts` provides a typed client for these endpoints:

```typescript
import { BackendTranspilerAdapter } from '@/adapters/BackendTranspilerAdapter';

const transpiler = new BackendTranspilerAdapter('http://localhost:4321');

// Transpile
const result = await transpiler.transpile(sourceCode, {
  includeACSL: true,
  acslLevel: 'full'
});

// Validate
const validation = await transpiler.validateInput(sourceCode);
```

## Architecture

```
Client Request
    ↓
POST /api/transpile
    ↓
Parse JSON body
    ↓
Create temp directory: /tmp/cpptoc-{timestamp}/
    ↓
Write source to: input.cpp
    ↓
Execute: cpptoc input.cpp [options]
    ↓
Read output from: input.c
    ↓
Parse stderr for diagnostics
    ↓
Cleanup temp files
    ↓
Return JSON response
```

## Deployment Considerations

For production deployment:

1. **Update transpiler path**: Change hardcoded path to environment variable
2. **Add rate limiting**: Prevent abuse
3. **Add authentication**: Protect API from unauthorized access
4. **Increase timeouts**: For large C++ projects
5. **Add caching**: Cache transpilation results for identical inputs
6. **Error monitoring**: Log errors to monitoring service
7. **Resource limits**: Set memory and CPU limits for transpiler process

### Environment Variables (Future)

```bash
TRANSPILER_PATH=/path/to/cpptoc
TRANSPILE_TIMEOUT=30000
VALIDATE_TIMEOUT=10000
TEMP_DIR=/tmp/cpptoc
```

## Known Limitations

1. **Single file only**: Cannot handle multi-file projects with includes
2. **No header provisioning**: Standard library headers must be available on server
3. **No streaming**: Large outputs buffered in memory
4. **Synchronous execution**: Blocks server thread during transpilation
5. **Limited error details**: Some Clang errors may not be parsed correctly

## Future Enhancements

- [ ] Support for multi-file projects
- [ ] Header file provisioning mechanism
- [ ] Streaming response for large outputs
- [ ] Async execution with job queue
- [ ] Better error parsing from Clang diagnostics
- [ ] Caching layer for repeated requests
- [ ] WebSocket support for real-time progress
- [ ] Docker containerization for isolated execution
