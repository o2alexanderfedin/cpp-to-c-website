# API Endpoints Testing Guide

Quick guide to test the newly created backend API endpoints.

## Prerequisites

1. **Transpiler binary built**:
   ```bash
   ls -la /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/build/cpptoc
   # Should show: -rwxr-xr-x ... cpptoc
   ```

2. **Dependencies installed**:
   ```bash
   npm install
   ```

## Quick Verification

Run the verification script:
```bash
npx tsx src/pages/api/__test-transpile.ts
```

Expected output:
```
✓ Transpiler binary found
```

## Start Dev Server

In one terminal:
```bash
npm run dev
```

Wait for:
```
astro v4.x.x ready in XXX ms
┃ Local    http://localhost:4321/
```

## Test with curl

In another terminal:

### Test 1: Simple Transpilation

```bash
curl -X POST http://localhost:4321/api/transpile \
  -H "Content-Type: application/json" \
  -d '{"source": "int main() { return 0; }"}' \
  | jq '.'
```

**Expected**:
```json
{
  "success": true,
  "cCode": "/* transpiled C code here */"
}
```

### Test 2: Validation (Valid Code)

```bash
curl -X POST http://localhost:4321/api/validate \
  -H "Content-Type: application/json" \
  -d '{"source": "int main() { return 0; }"}' \
  | jq '.'
```

**Expected**:
```json
{
  "valid": true
}
```

### Test 3: Validation (Invalid Code)

```bash
curl -X POST http://localhost:4321/api/validate \
  -H "Content-Type: application/json" \
  -d '{"source": "int main() { invalid syntax }"}' \
  | jq '.'
```

**Expected**:
```json
{
  "valid": false,
  "errors": ["error: ..."]
}
```

## Automated Test Script

Run all tests at once:
```bash
./test-api.sh
```

This runs 5 comprehensive test cases:
1. Simple C++ transpilation
2. ACSL annotation generation
3. Invalid syntax error handling
4. Validation of valid code
5. Validation of invalid code

## Test with Playground UI

1. Navigate to http://localhost:4321/playground
2. The playground uses `BackendTranspilerAdapter` which calls these endpoints
3. Try transpiling some C++ code through the UI

## Troubleshooting

### Error: "Transpiler binary not found"

**Fix**:
```bash
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c
mkdir -p build && cd build
cmake ..
make cpptoc
```

### Error: "Connection refused"

**Fix**: Ensure dev server is running (`npm run dev`)

### Error: "Invalid JSON response"

**Fix**: Check that the request has `Content-Type: application/json` header

### Error: "Transpilation timeout"

**Fix**: Source code may be too complex. Try simpler example or increase timeout in API file.

## Manual Testing Checklist

- [ ] Transpiler binary exists and is executable
- [ ] Dev server starts without errors
- [ ] `/api/transpile` returns successful response for simple code
- [ ] `/api/transpile` handles invalid syntax gracefully
- [ ] `/api/validate` validates correct code
- [ ] `/api/validate` detects syntax errors
- [ ] ACSL option generates annotations
- [ ] Timeout protection works (use very large/complex code)
- [ ] Diagnostics are returned when available
- [ ] Error messages are user-friendly

## Integration Testing

Test with the frontend adapter:

```typescript
// In browser console at http://localhost:4321/playground
const adapter = new BackendTranspilerAdapter('http://localhost:4321');
const result = await adapter.transpile('int main() { return 0; }');
console.log(result);
```

Expected:
```javascript
{
  success: true,
  cCode: "/* C code */",
  diagnostics: [...]
}
```

## Performance Testing

### Small Code (< 100 lines)
Should complete in < 1 second

### Medium Code (100-500 lines)
Should complete in < 5 seconds

### Large Code (500+ lines)
Should complete in < 30 seconds (before timeout)

## Next Steps

After successful testing:

1. **Commit changes**:
   ```bash
   git add src/pages/api/
   git commit -m "feat: Add backend API endpoints for transpilation"
   ```

2. **Update playground to use real API**:
   Edit `src/lib/playground/setup.ts` to use production config

3. **Deploy**:
   Build and deploy to production server

## Reference

- API Documentation: `src/pages/api/README.md`
- Implementation Summary: `API_IMPLEMENTATION.md`
- Frontend Adapter: `src/adapters/BackendTranspilerAdapter.ts`
