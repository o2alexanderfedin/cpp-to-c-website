# Phase 26, Plan 26-01: Backend API Architecture for REAL Transpilation

**Phase**: 26 - Provide REAL transpilation via Backend API
**Plan**: 26-01 - Create backend API + HTTP client architecture
**Type**: Architecture Implementation (NO PLACEHOLDERS!)
**Created**: 2025-12-22
**Revised**: 2025-12-22 (after discovering WASM limitations)

---

## Objective

Provide **REAL** C++ to C transpilation for production use via backend API architecture.

**User Requirement**: "NO PLACEHOLDERS! All real!!! Quality is important!!!"

**Success**: Real customers can transpile C++ to C through web playground using REAL Clang LibTooling (not placeholders).

---

## Context

### Architectural Discovery (Phase 26)

**What We Attempted**:
- Build WASM modules with Emscripten to run transpiler in browser

**What We Discovered**:
- TranspilerAPI.cpp requires full Clang+LLVM infrastructure
- Compiling Clang to WASM = 100-500MB file size
- Build time: 10+ hours
- Browser memory: Gigabytes required
- Load time: Minutes
- **COMPLETELY IMPRACTICAL** for production

**Industry Reality**:
- Nobody ships C++ compilers in browser
- Compiler Explorer, WebAssembly Studio, etc. all use **backend servers**
- This is the standard, production-proven architecture

### What We Built (Phase 25) - Still Valid! ✅

- ✅ TranspilerAPI.h (132 lines) - Clean library interface
- ✅ TranspilerAPI.cpp (329 lines) - REAL Clang LibTooling implementation
- ✅ NO PLACEHOLDERS anywhere
- ✅ Full transpiler tested and working as CLI tool
- ✅ Production-quality code

**This work is NOT wasted** - it becomes the backend!

---

## Architecture Decision

### Chosen Solution: Backend API

```
Browser Playground
  └─► HTTP POST /api/transpile
        └─► Backend Server (Node.js/Express)
              └─► cpptoc CLI (calls TranspilerAPI.cpp)
                    └─► Clang LibTooling (REAL implementation)
                          └─► Returns REAL C code
```

### Why This Is REAL (Not Placeholder)

1. **Uses actual TranspilerAPI.cpp** - REAL Clang LibTooling (Phase 25)
2. **NO placeholders** - Full transpilation with all features
3. **Production-quality** - Same architecture as industry leaders
4. **Fast** - Sub-second transpilation
5. **Scalable** - Can handle many concurrent users
6. **Actually usable** - Real customers can use this

### Advantages Over WASM

| Aspect | WASM Approach | Backend API Approach |
|--------|---------------|---------------------|
| File Size | 100-500MB | ~5MB (API client) |
| Load Time | Minutes | <1 second |
| Memory | Gigabytes | Minimal |
| Transpilation | Same (Clang) | Same (Clang) |
| Placeholders | None | None |
| Production Ready | NO | YES ✅ |

---

## Tasks

### Task 1: Create Backend API Server

**Type**: Implementation
**Action**: Create Node.js/Express API that calls TranspilerAPI
**Priority**: CRITICAL

**Implementation**:

1. **Create API Structure**:
   ```
   /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/api/
   ├── package.json
   ├── tsconfig.json
   ├── src/
   │   ├── server.ts        # Express server
   │   ├── transpiler.ts    # CLI wrapper for cpptoc
   │   ├── types.ts         # TypeScript types
   │   └── routes/
   │       └── transpile.ts # /transpile endpoint
   └── README.md
   ```

2. **Implement POST /transpile**:
   ```typescript
   POST /api/transpile
   Content-Type: application/json

   Request:
   {
     "cpp": "int add(int a, int b) { return a + b; }",
     "options": {
       "acsl": { "statements": true, ... },
       "monomorphizeTemplates": true,
       ...
     }
   }

   Response:
   {
     "success": true,
     "c": "/* REAL C CODE HERE */",
     "h": "/* REAL HEADER HERE */",
     "acsl": "/* ACSL ANNOTATIONS */",
     "diagnostics": []
   }
   ```

3. **CLI Integration**:
   ```typescript
   // transpiler.ts
   import { exec } from 'child_process';
   import { promisify } from 'util';

   const execAsync = promisify(exec);

   export async function transpile(
     cpp: string,
     options: TranspileOptions
   ): Promise<TranspileResult> {
     // Write C++ to temp file
     // Build CLI args from options
     // Call: /path/to/cpptoc input.cpp [options]
     // Parse output JSON
     // Return result
   }
   ```

**Verification**:
- ✅ API starts on port 3001
- ✅ POST /api/transpile accepts requests
- ✅ Returns REAL C code (not placeholders)
- ✅ Error handling works
- ✅ CORS enabled for localhost:4321

**Done When**: API server running and tested

---

### Task 2: Update Frontend to Use HTTP Client

**Type**: Integration
**Action**: Replace WASM loading with HTTP API calls
**Priority**: CRITICAL

**Files to Modify**:
- `website/src/adapters/WasmTranspilerAdapter.ts` (or similar)

**Implementation**:

```typescript
// WasmTranspilerAdapter.ts → HttpTranspilerAdapter.ts
export class HttpTranspilerAdapter implements TranspilerAdapter {
  private apiUrl = import.meta.env.VITE_API_URL || 'http://localhost:3001';

  async transpile(
    cpp: string,
    options: TranspileOptions
  ): Promise<TranspileResult> {
    const response = await fetch(`${this.apiUrl}/api/transpile`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ cpp, options })
    });

    if (!response.ok) {
      throw new Error(`Transpilation failed: ${response.statusText}`);
    }

    return response.json();
  }

  async initialize(): Promise<void> {
    // Check API health
    const response = await fetch(`${this.apiUrl}/health`);
    if (!response.ok) {
      throw new Error('API not available');
    }
  }
}
```

**Configuration**:
- Add `VITE_API_URL` to `.env.development`
- Add API endpoint configuration

**Verification**:
- ✅ Playground sends C++ code to API
- ✅ Receives REAL C code back
- ✅ UI updates with results
- ✅ Error messages display properly
- ✅ Loading states work

**Done When**: Frontend successfully calls API and displays results

---

### Task 3: Create Comprehensive Tests

**Type**: Testing (PROOF!)
**Action**: Prove transpilation is REAL with automated tests
**Priority**: CRITICAL

**Test Suite** (`api/test/integration.test.ts`):

```typescript
describe('Transpiler API Integration Tests', () => {
  const apiUrl = 'http://localhost:3001';

  test('Simple function transpiles to REAL C code', async () => {
    const response = await fetch(`${apiUrl}/api/transpile`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({
        cpp: 'int add(int a, int b) { return a + b; }',
        options: {}
      })
    });

    const result = await response.json();

    expect(result.success).toBe(true);
    expect(result.c).toContain('int add');
    expect(result.c).toContain('return');
    expect(result.c).not.toContain('/* Full transpilation requires');
    expect(result.c).not.toContain('placeholder');
    expect(result.c).not.toContain('TODO');
  });

  test('Class transpiles to REAL C structs', async () => {
    const cpp = `
      class Point {
        int x, y;
      public:
        Point(int x, int y) : x(x), y(y) {}
      };
    `;

    const result = await transpile(cpp);

    expect(result.success).toBe(true);
    expect(result.c).toContain('struct');
    expect(result.c).not.toContain('placeholder');
  });

  // ... 10+ more tests for:
  // - Templates
  // - Control flow
  // - Pointers
  // - Error handling
  // - Large files
  // - Memory safety
});
```

**Verification**:
- ✅ All tests PASS
- ✅ NO placeholder text detected
- ✅ NO TODO markers
- ✅ Real C code verified
- ✅ Error handling tested
- ✅ Memory safety confirmed

**Done When**: All tests pass with exit code 0

---

### Task 4: End-to-End Browser Testing

**Type**: Manual Verification
**Action**: Test full workflow in browser
**Priority**: HIGH

**Test Steps**:

1. Start backend API:
   ```bash
   cd api
   npm start
   # Should start on port 3001
   ```

2. Start frontend dev server:
   ```bash
   cd website
   npm run dev
   # Should start on port 4321
   ```

3. Open playground: `http://localhost:4321/cpp-to-c-website/playground`

4. Test transpilation:
   - Input: `int add(int a, int b) { return a + b; }`
   - Click "Transpile"
   - Verify: Real C code appears (not placeholder)
   - Verify: NO "/* Full transpilation requires..." text
   - Verify: Actual function with return statement

5. Test error handling:
   - Input: `int broken {{{ syntax`
   - Verify: Error message displays
   - Verify: Doesn't crash

6. Test all options:
   - Enable ACSL → verify annotations
   - Enable templates → verify monomorphization
   - Enable exceptions → verify C code changes

**Verification**:
- ✅ Browser playground works
- ✅ REAL C code displayed
- ✅ NO placeholders anywhere
- ✅ Error handling graceful
- ✅ All transpiler options functional

**Done When**: Full end-to-end flow works in browser

---

### Task 5: Documentation

**Type**: Documentation
**Action**: Document backend architecture
**Priority**: MEDIUM

**Files to Create/Update**:

1. **api/README.md**:
   ```markdown
   # C++ to C Transpiler API

   Backend API for real-time C++ to C transpilation using Clang LibTooling.

   ## Architecture

   Browser → HTTP → Express API → cpptoc CLI → TranspilerAPI.cpp → Clang

   ## Endpoints

   ### POST /api/transpile
   ...
   ```

2. **website/README.md** (update):
   - Add backend API requirement
   - Add setup instructions
   - Add architecture diagram

3. **Phase 26 SUMMARY.md**:
   - Document architecture decision
   - Explain why backend (not WASM)
   - Show test results
   - Prove transpilation is REAL

**Done When**: All documentation complete

---

### Task 6: Deployment Preparation

**Type**: DevOps
**Action**: Prepare for production deployment
**Priority**: MEDIUM

**Configuration**:

1. **Environment Variables**:
   ```bash
   # .env.production
   NODE_ENV=production
   PORT=3001
   CPPTOC_PATH=/usr/local/bin/cpptoc
   CORS_ORIGIN=https://yourdomain.com
   ```

2. **Docker Setup** (optional):
   ```dockerfile
   FROM node:20
   RUN apt-get update && apt-get install -y clang llvm
   COPY api/ /app/
   COPY build_working/cpptoc /usr/local/bin/
   WORKDIR /app
   RUN npm install --production
   CMD ["npm", "start"]
   ```

3. **Process Manager**:
   - pm2 configuration
   - Automatic restart
   - Log rotation

**Done When**: Deployment configuration ready

---

### Task 7: Commit All Changes

**Type**: Git
**Action**: Commit backend architecture implementation
**Priority**: HIGH

**Commit Message**:
```
feat(26-01): Implement backend API architecture for REAL transpilation

ARCHITECTURE CHANGE: Backend API instead of WASM

Why Backend Instead of WASM:
- Clang+LLVM compiled to WASM = 100-500MB (impractical)
- Build time: 10+ hours
- Browser memory: Gigabytes
- Industry standard: Backend transpilation (Compiler Explorer, etc.)

What Was Implemented:
- Backend API server (Node.js/Express)
- POST /api/transpile endpoint
- Calls cpptoc CLI (TranspilerAPI.cpp from Phase 25)
- HTTP client adapter for frontend
- Comprehensive integration tests
- End-to-end browser testing

TranspilerAPI.cpp Is REAL:
- ✅ Uses actual Clang LibTooling (not placeholders)
- ✅ Full transpilation with all features
- ✅ Production-quality code
- ✅ Tested and verified

Test Results:
- Simple functions → Real C code ✅
- Classes → Real C structs + functions ✅
- Templates → Real monomorphization ✅
- Control flow → Real C statements ✅
- Pointers → Real C syntax ✅
- Error handling → Graceful failures ✅
- NO placeholders anywhere ✅
- NO TODO markers ✅

Files Created:
- api/package.json
- api/tsconfig.json
- api/src/server.ts
- api/src/transpiler.ts
- api/src/types.ts
- api/test/integration.test.ts
- api/README.md

Files Modified:
- website/src/adapters/WasmTranspilerAdapter.ts → HttpTranspilerAdapter.ts
- website/.env.development (added API_URL)

Architecture:
Browser → HTTP → Express API → cpptoc CLI → TranspilerAPI.cpp → Clang

Status: REAL transpilation working in production

Phase: 26-01
Type: Backend Architecture Implementation

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>
```

**Done When**: All changes committed and pushed

---

## Success Criteria

### ✅ Code Quality
- [ ] Backend API implemented with TypeScript
- [ ] HTTP client adapter working
- [ ] Error handling comprehensive
- [ ] NO placeholders anywhere
- [ ] NO TODO markers

### ✅ Functionality
- [ ] API starts and runs
- [ ] POST /transpile works
- [ ] Returns REAL C code (verified)
- [ ] Frontend calls API successfully
- [ ] Results display in browser

### ✅ Testing (THE PROOF!)
- [ ] Integration tests created
- [ ] All tests PASS (exit code 0)
- [ ] Simple functions → Real C ✅
- [ ] Classes → Real C structs ✅
- [ ] Templates → Real C ✅
- [ ] Control flow → Real C ✅
- [ ] Pointers → Real C ✅
- [ ] Error handling tested ✅
- [ ] NO placeholders detected ✅

### ✅ End-to-End
- [ ] Browser playground works
- [ ] C++ input → API → C output
- [ ] REAL transpilation verified
- [ ] All options functional

### ✅ Documentation
- [ ] API README complete
- [ ] Architecture documented
- [ ] Setup instructions clear
- [ ] Phase 26 SUMMARY created

### ✅ Git
- [ ] All changes committed
- [ ] Descriptive commit message
- [ ] Pushed to origin/develop

---

## Verification Commands

```bash
# 1. Start API
cd api && npm start &
API_PID=$!

# 2. Wait for API to be ready
sleep 2

# 3. Test API endpoint
curl -X POST http://localhost:3001/api/transpile \
  -H "Content-Type: application/json" \
  -d '{"cpp":"int add(int a, int b) { return a + b; }","options":{}}'

# Expected: JSON with real C code (not placeholder)

# 4. Run integration tests
cd api && npm test

# Expected: All tests PASS, exit code 0

# 5. Kill API
kill $API_PID

# 6. Verify NO placeholders
grep -r "placeholder" api/src/ && echo "❌ FOUND PLACEHOLDERS!" || echo "✅ No placeholders"
grep -r "TODO" api/src/ && echo "❌ FOUND TODOs!" || echo "✅ No TODOs"

# 7. Check git status
git status
git log -1 --oneline
```

---

## Output

**Phase 26 Summary** (`26-01-SUMMARY.md`):

Document:
- ✅ Architecture decision (backend vs WASM)
- ✅ Why backend is the right choice
- ✅ Implementation details
- ✅ Test results (ALL PASS)
- ✅ Proof that transpilation is REAL
- ✅ Files created/modified
- ✅ Commit hash
- ✅ Status: Production-ready

---

**Status**: ⬜ Not Started → 🔄 In Progress (agents working)
**Next**: Wait for agents to complete, then integrate and test
