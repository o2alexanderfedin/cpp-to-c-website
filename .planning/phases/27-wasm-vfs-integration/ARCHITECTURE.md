# Architecture: WASM Transpiler with Virtual File System

**Phase**: 27 - WASM VFS Integration
**Created**: 2025-12-22
**Type**: Architecture Design

---

## Executive Summary

**Goal**: Enable the C++ to C transpiler to run as WebAssembly by integrating a Virtual File System for header file resolution.

**Key Insight**: Clang's `runToolOnCodeWithArgs()` already has built-in VFS support through the `FileContentMappings` parameter - we don't need to build a VFS from scratch.

**User Requirement**: Support multiple header directories like normal compilers (`-I/path1 -I/path2`).

---

## Architecture Decision

### Option 1: FileContentMappings (RECOMMENDED)

Use Clang's existing `FileContentMappings` parameter to inject virtual files.

**Pros**:
- ✅ Minimal code changes (15 lines)
- ✅ Uses existing, stable Clang API
- ✅ Perfect for WASM use case
- ✅ No manual VFS lifecycle management
- ✅ Supports multiple include directories naturally

**Implementation**:
```cpp
// 1. Accept virtual files in TranspileOptions
struct TranspileOptions {
    std::vector<std::pair<std::string, std::string>> virtualFiles;
};

// 2. Build FileContentMappings
clang::tooling::FileContentMappings mappings;
for (const auto& [path, content] : options.virtualFiles) {
    mappings.push_back({path, content});
}

// 3. Pass to runToolOnCodeWithArgs
runToolOnCodeWithArgs(action, code, args, filename, toolName, pch, mappings);
```

### Option 2: Explicit llvm::vfs::InMemoryFileSystem

Create and manage VFS manually using LLVM's VFS API.

**Pros**:
- Full control over filesystem behavior
- Can customize file attributes

**Cons**:
- ❌ More complex (30+ lines)
- ❌ Manual VFS lifecycle management
- ❌ Same functionality as Option 1

**Verdict**: Not needed - Option 1 provides everything we need.

---

## Technical Design

### 1. API Changes

#### TranspilerAPI.h

Add to `TranspileOptions` struct:
```cpp
/// @brief Virtual files for in-memory compilation
/// Each pair is (file_path, file_content)
/// Example: {"/usr/include/stdio.h", "... header content ..."}
std::vector<std::pair<std::string, std::string>> virtualFiles;
```

#### TranspilerAPI.cpp

Modify `transpile()` function (lines 221-226):

**Before**:
```cpp
bool success = clang::tooling::runToolOnCodeWithArgs(
    factory.create(),
    cppSource,
    args,
    filename
);
```

**After**:
```cpp
// Build FileContentMappings from virtual files
clang::tooling::FileContentMappings virtualMappedFiles;
for (const auto& [path, content] : options.virtualFiles) {
    virtualMappedFiles.push_back({path, content});
}

// Run with virtual files
bool success = clang::tooling::runToolOnCodeWithArgs(
    factory.create(),
    cppSource,
    args,
    filename,
    "cpptoc-transpiler",  // tool name
    std::make_shared<clang::PCHContainerOperations>(),
    virtualMappedFiles  // virtual files
);
```

### 2. Multiple Header Directory Support

To support `-I/path1 -I/path2` like normal compilers:

**Approach**: Virtual files use absolute paths, include directories point to virtual locations.

**Example**:
```cpp
// Virtual files (from WASM)
virtualFiles = {
    {"/virtual/include1/stdio.h", "... content ..."},
    {"/virtual/include1/stdlib.h", "... content ..."},
    {"/virtual/include2/myheader.h", "... content ..."}
};

// Compiler args (added automatically)
args = {
    "-std=c++17",
    "-I/virtual/include1",  // First include dir
    "-I/virtual/include2",  // Second include dir
    "-fsyntax-only"
};
```

**Code** (in transpile function, before runToolOnCodeWithArgs):
```cpp
// Detect include directories from virtual files
std::set<std::string> includeDirs;
for (const auto& [path, _] : options.virtualFiles) {
    // Extract directory from path
    size_t lastSlash = path.rfind('/');
    if (lastSlash != std::string::npos) {
        includeDirs.insert(path.substr(0, lastSlash));
    }
}

// Add as -I arguments
for (const auto& dir : includeDirs) {
    args.push_back("-I" + dir);
}
```

**Alternative** (explicit include paths in options):
```cpp
// TranspileOptions
struct TranspileOptions {
    std::vector<std::pair<std::string, std::string>> virtualFiles;
    std::vector<std::string> includePaths;  // Explicit -I paths
};

// Usage
for (const auto& path : options.includePaths) {
    args.push_back("-I" + path);
}
```

### 3. WASM Integration

#### JavaScript/TypeScript Interface

```typescript
interface VirtualFile {
    path: string;
    content: string;
}

interface TranspileOptions {
    virtualFiles: VirtualFile[];
    includePaths?: string[];  // Optional explicit -I paths
    acsl?: { ... };
    cppStandard?: number;
    // ... other options
}

// Example usage
const result = transpile(cppCode, "main.cpp", {
    virtualFiles: [
        { path: "/usr/include/stdio.h", content: stdioContent },
        { path: "/usr/include/stdlib.h", content: stdlibContent },
        { path: "/myproject/myheader.h", content: myheaderContent }
    ],
    includePaths: ["/usr/include", "/myproject"],
    cppStandard: 17
});
```

#### Embind Bindings (wasm/bindings/full.cpp)

```cpp
// Add VirtualFile struct
struct VirtualFile {
    std::string path;
    std::string content;
};

EMSCRIPTEN_BINDINGS(VirtualFile) {
    value_object<VirtualFile>("VirtualFile")
        .field("path", &VirtualFile::path)
        .field("content", &VirtualFile::content);
}

// Update TranspileOptions
struct TranspileOptions {
    // ... existing fields ...
    std::vector<VirtualFile> virtualFiles;
    std::vector<std::string> includePaths;
};

EMSCRIPTEN_BINDINGS(TranspileOptions) {
    // ... existing bindings ...
    .field("virtualFiles", &TranspileOptions::virtualFiles)
    .field("includePaths", &TranspileOptions::includePaths);
}

// Transpile function maps to library
TranspileResult transpile(const std::string& cpp, const TranspileOptions& opts) {
    cpptoc::TranspileOptions libOpts;

    // Map virtual files
    for (const auto& vf : opts.virtualFiles) {
        libOpts.virtualFiles.push_back({vf.path, vf.content});
    }

    // Map include paths
    libOpts.includePaths = opts.includePaths;

    // ... map other options ...

    return cpptoc::transpile(cpp, "input.cpp", libOpts);
}
```

---

## Data Flow

```
┌─────────────────────────────────────────────────────────────┐
│ Browser / JavaScript                                        │
│                                                             │
│ User provides:                                              │
│  - C++ source code (string)                                │
│  - Header files (array of {path, content})                 │
│  - Include paths (array of strings)                        │
└──────────────────────┬──────────────────────────────────────┘
                       │
                       │ WASM boundary
                       ▼
┌─────────────────────────────────────────────────────────────┐
│ WASM Module (Embind bindings)                              │
│                                                             │
│ 1. Receive JS objects                                      │
│ 2. Convert to C++ types                                    │
│ 3. Build TranspileOptions                                  │
└──────────────────────┬──────────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────────┐
│ TranspilerAPI.cpp                                          │
│                                                             │
│ 1. Build FileContentMappings from virtualFiles            │
│ 2. Add -I flags from includePaths                         │
│ 3. Call runToolOnCodeWithArgs with mappings               │
└──────────────────────┬──────────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────────┐
│ Clang LibTooling                                           │
│                                                             │
│ 1. Creates OverlayFileSystem                               │
│ 2. Creates InMemoryFileSystem                              │
│ 3. Adds virtual files from mappings                        │
│ 4. Parses C++ code                                         │
│ 5. Resolves #include via virtual filesystem               │
│ 6. Runs transpilation                                      │
└──────────────────────┬──────────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────────┐
│ Output (returns up the stack)                              │
│                                                             │
│  - Transpiled C code                                       │
│  - Diagnostics                                             │
│  - Success/failure status                                  │
└─────────────────────────────────────────────────────────────┘
```

---

## File Organization

### Virtual File Path Conventions

**Standard headers**: `/usr/include/c++/XX/...`
```
/usr/include/c++/17/vector
/usr/include/c++/17/algorithm
/usr/include/stdio.h
/usr/include/stdlib.h
```

**User headers**: `/virtual/project/...`
```
/virtual/project/myheader.h
/virtual/project/utils.h
```

**Include paths**:
```cpp
args.push_back("-I/usr/include/c++/17");
args.push_back("-I/usr/include");
args.push_back("-I/virtual/project");
```

---

## Implementation Scope

### Phase 27-01: Core VFS Integration (Minimal)

**Scope**: 15 lines of code, 1-2 hours
- Add `virtualFiles` field to TranspileOptions
- Modify transpile() to build FileContentMappings
- Pass mappings to runToolOnCodeWithArgs
- Test with single header file

### Phase 27-02: Include Path Support

**Scope**: 10 lines of code, 1 hour
- Add `includePaths` field to TranspileOptions
- Add -I flags to compiler args
- Test with multiple include directories

### Phase 27-03: WASM Bindings Update

**Scope**: 30 lines of code, 2 hours
- Add VirtualFile Embind bindings
- Update TranspileOptions Embind bindings
- Map JavaScript objects to C++ types
- Test from JavaScript

### Phase 27-04: Standard Library Headers Bundle

**Scope**: Research + packaging, 4-6 hours
- Research: Find minimal C++ standard library headers
- Extract headers from Clang installation
- Create header bundle (JSON/compressed format)
- Load headers into virtual filesystem on WASM init
- Test C++ code with standard includes

---

## Testing Strategy

### Unit Tests (C++)

```cpp
TEST(TranspilerAPI, VirtualFileResolution) {
    cpptoc::TranspileOptions opts;
    opts.virtualFiles = {
        {"/virtual/test.h", "#define MACRO 42"},
    };

    std::string cpp = "#include \"/virtual/test.h\"\nint x = MACRO;";
    auto result = cpptoc::transpile(cpp, "test.cpp", opts);

    EXPECT_TRUE(result.success);
    EXPECT_THAT(result.c, HasSubstr("int x = 42"));
}

TEST(TranspilerAPI, MultipleIncludePaths) {
    cpptoc::TranspileOptions opts;
    opts.virtualFiles = {
        {"/include1/a.h", "int foo();"},
        {"/include2/b.h", "int bar();"},
    };
    opts.includePaths = {"/include1", "/include2"};

    std::string cpp = "#include <a.h>\n#include <b.h>";
    auto result = cpptoc::transpile(cpp, "test.cpp", opts);

    EXPECT_TRUE(result.success);
}
```

### Integration Tests (WASM)

```javascript
test('transpile with virtual headers', async () => {
    const result = await transpile(
        '#include "test.h"\nint x = MACRO;',
        'main.cpp',
        {
            virtualFiles: [
                { path: '/virtual/test.h', content: '#define MACRO 42' }
            ],
            includePaths: ['/virtual']
        }
    );

    expect(result.success).toBe(true);
    expect(result.c).toContain('int x = 42');
});
```

---

## Risks & Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| FileContentMappings doesn't support our use case | High | Tested - Clang docs confirm it works |
| Include path resolution fails | High | Use absolute paths in virtual files |
| WASM size explosion with headers | Medium | Compress headers, lazy-load if needed |
| Path normalization issues (/ vs \\) | Low | Use POSIX paths consistently |

---

## References

- [Clang LibTooling Documentation](https://clang.llvm.org/docs/LibTooling.html)
- [Clang Tooling.cpp Source](https://clang.llvm.org/doxygen/Tooling_8cpp_source.html)
- [LLVM VirtualFileSystem API](https://llvm.org/doxygen/VirtualFileSystem_8h_source.html)
- [Emscripten File System Overview](https://emscripten.org/docs/porting/files/file_systems_overview.html)
- [wasm-clang GitHub](https://github.com/binji/wasm-clang)

---

## Next Steps

1. Create 27-01-PLAN.md for core VFS integration
2. Implement and test FileContentMappings approach
3. Verify multi-file resolution works
4. Update WASM bindings
5. Bundle standard library headers
6. Integration testing with browser playground
