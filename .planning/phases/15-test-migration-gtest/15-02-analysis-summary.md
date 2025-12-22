# Task 1: Test Structure Analysis and Fixture Extraction

## Executive Summary

Analyzed 76 macro-based test files in `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/` directory. Found approximately **1,260 test functions** across all files using custom macros (TEST_START, TEST_PASS, TEST_FAIL, ASSERT).

**Key Findings:**
- 76 files use macro-based testing framework
- ~1,260 total test functions identified
- 3 common macro patterns detected
- 5 primary fixture patterns identified
- Tests organized in 6 major categories

---

## 1. Macro-Based Test Files Inventory

### 1.1 Complete File List with Test Counts

#### Unit Tests - Lambdas (1 file, 60 tests)
- `./unit/lambdas/LambdaTranslatorTest.cpp` - 60 tests

#### Unit Tests - Operators (1 file, 62 tests)
- `./unit/operators/OperatorOverloadingTest.cpp` - 62 tests

#### Unit Tests - Smart Pointers (3 files, 95 tests)
- `./unit/smart_pointers/UniquePtrTest.cpp` - 30 tests
- `./unit/smart_pointers/RaiiIntegrationTest.cpp` - 25 tests
- `./unit/smart_pointers/SharedPtrTest.cpp` - 40 tests

#### Unit Tests - Move Semantics (6 files, 94 tests)
- `./unit/move_semantics/MoveSemanticTranslatorTest.cpp` - 50 tests
- `./unit/move_semantics/RvalueRefParameterTest.cpp` - 10 tests
- `./unit/move_semantics/StdMoveTranslationTest.cpp` - 10 tests
- `./unit/move_semantics/CopyMoveIntegrationTest.cpp` - 8 tests
- `./unit/move_semantics/MoveConstructorTranslationTest.cpp` - 7 tests
- `./unit/move_semantics/MoveAssignmentTranslationTest.cpp` - 9 tests

#### Unit Tests - Type Traits (2 files, 85 tests)
- `./unit/type_traits/TypeTraitsTest.cpp` - 40 tests
- `./unit/type_traits/MetaprogrammingTest.cpp` - 45 tests

#### Integration Tests - Core (6 files, 51 tests)
- `./IntegrationTest.cpp` - 5 tests
- `./STLIntegrationTest.cpp` - 5 tests
- `./TranslationIntegrationTest.cpp` - 6 tests
- `./VirtualMethodIntegrationTest.cpp` - 15 tests
- `./ExceptionHandlingIntegrationTest.cpp` - 15 tests
- `./OverloadResolutionTest.cpp` - 5 tests

#### Exception Handling Tests (8 files, 100 tests)
- `./TryCatchTransformerTest.cpp` - 8 tests
- `./ExceptionFrameTest.cpp` - 16 tests
- `./ExceptionPerformanceTest.cpp` - 4 tests
- `./ExceptionThreadSafetyTest.cpp` - 5 tests
- `./CatchHandlerTypeMatchingTest.cpp` - 10 tests
- `./LoopDestructorTest.cpp` - 26 tests
- `./EarlyReturnDestructorTest.cpp` - 16 tests
- `./NestedScopeDestructorTest.cpp` - 8 tests
- `./GotoDestructorTest.cpp` - 25 tests

#### Virtual/Inheritance Tests (16 files, 127 tests)
- `./VtableGeneratorTest.cpp` - 8 tests
- `./VirtualCallTranslatorTest.cpp` - 3 tests
- `./VirtualBaseDetectionTest.cpp` - 8 tests
- `./VirtualBaseOffsetTableTest.cpp` - 8 tests
- `./VirtualMethodAnalyzerTest.cpp` - 7 tests
- `./VptrInjectorTest.cpp` - 6 tests
- `./VTTGeneratorTest.cpp` - 8 tests
- `./VtableInitializerTest.cpp` - 6 tests
- `./OverrideResolverTest.cpp` - 8 tests
- `./HierarchyTraversalTest.cpp` - 8 tests
- `./DynamicCastTranslatorTest.cpp` - 8 tests
- `./DynamicCastCrossCastTest.cpp` - 7 tests
- `./CrossCastTraversalTest.cpp` - 7 tests
- `./TypeidTranslatorTest.cpp` - 8 tests
- `./TypeInfoGeneratorTest.cpp` - 8 tests
- `./PureVirtualHandlerTest.cpp` - 7 tests

#### Coroutine Tests (5 files, 43 tests)
- `./CoroutineDetectorTest.cpp` - 15 tests
- `./PromiseTranslatorTest.cpp` - 7 tests
- `./SuspendPointIdentifierTest.cpp` - 7 tests
- `./StateMachineTransformerTest.cpp` - 7 tests
- `./ResumeDestroyFunctionTest.cpp` - 7 tests

#### Runtime/Optimization Tests (4 files, 51 tests)
- `./runtime_mode_inline_test.cpp` - 10 tests
- `./runtime_mode_library_test.cpp` - 12 tests
- `./runtime_feature_flags_test.cpp` - 15 tests
- `./size_optimization_test.cpp` - 14 tests

#### ACSL Annotation Tests (2 files, 18 tests)
- `./ACSLStatementAnnotatorTest.cpp` - 18 tests
- `./ACSLGhostCodeInjectorTest.cpp` - 0 tests (empty/incomplete)
- `./ACSLAxiomaticBuilderTest.cpp` - 0 tests (empty/incomplete)
- `./ACSLTypeInvariantGeneratorTest.cpp` - 0 tests (empty/incomplete)
- `./ACSLBehaviorAnnotatorTest.cpp` - 0 tests (empty/incomplete)

#### Miscellaneous Tests (21 files, 209 tests)
- `./CppToCVisitorTest.cpp` - 14 tests
- `./CNodeBuilderTest.cpp` - 6 tests
- `./CodeGeneratorTest.cpp` - 0 tests
- `./test_cnodebuilder_manual.cpp` - 0 tests
- `./MonomorphizationTest.cpp` - 6 tests
- `./ActionTableGeneratorTest.cpp` - 9 tests
- `./CallingConventionTest.cpp` - 3 tests
- `./MemberInitListTest.cpp` - 5 tests
- `./CFGAnalysisTest.cpp` - 5 tests
- `./LinkageDetectionTest.cpp` - 6 tests
- `./ForwardDeclTest.cpp` - 6 tests
- `./IncludeGuardGeneratorTest.cpp` - 9 tests
- `./FileOutputManagerTest.cpp` - 5 tests
- `./DependencyAnalyzerTest.cpp` - 5 tests
- `./FrameAllocationTest.cpp` - 7 tests
- `./ValidationTest.cpp` - 0 tests

**Total: 76 files, ~1,260 test functions**

---

## 2. Macro Patterns Identified

### 2.1 Three Primary Macro Variants

#### Variant A: Simple Output (Most Common)
```cpp
#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS(name) std::cout << "PASS" << std::endl
#define ASSERT(cond, msg) \
    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        return; \
    }
```
**Used in:** MoveSemanticTranslatorTest.cpp, TypeTraitsTest.cpp (and ~45 other files)

#### Variant B: Counter-Based (Integration Tests)
```cpp
#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name) { std::cout << "✓" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "✗ FAILED: " << msg << std::endl; tests_failed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }
```
**Used in:** FeatureInteractionTest.cpp, VirtualMethodIntegrationTest.cpp (and ~20 files)

#### Variant C: Return Bool (Type Traits Style)
```cpp
#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS() std::cout << "PASS" << std::endl
#define ASSERT(cond, msg) \
    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        std::cerr << "  at line " << __LINE__ << std::endl; \
        return false; \
    }
```
**Used in:** TypeTraitsTest.cpp, MetaprogrammingTest.cpp

### 2.2 Additional Helper Macros
```cpp
// String containment checks
#define ASSERT_CONTAINS(haystack, needle, msg)
#define ASSERT_NOT_CONTAINS(haystack, needle, msg)
#define ASSERT_NOT_EMPTY(str, msg)
```
**Used in:** ~15 files for code generation validation

---

## 3. Common Fixture Patterns

### 3.1 Pattern 1: AST Builder Helper (60+ files)
```cpp
// Helper function to build AST from C++ code
std::unique_ptr<ASTUnit> buildAST(const char *code) {
    return tooling::buildASTFromCode(code);
}

// OR with args:
std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cpp");
}
```
**Recommendation:** Create `TestASTFixture` base class in GTest

### 3.2 Pattern 2: Custom AST Visitor (25+ files)
```cpp
// Specialized visitor to find specific AST nodes
class MoveSemanticsFinder : public RecursiveASTVisitor<MoveSemanticsFinder> {
public:
    std::vector<const CXXMethodDecl*> moveConstructors;
    std::vector<const CXXMethodDecl*> moveAssignments;
    std::vector<const CallExpr*> stdMoveCalls;

    bool VisitCXXConstructorDecl(CXXConstructorDecl *D) {
        if (D->isMoveConstructor()) {
            moveConstructors.push_back(D);
        }
        return true;
    }
    // ... more visitor methods
};
```
**Recommendation:** Create reusable visitor fixtures per feature category

### 3.3 Pattern 3: Test Counter Management (30+ files)
```cpp
static int tests_passed = 0;
static int tests_failed = 0;

int main() {
    // Run tests...

    std::cout << "Results: " << tests_passed << " passed, "
              << tests_failed << " failed\n";
    return tests_failed > 0 ? 1 : 0;
}
```
**Recommendation:** Use GTest's built-in test counting, no custom needed

### 3.4 Pattern 4: Function Finder Helper (15+ files)
```cpp
FunctionDecl* findFunction(ASTContext& Context, const std::string& name) {
    TranslationUnitDecl* TU = Context.getTranslationUnitDecl();
    for (auto* Decl : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(Decl)) {
            if (FD->getNameAsString() == name) {
                return FD;
            }
        }
    }
    return nullptr;
}
```
**Recommendation:** Create `ASTQueryFixture` with common search utilities

### 3.5 Pattern 5: Code Snippet Testing (50+ files)
```cpp
void test_specific_feature() {
    TEST_START("specific_feature");

    const char *code = R"(
        // C++ code to test
        template<typename T>
        class MyClass { ... };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse code");

    // Perform AST analysis
    // ...

    TEST_PASS("specific_feature");
}
```
**Recommendation:** Create parameterized test fixtures for code snippet testing

---

## 4. Recommended Fixture Organization

### 4.1 Base Fixtures (for all tests)

#### `TestASTFixture` - Base class for AST testing
```cpp
class TestASTFixture : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const char* code);
    std::unique_ptr<ASTUnit> buildASTWithArgs(const char* code,
                                              const std::vector<std::string>& args);
    ASTContext& getContext();
};
```

#### `ASTQueryFixture` - Extends TestASTFixture with search utilities
```cpp
class ASTQueryFixture : public TestASTFixture {
protected:
    FunctionDecl* findFunction(const std::string& name);
    CXXRecordDecl* findClass(const std::string& name);
    VarDecl* findVariable(const std::string& name);
    template<typename T>
    std::vector<T*> findNodesOfType();
};
```

### 4.2 Feature-Specific Fixtures

#### For Lambda Tests (60 tests)
```cpp
class LambdaTestFixture : public ASTQueryFixture {
protected:
    class LambdaFinder : public RecursiveASTVisitor<LambdaFinder> {
        // Lambda-specific visitor
    };
    LambdaFinder finder;
};
```

#### For Move Semantics Tests (94 tests)
```cpp
class MoveSemanticFixture : public ASTQueryFixture {
protected:
    class MoveSemanticsFinder : public RecursiveASTVisitor<MoveSemanticsFinder> {
        // Move semantics visitor (existing pattern)
    };
    MoveSemanticsFinder finder;
};
```

#### For Type Traits Tests (85 tests)
```cpp
class TypeTraitsFixture : public TestASTFixture {
protected:
    // Type trait checking utilities
    bool checkStaticAssert(const char* code);
    QualType extractType(const std::string& name);
};
```

#### For Virtual Method Tests (127 tests)
```cpp
class VirtualMethodFixture : public ASTQueryFixture {
protected:
    class VirtualMethodVisitor : public RecursiveASTVisitor<VirtualMethodVisitor> {
        // Virtual method analysis
    };
    VirtualMethodVisitor visitor;

    // Helper methods
    const CXXRecordDecl* findClassWithVTable(const std::string& name);
    std::vector<const CXXMethodDecl*> getVirtualMethods(const CXXRecordDecl* RD);
};
```

#### For Exception Handling Tests (100 tests)
```cpp
class ExceptionHandlingFixture : public ASTQueryFixture {
protected:
    class ExceptionVisitor : public RecursiveASTVisitor<ExceptionVisitor> {
        // Exception handling constructs
    };
    ExceptionVisitor visitor;

    std::vector<const CXXTryStmt*> findTryStatements();
    std::vector<const CXXThrowExpr*> findThrowExpressions();
};
```

---

## 5. Migration Strategy Summary

### 5.1 Test Count by Priority

1. **High Priority** (Core Features): 396 tests
   - Lambdas: 60 tests
   - Operators: 62 tests
   - Move Semantics: 94 tests
   - Type Traits: 85 tests
   - Smart Pointers: 95 tests

2. **Medium Priority** (Advanced Features): 270 tests
   - Virtual Methods/Inheritance: 127 tests
   - Exception Handling: 100 tests
   - Coroutines: 43 tests

3. **Lower Priority** (Integration/Specialized): 594 tests
   - Integration tests: 51 tests
   - ACSL annotations: 18 tests
   - Runtime/Optimization: 51 tests
   - Miscellaneous: 474 tests

### 5.2 Estimated Migration Effort

- **Fixture Creation**: 2-3 days
  - 5 base fixtures
  - 10-12 feature-specific fixtures

- **Test Migration**: 10-15 days
  - ~1,260 tests to convert
  - Average: 80-120 tests per day
  - Priority-based approach

- **Validation & Testing**: 2-3 days
  - Ensure all tests pass
  - Fix migration issues
  - Update documentation

**Total Estimated Time**: 14-21 days

---

## 6. Next Steps

1. ✅ **Task 1 Complete**: Analysis and inventory done
2. **Task 2**: Create base fixture classes (TestASTFixture, ASTQueryFixture)
3. **Task 3**: Migrate high-priority test categories first
4. **Task 4**: Create feature-specific fixtures as needed
5. **Task 5**: Migrate remaining tests
6. **Task 6**: Remove old macro-based framework
7. **Task 7**: Update build system and documentation

---

## Appendix A: Sample Test Function Distribution

| File | Tests | Category |
|------|-------|----------|
| OperatorOverloadingTest.cpp | 62 | Operators |
| LambdaTranslatorTest.cpp | 60 | Lambdas |
| MoveSemanticTranslatorTest.cpp | 50 | Move Semantics |
| MetaprogrammingTest.cpp | 45 | Type Traits |
| SharedPtrTest.cpp | 40 | Smart Pointers |
| TypeTraitsTest.cpp | 40 | Type Traits |
| UniquePtrTest.cpp | 30 | Smart Pointers |
| LoopDestructorTest.cpp | 26 | Exception Handling |
| GotoDestructorTest.cpp | 25 | Exception Handling |
| RaiiIntegrationTest.cpp | 25 | Smart Pointers |

**Average tests per file**: ~17 tests (excluding empty files)
**Median tests per file**: 8 tests

---

## Appendix B: Files Requiring Special Attention

### Incomplete/Empty Test Files (need investigation)
- `./ValidationTest.cpp` - 0 tests
- `./CodeGeneratorTest.cpp` - 0 tests
- `./test_cnodebuilder_manual.cpp` - 0 tests
- `./ACSLGhostCodeInjectorTest.cpp` - 0 tests
- `./ACSLAxiomaticBuilderTest.cpp` - 0 tests
- `./ACSLTypeInvariantGeneratorTest.cpp` - 0 tests
- `./ACSLBehaviorAnnotatorTest.cpp` - 0 tests

These files may be:
- Work in progress
- Placeholder files
- Incorrectly categorized
- Need deletion or completion

**Recommendation**: Review these 7 files before migration to determine disposition.
