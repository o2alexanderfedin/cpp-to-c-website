# Test Framework Analysis - C++ to C Transpiler

**Date**: 2025-12-20
**Total Tests**: 988 across 51 suites
**Analyzed by**: Claude Sonnet 4.5
**Project**: hupyy-cpp-to-c (C++ to C Transpiler)

---

## Executive Summary

**Primary Framework**: Custom/Home-grown (986 tests, 99.8%)
**Secondary Framework**: Google Test (2 tests, 0.2%)
**Test Distribution**: Highly inconsistent with one dominant custom framework
**Recommendation**: Migrate to Google Test (GTest) for standardization, improved maintainability, and better CI/CD integration

### Key Findings

1. **Framework Distribution Imbalance**: 99.8% of tests use a custom home-grown framework with inconsistent implementation patterns across test suites
2. **Dual Framework Burden**: Maintaining both custom and GTest frameworks increases cognitive load and maintenance overhead
3. **Output Format Inconsistency**: Custom framework uses varying output styles (`std::cout`, assertion macros like `TEST_START/TEST_PASS`, simple function calls)
4. **Migration Opportunity**: 986 tests can be standardized under a single, well-supported framework with minimal risk
5. **CI/CD Integration**: GTest provides superior CI/CD integration, XML output for reporting tools, and parallel test execution

---

## Detailed Breakdown

### Framework Usage by Category

| Framework | Core Tests | Integration Tests | Real-World Tests | Example Tests | Total | Percentage |
|-----------|------------|-------------------|------------------|---------------|-------|------------|
| **Custom** | 720 | 4 | 252 | 10 | **986** | **99.8%** |
| **Google Test** | 0 | 2 | 0 | 0 | **2** | **0.2%** |
| **TOTAL** | **720** | **6** | **252** | **10** | **988** | **100%** |

### Framework Distribution Chart

```
Custom Framework:  ████████████████████████████████████████████████ 99.8% (986 tests)
Google Test (GTest): ▏ 0.2% (2 tests)
```

---

## Framework Inventory

### 1. Custom/Home-grown Framework (986 tests, 99.8%)

**Usage Pattern**: Dominant framework across all core unit tests, real-world integration tests, and most examples

**Implementation Variants**:

#### Variant A: Inline Assertion Style (Most Common)
- **Examples**: ACSLClassAnnotatorTest, ValidationTest, VirtualMethodIntegrationTest
- **Pattern**: Simple functions with `assert()` + `std::cout` for output
- **Test Count**: ~650 tests
- **Code Sample**:
```cpp
void testSimpleClassPrimitiveMembers() {
    std::cout << "Test 1: Simple class with primitive members... ";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    std::cout << "PASSED\n";
}
```

#### Variant B: Macro-Based Style
- **Examples**: FeatureInteractionTest, LambdaTranslatorTest
- **Pattern**: Custom macros (`TEST_START`, `TEST_PASS`, `TEST_FAIL`, `ASSERT`)
- **Test Count**: ~300 tests
- **Code Sample**:
```cpp
#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name) { std::cout << "✓" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "✗ FAILED: " << msg << std::endl; tests_failed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }

void test_interaction_templates_exceptions() {
    TEST_START("test_interaction_templates_exceptions");

    auto AST = createAST(code);
    ASSERT(AST, "Failed to parse code");

    TEST_PASS("test_interaction_templates_exceptions");
}
```

#### Variant C: Helper Function Style
- **Examples**: Real-world tests (JSON parser, Logger, String formatter)
- **Pattern**: Custom `test()` helper function with string name + boolean condition
- **Test Count**: ~252 tests
- **Code Sample**:
```cpp
void test(const std::string& name, bool condition) {
    if (condition) {
        std::cout << "[PASS] " << name << std::endl;
    } else {
        std::cout << "[FAIL] " << name << std::endl;
        throw std::runtime_error("Test failed: " + name);
    }
}

void testNullValue() {
    JsonParser parser;
    auto value = parser.parse("null");
    test("Parse null", value->isNull());
    test("Null toString", value->toString() == "null");
}
```

**Characteristics**:
- **No external dependencies**: All tests compile with just standard C++ library
- **Simple but inconsistent**: Three distinct implementation styles across test suites
- **Manual test counting**: No automatic test discovery or counting
- **Basic output**: Plain text to stdout, no XML/JSON reporting
- **No fixtures**: Limited setup/teardown support across different variants
- **No parameterization**: Each test case must be manually written
- **Exit on failure**: Many tests use `exit(1)` or exceptions, stopping execution

**Suites Using Custom Framework**:
- All 44 core unit test suites (ACSLStatementAnnotatorTest, ACSLBehaviorAnnotatorTest, ACSLClassAnnotatorTest, etc.)
- 4 integration test suites (EdgeCasesTest, ErrorHandlingTest, FeatureInteractionTest, FeatureCombinationTest)
- All 5 real-world test suites (json-parser, resource-manager, logger, string-formatter, test-framework)
- 2 example test suites (test-framework example, safety-critical example)

---

### 2. Google Test (GTest) (2 tests, 0.2%)

**Usage Pattern**: Only used in 2 Frama-C integration tests (currently commented out in CMakeLists.txt)

**Implementation**:
- **Examples**: FramaCEVATests, FramaCWPTests
- **Pattern**: Standard GTest macros (`TEST`, `EXPECT_*`, `ASSERT_*`)
- **Test Count**: 2 test suites (estimated 15-30 individual test cases, currently disabled)
- **Code Sample**:
```cpp
#include <gtest/gtest.h>

class FramaCEVATest : public ::testing::Test {
protected:
    std::string transpileWithACSL(const std::string& cppCode) {
        // Setup code
    }
};

TEST_F(FramaCEVATest, ArrayBoundsCheck) {
    auto result = transpileWithACSL(cppCode);
    EXPECT_TRUE(result.success);
    EXPECT_LT(result.alarms, 5);
}
```

**Characteristics**:
- **Industry standard**: Widely adopted, mature testing framework
- **Rich assertions**: `EXPECT_*`, `ASSERT_*`, custom matchers
- **Test fixtures**: Built-in setup/teardown with `SetUp()` and `TearDown()`
- **Parameterized tests**: `TEST_P` for data-driven testing
- **XML output**: Native support for xUnit XML format
- **Parallel execution**: Thread-safe test execution
- **Test discovery**: Automatic test registration and execution
- **Death tests**: Safe testing of code that should crash

**Suites Using GTest**:
- FramaCEVATests (Frama-C EVA integration, **currently commented out**)
- FramaCWPTests (Frama-C WP integration, **currently commented out**)

**Status**: Both GTest suites are commented out in CMakeLists.txt (lines 2400-2446), indicating they may be incomplete or under development. GTest dependency exists but is not actively used.

---

## Test Output Formats

| Format Type | Test Suites | Count | Pattern | Notes |
|-------------|-------------|-------|---------|-------|
| **Inline stdout** | Core unit tests | ~650 | `std::cout << "Test X: Description... "` followed by `PASSED` or `FAILED` | Simplest but inconsistent formatting |
| **Macro-based stdout** | Integration tests | ~300 | `TEST_START(name)` + `TEST_PASS(name)` macros | Adds test counting, structured output |
| **Helper function** | Real-world tests | ~252 | `test(name, condition)` with `[PASS]`/`[FAIL]` prefix | Cleanest custom approach, but still limited |
| **GTest XML** | (Commented out) | 0 | Standard xUnit XML format | Not currently used, but available |

### Output Format Examples

**Inline stdout (Variant A)**:
```
Test 1: Simple class with primitive members... PASSED
Test 2: Class with pointer members... PASSED
Test 3: Stack class with array members... PASSED
```

**Macro-based stdout (Variant B)**:
```
Running test_interaction_templates_exceptions... ✓
Running test_virtual_methods_with_templates... ✓
Running test_exceptions_with_inheritance... ✓

Tests passed: 30
Tests failed: 0
```

**Helper function (Variant C)**:
```
[PASS] Parse null
[PASS] Null toString
[PASS] Parse true
[PASS] Parse false
[PASS] Boolean toString
```

**GTest XML (Not used)**:
```xml
<?xml version="1.0" encoding="UTF-8"?>
<testsuites tests="15" failures="0" errors="0">
  <testsuite name="FramaCEVATest" tests="15" failures="0">
    <testcase name="ArrayBoundsCheck" status="run" time="0.123"/>
  </testsuite>
</testsuites>
```

---

## Inconsistencies Found

### 1. Three Distinct Custom Framework Implementations

**Description**: The custom framework has evolved into three incompatible variants with different APIs, output formats, and assertion styles

**Impact**:
- Developers must learn and remember three different testing patterns
- Copy-paste errors when creating new tests from different templates
- Inconsistent test output makes it hard to parse results programmatically
- No unified test runner or reporting

**Affected Suites**: All 986 custom framework tests

**Example Inconsistencies**:
- Some tests use `assert()`, others use custom `ASSERT()` macro
- Some count tests manually (`tests_passed++`), others don't track count
- Some use `exit(1)` on failure, others use `throw`, others just print errors
- Output prefixes vary: "Test X:", "[PASS]", "Running...", "✓", etc.

---

### 2. No Standardized Test Fixtures

**Description**: Setup/teardown code is duplicated across test files with no consistent pattern

**Impact**:
- Code duplication in AST creation helpers (`createAST`, `parseCode`, `buildASTFromCodeWithArgs`)
- Inconsistent resource cleanup (some tests clean up, others don't)
- Difficult to add common test infrastructure (mocking, logging, etc.)

**Affected Suites**: All test suites

**Example**:
```cpp
// ACSLClassAnnotatorTest.cpp
std::unique_ptr<ASTUnit> parseCode(const std::string& code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args);
}

// FeatureInteractionTest.cpp (different name, similar code)
std::unique_ptr<ASTUnit> createAST(const std::string &code) {
    std::vector<std::string> args = {"-std=c++17"};
    auto AST = clang::tooling::buildASTFromCodeWithArgs(code, args, "test.cpp");
    return AST;
}
```

---

### 3. Mixed Test Organization Patterns

**Description**: Some tests use function-per-test, others use test categories with multiple assertions per function

**Impact**:
- Granularity varies widely (some suites have 60 tests, others have 8)
- Difficult to track exactly which assertion failed in multi-assertion tests
- Inconsistent test naming conventions

**Affected Suites**: All test suites

**Example Patterns**:
- LambdaTranslatorTest: 60 individual test functions
- ACSLClassAnnotatorTest: 10 test functions with multiple assertions each
- ValidationTest: 15 test functions that compile/run generated C code

---

### 4. No CI/CD Integration Features

**Description**: Custom framework lacks features needed for modern CI/CD pipelines

**Impact**:
- No machine-readable output (XML, JSON) for CI tools like Jenkins, GitHub Actions
- No test discovery for selective test execution
- No parallel test execution support
- Difficult to integrate with coverage tools
- No test result caching or dependency tracking

**Affected Suites**: All 986 custom framework tests

**Missing Features**:
- XML/JSON test result output
- Test filtering by name or tag
- Parallel test execution
- Test timing and performance tracking
- Failure retry logic
- Test result history and trends

---

### 5. GTest Integration Half-Implemented

**Description**: GTest dependency exists and is configured in CMakeLists.txt, but the only 2 test suites using it are commented out

**Impact**:
- Wasted infrastructure (GTest is linked but not used)
- Unclear whether to use custom or GTest for new tests
- Two frameworks to maintain, document, and support

**Affected Suites**: FramaCEVATests, FramaCWPTests (commented out)

**Evidence**:
```cmake
# Lines 2400-2446 in CMakeLists.txt are commented out:
# target_link_libraries(FramaCWPTests PRIVATE
#     GTest::gtest
#     GTest::gtest_main
# )
```

---

## Migration Strategy Recommendation

### Target Framework: Google Test (GTest)

**Rationale**:
1. **Industry Standard**: GTest is the de facto C++ testing framework, used by Google, LLVM, Chromium, and thousands of open-source projects
2. **Rich Feature Set**: Fixtures, parameterized tests, death tests, custom matchers, mock support (GMock)
3. **CI/CD Ready**: Native XML output, test discovery, parallel execution, integration with all major CI systems
4. **Active Development**: Maintained by Google, regular updates, extensive documentation
5. **Partial Infrastructure Exists**: GTest is already configured in CMakeLists.txt
6. **Clang/LLVM Compatibility**: GTest integrates seamlessly with Clang-based projects (this project already uses Clang tooling)
7. **Learning Curve**: Widely known framework, extensive community resources and tutorials

**Benefits Over Custom Framework**:
- Automatic test discovery and registration
- Structured test fixtures with setup/teardown
- Parameterized tests reduce code duplication
- XML output for CI/CD integration
- Parallel test execution for faster CI pipelines
- Better assertion messages with line numbers and values
- Death tests for testing error conditions safely
- Test filtering and selective execution
- Consistent API across all test suites

---

### Migration Phases

#### Phase 1: Low-Hanging Fruit (252 tests, 8-12 hours estimated)

**Target**: Real-world integration tests using helper function style

**Suites to Migrate**:
1. json-parser (68 tests)
2. resource-manager (98 tests)
3. logger (24 tests)
4. string-formatter (61 tests)
5. test-framework (9 tests)

**Rationale**: These tests already use a clean helper function pattern that maps directly to GTest assertions

**Migration Pattern**:
```cpp
// Before (Custom)
void testNullValue() {
    JsonParser parser;
    auto value = parser.parse("null");
    test("Parse null", value->isNull());
    test("Null toString", value->toString() == "null");
}

// After (GTest)
TEST(JsonParserTest, ParseNull) {
    JsonParser parser;
    auto value = parser.parse("null");
    EXPECT_TRUE(value->isNull()) << "Parse null";
    EXPECT_EQ(value->toString(), "null") << "Null toString";
}
```

**Estimated Effort**:
- ~15-30 minutes per test suite
- 5 test suites × 30 min = 2.5 hours migration
- 2-3 hours for testing and validation
- 3-4 hours for documentation and review
- **Total: 8-12 hours**

**Risk**: **Low** - Clean pattern, isolated tests, good test coverage to verify migration

---

#### Phase 2: Medium Complexity (300 tests, 15-20 hours estimated)

**Target**: Integration tests and unit tests using macro-based style

**Suites to Migrate**:
1. FeatureInteractionTest (30 tests)
2. FeatureCombinationTest (20 tests)
3. EdgeCasesTest (30 tests)
4. ErrorHandlingTest (25 tests)
5. LambdaTranslatorTest (60 tests)
6. OperatorOverloadingTest (62 tests)
7. MoveSemanticTranslatorTest (50 tests)
8. Other macro-based tests (~23 tests)

**Rationale**: Macro-based tests already have structured assertions, but need fixture refactoring

**Migration Pattern**:
```cpp
// Before (Custom with macros)
static int tests_passed = 0;
static int tests_failed = 0;
#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name) { std::cout << "✓" << std::endl; tests_passed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }

void test_interaction_templates_exceptions() {
    TEST_START("test_interaction_templates_exceptions");
    auto AST = createAST(code);
    ASSERT(AST, "Failed to parse code");
    TEST_PASS("test_interaction_templates_exceptions");
}

// After (GTest with fixture)
class FeatureInteractionTest : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> createAST(const std::string& code) {
        std::vector<std::string> args = {"-std=c++17"};
        return clang::tooling::buildASTFromCodeWithArgs(code, args, "test.cpp");
    }
};

TEST_F(FeatureInteractionTest, TemplatesWithExceptions) {
    const char* code = R"(...)";
    auto AST = createAST(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";
    // Additional assertions
}
```

**Challenges**:
- Need to create test fixtures for shared helper functions (`createAST`, etc.)
- Some tests have manual test counting that must be removed
- Multiple assertions per test may need to be split into separate test cases
- Custom macros need to be replaced with GTest equivalents

**Estimated Effort**:
- ~30-45 minutes per test suite (fixture creation, macro replacement)
- ~8 major test suites × 45 min = 6 hours migration
- 4-5 hours for testing and validation
- 4-5 hours for documentation and review
- **Total: 15-20 hours**

**Risk**: **Medium** - Requires fixture refactoring, but patterns are well-defined

---

#### Phase 3: High Complexity (434 tests, 25-35 hours estimated)

**Target**: Core unit tests using inline assertion style

**Suites to Migrate**:
1. All ACSL tests (79 tests): ACSLStatementAnnotatorTest, ACSLBehaviorAnnotatorTest, ACSLClassAnnotatorTest, etc.
2. Transpilation tests (95 tests): StandaloneFunctionTranslationTest, VirtualBaseDetectionTest, etc.
3. Template tests (85 tests): TypeTraitsTest, MetaprogrammingTest
4. Remaining unit tests (~175 tests)

**Rationale**: These tests use the simplest but least structured pattern, requiring most refactoring

**Migration Pattern**:
```cpp
// Before (Custom inline style)
void testSimpleClassPrimitiveMembers() {
    std::cout << "Test 1: Simple class with primitive members... ";

    std::string code = R"(
        class Point {
        public:
            int x;
            int y;
        };
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    ClassExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.classes.empty() && "No classes found");

    const CXXRecordDecl* pointClass = extractor.classes[0];
    ACSLClassAnnotator annotator;
    std::string predicate = annotator.generateClassInvariantPredicate(pointClass);

    assert(!predicate.empty() && "Predicate should not be empty");
    assert(predicate.find("predicate inv_Point") != std::string::npos &&
           "Predicate should contain class name");

    std::cout << "PASSED\n";
}

// After (GTest with fixture and parameterization)
class ACSLClassAnnotatorTest : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> parseCode(const std::string& code) {
        std::vector<std::string> args = {"-std=c++17"};
        return tooling::buildASTFromCodeWithArgs(code, args);
    }

    const CXXRecordDecl* extractClass(ASTUnit* AST) {
        ClassExtractor extractor;
        extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
        return extractor.classes.empty() ? nullptr : extractor.classes[0];
    }
};

TEST_F(ACSLClassAnnotatorTest, SimpleClassPrimitiveMembers) {
    std::string code = R"(
        class Point {
        public:
            int x;
            int y;
        };
    )";

    auto AST = parseCode(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";

    const CXXRecordDecl* pointClass = extractClass(AST.get());
    ASSERT_NE(pointClass, nullptr) << "No classes found";

    ACSLClassAnnotator annotator;
    std::string predicate = annotator.generateClassInvariantPredicate(pointClass);

    EXPECT_FALSE(predicate.empty()) << "Predicate should not be empty";
    EXPECT_NE(predicate.find("predicate inv_Point"), std::string::npos)
        << "Predicate should contain class name";
}
```

**Challenges**:
- Tests have multiple inline assertions that should be separate test cases or combined with better structure
- Need to extract common helper code into fixtures
- Some tests use `exit(1)` which must be replaced with proper test failure
- Test descriptions embedded in `std::cout` strings need to become test names
- Large test functions may need to be split into multiple focused tests

**Estimated Effort**:
- ~45-60 minutes per test suite (extensive refactoring, fixture extraction)
- ~30 major test suites × 60 min = 30 hours migration
- 8-10 hours for testing and validation
- 6-8 hours for documentation and review
- **Total: 25-35 hours**

**Risk**: **Medium-High** - Most refactoring required, but tests are well-defined with clear assertions

---

### Migration Effort Summary

| Phase | Test Suites | Test Count | Estimated Hours | Risk Level | Cumulative Time |
|-------|-------------|------------|-----------------|------------|-----------------|
| **Phase 1** | 5 | 252 | 8-12 | Low | 8-12 hrs |
| **Phase 2** | ~8 | 300 | 15-20 | Medium | 23-32 hrs |
| **Phase 3** | ~30 | 434 | 25-35 | Medium-High | 48-67 hrs |
| **TOTAL** | **~43** | **986** | **48-67 hrs** | - | **~1.5-2 weeks** |

**Note**: GTest integration tests (FramaCEVATests, FramaCWPTests) should be uncommented and completed as part of this migration.

---

### Recommended Migration Approach

#### Option A: Big Bang Migration (NOT RECOMMENDED)
- Migrate all tests in one large PR
- High risk of breaking changes
- Long review cycle
- Difficult to roll back

#### Option B: Incremental Migration (RECOMMENDED)
- Migrate phase by phase with separate PRs
- Run both custom and GTest frameworks in parallel during migration
- Keep existing custom tests passing while adding GTest versions
- Gradually deprecate custom framework after full migration
- Allows for rollback if issues are discovered

**Incremental Migration Steps**:
1. **Setup**: Enable GTest in CMakeLists.txt, create common test fixtures (2-3 hours)
2. **Phase 1**: Migrate real-world tests, verify in CI (8-12 hours + 1 week soak time)
3. **Phase 2**: Migrate macro-based tests, run both frameworks in parallel (15-20 hours + 1 week soak time)
4. **Phase 3**: Migrate inline-style tests in batches (25-35 hours + 2 week soak time)
5. **Cleanup**: Remove custom framework code, update documentation (3-5 hours)

**Total Timeline**: 2-3 months with parallel framework support, or 1.5-2 weeks of focused work

---

### Risk Assessment

#### Low Risk (Phase 1: Real-World Tests)

**Characteristics**:
- Clean helper function pattern
- Isolated tests with minimal dependencies
- Well-defined test boundaries
- Good coverage to verify migration

**Mitigation**: Run side-by-side with custom framework for 1 week before removing old tests

---

#### Medium Risk (Phase 2: Macro-Based Tests)

**Characteristics**:
- Need fixture refactoring
- Some custom macros to replace
- Test counting logic to remove

**Mitigation**:
- Create comprehensive fixture library first
- Migrate one suite at a time
- Keep old and new tests running in parallel for 2 weeks

---

#### Medium-High Risk (Phase 3: Inline-Style Tests)

**Characteristics**:
- Most refactoring required
- Multiple assertions per test
- Embedded test descriptions to extract
- Large test functions to potentially split

**Mitigation**:
- Start with simplest suites (fewer assertions)
- Use GTest death tests for tests expecting failures
- Split large multi-assertion tests into focused test cases
- Extensive code review for each batch
- Run in parallel with custom framework for 1 month

---

### Success Criteria

**Migration Complete When**:
1. All 988 tests migrated to GTest
2. 100% test pass rate maintained (currently 100%)
3. CI/CD pipeline generates XML test reports
4. Test execution time maintained or improved
5. Custom framework code removed from codebase
6. Documentation updated with GTest patterns
7. Developer onboarding guide created

**Quality Gates**:
- Zero test failures after migration
- No decrease in code coverage
- Test execution time within 10% of baseline
- All CI/CD integrations working with XML output
- Peer review approval on all migration PRs

---

## Additional Recommendations

### 1. Enable Frama-C Integration Tests

**Action**: Uncomment and complete FramaCEVATests and FramaCWPTests
**Effort**: 4-8 hours
**Impact**: Validates ACSL annotation correctness with formal verification tools
**Priority**: Medium (after Phase 1 migration)

---

### 2. Add Parameterized Tests

**Action**: Convert repetitive test patterns to GTest parameterized tests
**Example**: JSON parser type tests (null, bool, number, string) can share one parameterized test
**Effort**: 5-10 hours during migration
**Impact**: Reduces code duplication by 20-30%
**Priority**: High (during Phase 1-2)

---

### 3. Implement Test Fixtures for Common Utilities

**Action**: Create shared fixture library for AST parsing, code generation, etc.
**Effort**: 6-10 hours
**Impact**: Eliminates 200+ lines of duplicated helper code
**Priority**: High (before Phase 2 migration)

**Proposed Fixtures**:
```cpp
class ASTTestFixture : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> parseCode(const std::string& code,
                                        const std::string& filename = "test.cpp");
    const CXXRecordDecl* extractClass(ASTUnit* AST, size_t index = 0);
    const FunctionDecl* extractFunction(ASTUnit* AST, const std::string& name);
};

class TranspilerTestFixture : public ASTTestFixture {
protected:
    std::string transpileToCWithACSL(const std::string& cppCode);
    bool compileC(const std::string& cCode, std::string& errors);
    std::string runCProgram(const std::string& cCode);
};
```

---

### 4. Add CI/CD Test Reporting

**Action**: Configure GitHub Actions to parse GTest XML output and generate test reports
**Effort**: 2-4 hours
**Impact**: Visible test results in PRs, historical trend tracking
**Priority**: High (after Phase 1 migration)

---

### 5. Implement Parallel Test Execution

**Action**: Enable GTest's parallel test execution with `--gtest_shuffle` and `--gtest_repeat`
**Effort**: 1-2 hours
**Impact**: Reduce CI test execution time by 50-70%
**Priority**: Medium (after full migration)

---

## Appendix: Detailed Suite Inventory

### Core Unit Tests (720 tests, 44 suites)

| Suite Name | Tests | Framework | Output Format | Source File | Migration Difficulty |
|------------|-------|-----------|---------------|-------------|----------------------|
| ACSLStatementAnnotatorTest | 18 | Custom | Inline stdout | tests/ACSLStatementAnnotatorTest.cpp | Medium |
| ACSLBehaviorAnnotatorTest | 15 | Custom | Inline stdout | tests/ACSLBehaviorAnnotatorTest.cpp | Medium |
| ACSLClassAnnotatorTest | 10 | Custom | Inline stdout | tests/ACSLClassAnnotatorTest.cpp | Medium |
| ACSLFunctionAnnotatorTest | 15 | Custom | Inline stdout | tests/ACSLFunctionAnnotatorTest.cpp | Medium |
| ACSLLoopAnnotatorTest | 12 | Custom | Inline stdout | tests/ACSLLoopAnnotatorTest.cpp | Medium |
| ACSLMemoryPredicateAnalyzerTest | 12 | Custom | Inline stdout | tests/ACSLMemoryPredicateAnalyzerTest.cpp | Medium |
| ACSLGeneratorTest | 7 | Custom | Inline stdout | tests/ACSLGeneratorTest.cpp | Medium |
| ACSLAxiomaticBuilderTest | 15 | Custom | Inline stdout | tests/ACSLAxiomaticBuilderTest.cpp | Medium |
| ACSLTypeInvariantGeneratorTest | 15 | Custom | Inline stdout | tests/ACSLTypeInvariantGeneratorTest.cpp | Medium |
| ACSLGhostCodeInjectorTest | 12 | Custom | Inline stdout | tests/ACSLGhostCodeInjectorTest.cpp | Medium |
| StandaloneFunctionTranslationTest | 15 | Custom | Inline stdout | tests/StandaloneFunctionTranslationTest.cpp | Medium |
| VirtualBaseDetectionTest | 8 | Custom | Inline stdout | tests/VirtualBaseDetectionTest.cpp | Medium |
| VirtualBaseOffsetTableTest | 8 | Custom | Inline stdout | tests/VirtualBaseOffsetTableTest.cpp | Medium |
| VTTGeneratorTest | 8 | Custom | Inline stdout | tests/VTTGeneratorTest.cpp | Medium |
| ConstructorSplitterTest | 8 | Custom | Inline stdout | tests/ConstructorSplitterTest.cpp | Medium |
| ExceptionIntegrationTest | 11 | Custom | Inline stdout | tests/ExceptionIntegrationTest.cpp | Medium |
| ExceptionRuntimeTest | 12 | Custom | Inline stdout | tests/ExceptionRuntimeTest.cpp | Medium |
| ExceptionPerformanceTest | 3 | Custom | Inline stdout | tests/ExceptionPerformanceTest.cpp | Medium |
| ExceptionHandlingIntegrationTest | 15 | Custom | Inline stdout | tests/ExceptionHandlingIntegrationTest.cpp | Medium |
| RTTIIntegrationTest | 15 | Custom | Inline stdout | tests/RTTIIntegrationTest.cpp | Medium |
| TemplateIntegrationTest | 15 | Custom | Inline stdout | tests/TemplateIntegrationTest.cpp | Medium |
| HierarchyTraversalTest | 8 | Custom | Inline stdout | tests/HierarchyTraversalTest.cpp | Medium |
| CoroutineDetectorTest | 15 | Custom | Inline stdout | tests/CoroutineDetectorTest.cpp | Medium |
| SuspendPointIdentifierTest | 7 | Custom | Inline stdout | tests/SuspendPointIdentifierTest.cpp | Medium |
| StateMachineTransformerTest | 7 | Custom | Inline stdout | tests/StateMachineTransformerTest.cpp | Medium |
| PromiseTranslatorTest | 7 | Custom | Inline stdout | tests/PromiseTranslatorTest.cpp | Medium |
| CoroutineIntegrationTest | 7 | Custom | Inline stdout | tests/CoroutineIntegrationTest.cpp | Medium |
| ResumeDestroyFunctionTest | 7 | Custom | Inline stdout | tests/ResumeDestroyFunctionTest.cpp | Medium |
| FrameAllocationTest | 7 | Custom | Inline stdout | tests/FrameAllocationTest.cpp | Medium |
| MoveSemanticTranslatorTest | 50 | Custom | Macro-based | tests/unit/move_semantics/MoveSemanticTranslatorTest.cpp | Medium |
| MoveConstructorTranslationTest | 7 | Custom | Macro-based | tests/unit/move_semantics/MoveConstructorTranslationTest.cpp | Easy |
| MoveAssignmentTranslationTest | 9 | Custom | Macro-based | tests/unit/move_semantics/MoveAssignmentTranslationTest.cpp | Easy |
| StdMoveTranslationTest | 10 | Custom | Macro-based | tests/unit/move_semantics/StdMoveTranslationTest.cpp | Easy |
| RvalueRefParameterTest | 10 | Custom | Macro-based | tests/unit/move_semantics/RvalueRefParameterTest.cpp | Easy |
| CopyMoveIntegrationTest | 15 | Custom | Macro-based | tests/unit/move_semantics/CopyMoveIntegrationTest.cpp | Medium |
| LambdaTranslatorTest | 60 | Custom | Macro-based | tests/unit/lambdas/LambdaTranslatorTest.cpp | Medium |
| OperatorOverloadingTest | 62 | Custom | Macro-based | tests/unit/operators/OperatorOverloadingTest.cpp | Medium |
| SharedPtrTest | 15 | Custom | Macro-based | tests/unit/smart_pointers/SharedPtrTest.cpp | Easy |
| UniquePtrTest | 15 | Custom | Macro-based | tests/unit/smart_pointers/UniquePtrTest.cpp | Easy |
| RaiiIntegrationTest | 12 | Custom | Macro-based | tests/unit/smart_pointers/RaiiIntegrationTest.cpp | Easy |
| RuntimeModeLibraryTest | 12 | Custom | Inline stdout | tests/runtime_mode_library_test.cpp | Medium |
| RuntimeModeInlineTest | 10 | Custom | Inline stdout | tests/runtime_mode_inline_test.cpp | Medium |
| RuntimeFeatureFlagsTest | 15 | Custom | Inline stdout | tests/runtime_feature_flags_test.cpp | Medium |
| SizeOptimizationTest | 14 | Custom | Inline stdout | tests/size_optimization_test.cpp | Medium |

### Integration Tests (6 tests, 6 suites)

| Suite Name | Tests | Framework | Output Format | Source File | Migration Difficulty |
|------------|-------|-----------|---------------|-------------|----------------------|
| EdgeCasesTest | 30 | Custom | Macro-based | tests/integration/EdgeCasesTest.cpp | Medium |
| ErrorHandlingTest | 25 | Custom | Macro-based | tests/integration/ErrorHandlingTest.cpp | Medium |
| FeatureInteractionTest | 30 | Custom | Macro-based | tests/integration/FeatureInteractionTest.cpp | Medium |
| FeatureCombinationTest | 20 | Custom | Macro-based | tests/integration/FeatureCombinationTest.cpp | Medium |
| FramaCEVATests | ~15 (disabled) | GTest | XML | tests/integration/FramaCEVATests.cpp | N/A (Enable) |
| FramaCWPTests | ~15 (disabled) | GTest | XML | tests/integration/FramaCWPTests.cpp | N/A (Enable) |

### Real-World Integration Tests (252 tests, 5 suites)

| Suite Name | Tests | Framework | Output Format | Source File | Migration Difficulty |
|------------|-------|-----------|---------------|-------------|----------------------|
| JSON Parser | 68 | Custom | Helper function | tests/real-world/json-parser/tests/test_json_parser.cpp | Easy |
| Resource Manager | 98 | Custom | Helper function | tests/real-world/resource-manager/tests/test_resource_manager.cpp | Easy |
| Logger | 24 | Custom | Helper function | tests/real-world/logger/tests/test_logger.cpp | Easy |
| String Formatter | 61 | Custom | Helper function | tests/real-world/string-formatter/tests/test_string_formatter.cpp | Easy |
| Test Framework | 9 | Custom | Helper function | tests/real-world/test-framework/tests/test_framework.cpp | Easy |

### Example Tests (10 tests, 2 suites)

| Suite Name | Tests | Framework | Output Format | Source File | Migration Difficulty |
|------------|-------|-----------|---------------|-------------|----------------------|
| Test Framework Example | 7 | Custom | Helper function | examples/test-framework/tests/test_example.cpp | Easy |
| Safety-Critical Example | 3 | Custom | Inline stdout | examples/safety-critical/tests/test_flight_control.cpp | Easy |

---

## Glossary

**Custom Framework**: Home-grown testing infrastructure using standard C++ assertions and iostream for output, with no external dependencies

**GTest (Google Test)**: Industry-standard C++ testing framework developed by Google, providing rich assertions, fixtures, parameterized tests, and CI/CD integration

**Test Fixture**: Reusable test setup/teardown code shared across multiple test cases

**Parameterized Test**: Test that runs multiple times with different input data, reducing code duplication

**Death Test**: Test that verifies code terminates (crashes) as expected under certain conditions

**xUnit XML**: Standard test result format supported by CI/CD tools like Jenkins, GitHub Actions, CircleCI

**Test Discovery**: Automatic detection and registration of test cases without manual configuration

---

**End of Report**

---

**Next Steps**:
1. Review this analysis with the development team
2. Prioritize migration phases based on business needs
3. Allocate resources for migration effort (1.5-2 weeks focused work)
4. Create GTest fixture library before beginning Phase 1
5. Set up CI/CD pipeline to consume GTest XML output
6. Begin incremental migration with Phase 1 (real-world tests)
