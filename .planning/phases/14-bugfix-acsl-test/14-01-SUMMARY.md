# Phase 14-01 Summary: ACSLStatementAnnotatorTest Bugfix

**Status**: COMPLETE
**Result**: ACSLStatementAnnotatorTest now passing (18/18 tests, exit code 0)
**Date**: December 21, 2025

## Root Cause

The test executable was experiencing exit code 138 (SIGBUS) during cleanup/teardown. Analysis revealed:

**Compilation Error Leading to Previous Failure:**
The test file had a critical bug where `persistentASTs` was referenced in the `parseFunctionDecl()` helper function (line 36) before it was declared. The static vector was declared as a member of the `ACSLStatementAnnotatorTest` test fixture class, but the helper function was defined before the class declaration.

This caused a compilation error:
```
error: use of undeclared identifier 'persistentASTs'
   36 |     persistentASTs.push_back(std::move(AST));
      |     ^
```

**Previous Attempt at Fix:**
Someone had attempted to fix the exit code 138 crash by introducing a `persistentASTs` vector to keep AST units alive and prevent dangling pointers during cleanup. However, the implementation had a scope/ordering issue that prevented compilation.

**Actual Root Cause:**
The exit code 138 was caused by AST destruction order issues - FunctionDecl pointers returned by `parseFunctionDecl()` were becoming dangling when their owning ASTUnit objects were destroyed at the end of the helper function.

## Fix Applied

**Solution:** Move `persistentASTs` declaration to global scope before the helper function

The fix involved two changes to `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/ACSLStatementAnnotatorTest.cpp`:

1. **Moved static vector to global scope** (after `using namespace clang;`, before `parseFunctionDecl()`):
   ```cpp
   // Static storage for AST units to prevent dangling pointers during test cleanup
   // This fixes exit code 138 (SIGBUS) caused by AST destruction order issues
   static std::vector<std::unique_ptr<ASTUnit>> persistentASTs;
   ```

2. **Removed duplicate declarations** from the test fixture class:
   - Removed `static std::vector<std::unique_ptr<ASTUnit>> persistentASTs;` from class definition
   - Removed static member initialization `std::vector<std::unique_ptr<ASTUnit>> ACSLStatementAnnotatorTest::persistentASTs;`

**Why This Works:**
- AST units are now stored in a global static vector that persists until program termination
- FunctionDecl pointers remain valid throughout test execution since their owning ASTUnit objects are kept alive
- Prevents dangling pointer access during test cleanup/teardown
- Eliminates the SIGBUS crash (exit code 138)

## Verification Results

### Compilation
✅ Test compiles successfully with no warnings or errors

### Exit Code
✅ Exit code: **0** (was **138**)

### Test Results
✅ All **18/18** tests passing in ACSLStatementAnnotatorTest suite
- PointerDereferenceAssertion
- ArrayAccessAssertion
- DivisionByZeroAssertion
- BufferOverflowAssertion
- NullPointerAssertion
- CastAssertion
- ValidatedInputAssumption
- ConstructorAssumption
- PlatformAssumption
- ProofMilestoneCheck
- InvariantMaintenanceCheck
- CustomProofObligationCheck
- NoneLevelNoAnnotations
- BasicLevelEssentialAnnotations
- FullLevelComprehensiveAnnotations
- MultiplePointerDereferences
- NestedArrayAccess
- ModuloOperation

### Test Stability
✅ **10/10** consecutive runs successful (all with exit code 0)

### Full Test Suite
✅ **53/54** test suites passing (98.1% pass rate)
- ACSLStatementAnnotatorTest: **PASSED** ✅ (was FAILING with exit code 138)
- Only unrelated failure: MoveSemanticTranslatorTest (11/50 tests failing, pre-existing issue)

### Memory Safety
✅ No crashes during any test run
✅ Clean exit code 0 on all executions

### Regressions
✅ **None** - All previously passing tests continue to pass

## Files Modified

**Modified:**
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/ACSLStatementAnnotatorTest.cpp`
  - Moved `persistentASTs` static vector declaration to global scope
  - Added documentation comment explaining the fix
  - Removed duplicate declarations from test fixture class

## Technical Details

**Previous Code Structure:**
```cpp
using namespace clang;

FunctionDecl* parseFunctionDecl(...) {
    // ...
    persistentASTs.push_back(std::move(AST));  // ERROR: undeclared identifier
    return result;
}

class ACSLStatementAnnotatorTest : public ::testing::Test {
protected:
    static std::vector<std::unique_ptr<ASTUnit>> persistentASTs;  // Declared too late
};
```

**Fixed Code Structure:**
```cpp
using namespace clang;

// Static storage for AST units - GLOBAL SCOPE
static std::vector<std::unique_ptr<ASTUnit>> persistentASTs;

FunctionDecl* parseFunctionDecl(...) {
    // ...
    persistentASTs.push_back(std::move(AST));  // ✅ Now valid
    return result;
}

class ACSLStatementAnnotatorTest : public ::testing::Test {
protected:
    // Test fixture (no static members needed)
};
```

## Performance Impact

- **Minimal:** AST units are stored for lifetime of test executable (acceptable for test code)
- **Memory:** Approximately 18 AST units retained (one per test), cleared on program exit
- **Execution Time:** No measurable impact (test suite runs in ~55-96ms)

## Commit

**Main Repository:**
- Commit: `71c7eaff2fd8288a849cf7f2ca375ebfd3d86f09`
- Message: `feat(14-01): Fix ACSLStatementAnnotatorTest exit code 138`
- Branch: `develop`

**Website Submodule:**
- Commit: `7afa59c`
- Message: `docs(14-01): Add Phase 14-01 completion summary`
- Branch: `develop`

## Production Status

✅ **ACSLStatementAnnotatorTest FIXED - ZERO EXIT CODE 138 FAILURES**

The test suite is now stable with clean exit codes. The fix addresses both the immediate compilation error and the underlying AST lifetime management issue that was causing the SIGBUS crash.

**Next Steps:**
- Address MoveSemanticTranslatorTest failures (separate issue, 11/50 tests failing)
- Continue monitoring test stability in CI/CD pipeline

---

**Prepared by**: Claude Sonnet 4.5 (Autonomous Agent)
**Execution Date**: December 21, 2025
**Phase**: 14-01 Bugfix - ACSL Test Exit Code 138
