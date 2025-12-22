<objective>
Analyze all 988 tests across the C++ to C transpiler project to document:
1. Total test count by category and test suite
2. Test framework usage patterns (which frameworks are used where)
3. Inconsistencies and opportunities for standardization
4. Recommended migration strategy to a single unified test framework

This analysis will inform a technical discussion about standardizing the test infrastructure and guide a potential framework consolidation effort.
</objective>

<context>
Project: C++ to C Transpiler (hupyy-cpp-to-c)

**Current Test Landscape** (from recent comprehensive test report):
- **988 total tests** across 51 test suites
- **Core unit tests**: 720 tests (44 suites in `build/*Test`)
- **Real-world integration**: 252 tests (5 suites in `tests/real-world/*/build/`)
- **Example tests**: 16 tests (examples in `examples/*/build/`)

**Known Test Categories**:
1. Core unit test suites (ACSL, transpilation phases, C++ features)
2. Real-world integration tests (JSON parser, resource manager, logger, etc.)
3. Example/demonstration tests
4. Shell script tests (build/integration tests in `tests/*.sh`)

**Why this matters**:
- Multiple test frameworks increase maintenance burden
- Inconsistent patterns make it harder to add new tests
- Standardization improves developer experience and CI/CD reliability
- Framework choice affects build time, test output clarity, and debugging experience
</context>

<requirements>
1. **Inventory all test executables**:
   - Scan `build/*Test` for core unit tests
   - Scan `tests/real-world/*/build/` for integration tests
   - Scan `examples/*/build/` for example tests
   - Identify any additional test executables

2. **Analyze test framework usage**:
   - For each test executable, determine which framework is used:
     - Custom framework (check for custom assertion macros, test registration)
     - Google Test (gtest)
     - Catch2
     - Boost.Test
     - CppUnit
     - Other frameworks
   - Examine test source files when needed to identify framework
   - Look for patterns in:
     - Include statements (`#include <gtest/gtest.h>`, `#include "test_framework.h"`)
     - Test macros (`TEST()`, `ASSERT_*`, custom macros)
     - Main function patterns
     - Assertion styles

3. **Document test output formats**:
   - Categorize by output style (custom format, xUnit XML, TAP, etc.)
   - Note which suites have consistent vs inconsistent output
   - Identify suites that would benefit from standardized reporting

4. **Identify framework inconsistencies**:
   - Map which framework is used in each category
   - Highlight areas using different frameworks for similar tests
   - Note any custom/home-grown frameworks vs established libraries

5. **Assess migration complexity**:
   - Count tests using each framework
   - Identify tests that would be easy vs hard to migrate
   - Note any framework-specific features being used (fixtures, parameterized tests, etc.)
</requirements>

<implementation>
**Step 1: Gather test executable inventory**
```bash
# Find all test executables
find build -type f -name "*Test" -executable
find tests/real-world -type f -name "test_*" -executable
find examples -type f -name "*test*" -executable
```

**Step 2: Examine test source files**
For representative samples from each category:
- Read test source files to identify framework
- Look for include directives and test macros
- Check CMakeLists.txt for framework dependencies

**Step 3: Categorize by framework**
Create a mapping of:
- Framework name → Test suites using it
- Test count per framework
- LOC (lines of code) per framework

**Step 4: Analyze patterns**
- Are core unit tests using one framework?
- Are integration tests using another?
- Is there a custom framework for specific test types?
- What's the ratio of custom vs established frameworks?

**Why examine source files**: Test executables don't reveal which framework was used. Source code inspection is necessary to identify frameworks and assess migration effort.
</implementation>

<research>
You may need to examine these file types:
- `tests/*Test.cpp` - Core unit test source files
- `tests/real-world/*/test_*.cpp` - Integration test sources
- `CMakeLists.txt` - Build configuration revealing framework dependencies
- `tests/*.h` - Custom test framework headers (if any)
- Example test sources in `examples/`

Use Glob and Read tools to efficiently scan and examine test files.
</research>

<output>
Generate a comprehensive analysis report at:
`./test-reports/test-framework-analysis-2025-12-20.md`

**Report Structure**:

```markdown
# Test Framework Analysis - C++ to C Transpiler

**Date**: 2025-12-20
**Total Tests**: 988 across 51 suites

## Executive Summary

- **Primary Framework**: [framework name] ([X] tests, [Y]%)
- **Secondary Frameworks**: [list with counts]
- **Custom/Home-grown**: [count if any]
- **Recommendation**: [one-sentence recommendation]

## Detailed Breakdown

### Framework Usage by Category

| Framework | Core Tests | Integration Tests | Example Tests | Total |
|-----------|------------|-------------------|---------------|-------|
| [Name]    | X          | Y                 | Z             | Total |

### Framework Distribution

**[Framework Name]** (X tests, Y%)
- Test suites: [list of suites]
- Usage pattern: [where/why used]
- Migration complexity: [easy/medium/hard]

[Repeat for each framework]

### Test Output Formats

| Format Type | Test Suites | Notes |
|-------------|-------------|-------|
| Custom text | [list]      | [observations] |
| xUnit XML   | [list]      | [observations] |
| TAP         | [list]      | [observations] |

## Inconsistencies Found

1. **[Inconsistency category]**
   - Description: [what's inconsistent]
   - Impact: [why it matters]
   - Affected suites: [list]

## Migration Strategy Recommendation

### Target Framework: [Framework Name]

**Rationale**:
- [Why this framework]
- [Benefits over current mix]
- [Compatibility considerations]

### Migration Phases

**Phase 1: Low-Hanging Fruit** ([X] tests, [Y] hours estimated)
- Suites to migrate: [list easiest migrations]
- Estimated effort: [breakdown]

**Phase 2: Medium Complexity** ([X] tests, [Y] hours estimated)
- Suites to migrate: [list]
- Challenges: [what makes these harder]

**Phase 3: High Complexity** ([X] tests, [Y] hours estimated)
- Suites to migrate: [list hardest migrations]
- Challenges: [special cases, custom features, etc.]

### Risk Assessment

- **Low risk**: Suites with simple assertions
- **Medium risk**: Suites using fixtures/setup
- **High risk**: Suites with custom framework features

## Appendix: Detailed Suite Inventory

[For each test suite, include]:
- Suite name
- Test count
- Framework used
- Output format
- Source file location
- Migration difficulty (easy/medium/hard)
```
</output>

<verification>
Before declaring complete, verify:
1. ✓ All 988 tests accounted for in the analysis
2. ✓ Each test suite categorized by framework
3. ✓ Framework percentages calculated accurately
4. ✓ Migration strategy includes effort estimates
5. ✓ Inconsistencies clearly documented with impact
6. ✓ Report suitable for technical discussion
7. ✓ Recommendations actionable and justified
</verification>

<success_criteria>
- Comprehensive inventory of all 988 tests by framework
- Clear identification of framework inconsistencies
- Actionable migration strategy with effort estimates
- Report ready for team discussion
- Analysis reveals patterns (e.g., "all ACSL tests use framework X")
- Percentage breakdown shows current framework distribution
</success_criteria>
