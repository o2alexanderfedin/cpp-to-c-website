#!/usr/bin/env python3
"""
Migrate inline-style tests (Variant A) to Google Test format.
Pattern:
- void testName() { std::cout << "Test..."; assert(...); std::cout << "PASSED\n"; }
- int main() { testName(); ... return 0; }

Target:
- TEST_F(Fixture, Name) { ASSERT_...; }
- Remove main()
- Add #include <gtest/gtest.h>
"""

import re
import sys
from pathlib import Path

def extract_test_functions(content):
    """Extract all test functions from the file."""
    # Pattern: void testXxx() { ... }
    pattern = r'void\s+(test\w+)\s*\(\)\s*\{([^}]+(?:\{[^}]*\}[^}]*)*)\}'
    matches = re.finditer(pattern, content, re.DOTALL)

    tests = []
    for match in matches:
        test_name = match.group(1)
        test_body = match.group(2)
        tests.append((test_name, test_body, match.span()))

    return tests

def convert_test_to_gtest(test_name, test_body, fixture_name):
    """Convert a single test function to GTest format."""
    # Remove the initial cout line
    test_body = re.sub(r'std::cout\s*<<\s*"Test\s+\d+:.*?";?\s*', '', test_body, count=1)
    test_body = re.sub(r'std::cout\s*<<\s*"TEST.*?";?\s*', '', test_body, count=1)

    # Remove the final "PASSED" lines
    test_body = re.sub(r'std::cout\s*<<\s*"PASS(ED)?\\?n?".*?;?\s*', '', test_body)
    test_body = re.sub(r'std::cout\s*<<\s*"PASSED".*?;?\s*', '', test_body)

    # Convert assert() to ASSERT/EXPECT
    # assert(condition && "message") -> ASSERT_TRUE(condition) << "message"
    test_body = re.sub(
        r'assert\s*\(\s*([^&]+?)\s*&&\s*"([^"]+)"\s*\)',
        r'ASSERT_TRUE(\1) << "\2"',
        test_body
    )

    # assert(condition) -> ASSERT_TRUE(condition)
    test_body = re.sub(r'assert\s*\(([^)]+)\)\s*;', r'ASSERT_TRUE(\1);', test_body)

    # Convert exit(1) to FAIL()
    test_body = re.sub(r'exit\s*\(\s*1\s*\)\s*;', 'FAIL();', test_body)

    # Extract test name (remove "test" prefix, convert to CamelCase)
    gtest_name = test_name
    if gtest_name.startswith('test'):
        gtest_name = gtest_name[4:]  # Remove 'test' prefix

    # Build GTest function
    gtest = f"TEST_F({fixture_name}, {gtest_name}) {{\n{test_body}\n}}\n"

    return gtest

def extract_fixture_name(content):
    """Extract or determine the fixture name from the file."""
    # Look for existing class definitions
    match = re.search(r'class\s+(\w+Extractor|Test\w+)\s*:', content)
    if match:
        base_name = match.group(1)
        if 'Extractor' in base_name:
            # ACSLTypeInvariantGeneratorTest -> TypeExtractor
            # Create fixture name
            return base_name.replace('Extractor', 'Fixture')
        return base_name + 'Fixture'

    # Default: extract from filename
    return 'TestFixture'

def migrate_file(file_path):
    """Migrate a single test file to GTest format."""
    content = Path(file_path).read_text()

    # Check if already migrated
    if '#include <gtest/gtest.h>' in content or 'TEST_F(' in content:
        print(f"✓ {file_path} already migrated")
        return False

    # Extract test functions
    tests = extract_test_functions(content)
    if not tests:
        print(f"✗ {file_path} - no tests found")
        return False

    print(f"Found {len(tests)} tests in {file_path}")

    # Determine fixture name
    fixture_name = extract_fixture_name(content)

    # Find the position to insert converted tests (before main)
    main_pattern = r'int\s+main\s*\(\s*\)\s*\{.*?\n\s*return\s+0;\s*\}'
    main_match = re.search(main_pattern, content, re.DOTALL)

    if not main_match:
        print(f"✗ {file_path} - no main() found")
        return False

    # Build new content
    new_content = content

    # Add gtest include if not present
    if '#include <gtest/gtest.h>' not in new_content:
        # Find first #include and add after it
        include_pos = new_content.find('#include')
        if include_pos != -1:
            first_newline = new_content.find('\n', include_pos)
            new_content = new_content[:first_newline+1] + '#include <gtest/gtest.h>\n' + new_content[first_newline+1:]

    # Create fixture class if needed
    fixture_class = f"\n// Test fixture\nclass {fixture_name} : public ::testing::Test {{\nprotected:\n}};\n\n"

    # Convert tests
    converted_tests = []
    for test_name, test_body, _ in tests:
        gtest = convert_test_to_gtest(test_name, test_body, fixture_name)
        converted_tests.append(gtest)

    # Remove old test functions and main
    for test_name, _, span in reversed(tests):
        new_content = new_content[:span[0]] + new_content[span[1]+1:]

    # Remove main()
    new_content = re.sub(main_pattern, '', new_content, flags=re.DOTALL)

    # Insert fixture and tests before the final section
    insertion_point = new_content.rfind('// ===')
    if insertion_point == -1:
        insertion_point = len(new_content)

    new_content = new_content[:insertion_point] + fixture_class + '\n'.join(converted_tests) + '\n' + new_content[insertion_point:]

    # Write back
    Path(file_path).write_text(new_content)
    print(f"✓ {file_path} migrated - {len(tests)} tests")
    return True

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: migrate_inline_tests.py <file1.cpp> [file2.cpp ...]")
        sys.exit(1)

    for file_path in sys.argv[1:]:
        migrate_file(file_path)
