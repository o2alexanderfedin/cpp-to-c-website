#!/usr/bin/env python3
"""
Script to migrate inline-style tests to GTest format.
Converts:
  - void test_Name() -> TEST(Suite, Name)
  - std::cout << "Running..." -> (removed)
  - std::cout << "✓" -> (removed)
  - assert(cond && "msg") -> ASSERT_TRUE(cond) << "msg"
  - assert(cond) -> ASSERT_TRUE(cond)
  - Adds GTest includes
  - Removes main() and replaces with auto-registration
"""

import re
import sys
import os

def convert_test_function_to_gtest(content, suite_name):
    """Convert test_FunctionName() to TEST(Suite, FunctionName)"""

    # Pattern: void test_Name() { ... } - capture entire function
    # First, let's just convert the function signature
    pattern = r'void\s+(test_\w+)\s*\(\s*\)\s*\{'

    def replacer(match):
        test_name = match.group(1)
        # Remove test_ prefix
        clean_name = test_name[5:] if test_name.startswith('test_') else test_name
        return f'TEST({suite_name}, {clean_name}) {{'

    content = re.sub(pattern, replacer, content)
    return content

def remove_cout_statements(content):
    """Remove std::cout << "Running..." and std::cout << "✓" statements"""

    # Remove "Running test..." lines
    content = re.sub(r'\s*std::cout\s*<<\s*"Running\s+test.*?;\s*\n', '', content)

    # Remove "✓" lines
    content = re.sub(r'\s*std::cout\s*<<\s*"✓".*?;\s*\n', '', content)

    # Remove other PASSED-style outputs
    content = re.sub(r'\s*std::cout\s*<<\s*"PASSED.*?;\s*\n', '', content)

    return content

def convert_asserts_to_gtest(content):
    """Convert assert() to ASSERT_* macros"""

    # assert(condition && "message") -> ASSERT_TRUE(condition) << "message"
    pattern1 = r'assert\s*\(\s*([^&]+?)\s*&&\s*"([^"]+)"\s*\)'
    content = re.sub(pattern1, r'ASSERT_TRUE(\1) << "\2"', content)

    # assert(!condition && "message") -> ASSERT_FALSE(condition) << "message"
    pattern2 = r'assert\s*\(\s*!\s*([^&]+?)\s*&&\s*"([^"]+)"\s*\)'
    content = re.sub(pattern2, r'ASSERT_FALSE(\1) << "\2"', content)

    # assert(condition) -> ASSERT_TRUE(condition)
    pattern3 = r'assert\s*\(\s*([^)]+?)\s*\)'
    content = re.sub(pattern3, r'ASSERT_TRUE(\1)', content)

    return content

def update_includes(content):
    """Add GTest includes and remove old test includes"""

    # Remove #include <cassert>
    content = re.sub(r'#include\s+<cassert>\s*\n', '', content)

    # Remove std::cout include if not needed
    content = re.sub(r'#include\s+<iostream>\s*\n', '', content)

    # Add GTest include after other includes
    if '#include <gtest/gtest.h>' not in content:
        # Find last #include and add after it
        includes = list(re.finditer(r'#include\s+[<"].*?[>"]\s*\n', content))
        if includes:
            last_include = includes[-1]
            insert_pos = last_include.end()
            content = content[:insert_pos] + '#include <gtest/gtest.h>\n' + content[insert_pos:]

    return content

def remove_main_function(content):
    """Remove main() function - GTest provides its own"""

    # Remove entire main() function
    pattern = r'int\s+main\s*\([^)]*\)\s*\{[^}]*(?:\{[^}]*\}[^}]*)*\}\s*$'
    content = re.sub(pattern, '', content, flags=re.MULTILINE | re.DOTALL)

    return content

def extract_suite_name_from_filename(filename):
    """Extract test suite name from filename: FooBarTest.cpp -> FooBarTest"""
    basename = os.path.basename(filename)
    suite_name = basename.replace('.cpp', '')
    return suite_name

def migrate_file(input_file, output_file=None):
    """Migrate a single test file from inline style to GTest"""

    if output_file is None:
        output_file = input_file

    with open(input_file, 'r') as f:
        content = f.read()

    suite_name = extract_suite_name_from_filename(input_file)

    # Apply transformations
    content = convert_test_function_to_gtest(content, suite_name)
    content = remove_cout_statements(content)
    content = convert_asserts_to_gtest(content)
    content = update_includes(content)
    content = remove_main_function(content)

    with open(output_file, 'w') as f:
        f.write(content)

    print(f"✓ Migrated {input_file} -> {output_file}")

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: migrate_inline_to_gtest.py <input_file> [output_file]")
        sys.exit(1)

    input_file = sys.argv[1]
    output_file = sys.argv[2] if len(sys.argv) > 2 else None

    migrate_file(input_file, output_file)
