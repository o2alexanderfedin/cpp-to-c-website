<objective>
Replace all instances of `/Users/alexanderfedin/` with `~/` in documentation files for improved portability.

This ensures documentation works for all users regardless of their username or home directory path, making examples and instructions universally applicable.
</objective>

<context>
Documentation files in this repository currently contain absolute paths like `/Users/alexanderfedin/Projects/...` which are user-specific and not portable.

Using `~/` (tilde notation) instead makes paths:
- **Portable**: Work for any user on any system
- **Cleaner**: Shorter, more readable
- **Standard**: Common Unix/Linux convention
- **Future-proof**: Won't break if username changes

This is especially important for:
- Documentation that other users will read
- Examples that users might copy-paste
- CI/CD verification documents
- Hook documentation that's used globally
</context>

<requirements>
1. **Find All Instances**: Search for `/Users/alexanderfedin/` across all documentation files
2. **Replace with Tilde**: Change to `~/` while preserving the rest of the path
3. **Verify Context**: Ensure replacements make sense (don't break code blocks or URLs)
4. **Update Consistently**: Apply changes to all relevant files
5. **Preserve Formatting**: Maintain markdown formatting, code blocks, and indentation
</requirements>

<implementation>
Follow these steps:

1. **Search for User-Specific Paths**
   ```bash
   # Find all instances in documentation
   grep -r "/Users/alexanderfedin/" docs/ --include="*.md"
   grep -r "/Users/alexanderfedin/" *.md 2>/dev/null
   ```

2. **Review Each Instance**
   - Examine context to ensure replacement is appropriate
   - Most cases in documentation should be replaced
   - Keep absolute paths only if technically required (rare)

3. **Perform Replacements**
   For each file containing the pattern:
   - Replace `/Users/alexanderfedin/` with `~/`
   - Example: `/Users/alexanderfedin/Projects/foo` → `~/Projects/foo`
   - Example: `/Users/alexanderfedin/.claude/hooks` → `~/.claude/hooks`

4. **Common Locations to Check**
   - `docs/` directory (all markdown files)
   - `README.md`, `CONTRIBUTING.md`, `ARCHITECTURE.md`
   - CI/CD documentation
   - Hook documentation
   - Any verification or test documentation

5. **Verify Changes**
   - Ensure no broken references
   - Check that examples still make sense
   - Confirm code blocks are still valid
</implementation>

<output>
Modify files:
- All documentation files containing `/Users/alexanderfedin/`

Provide summary showing:
- List of files modified
- Number of replacements per file
- Any instances that were NOT replaced (with explanation)
</output>

<verification>
Before declaring complete:

1. **Verify No Instances Remain**:
   ```bash
   grep -r "/Users/alexanderfedin/" docs/ --include="*.md"
   grep -r "/Users/alexanderfedin/" *.md 2>/dev/null
   ```
   Expected: No results (or only in appropriate contexts with documented reason)

2. **Check Markdown Formatting**:
   - Code blocks still valid
   - Links not broken
   - Examples remain clear

3. **Verify Tilde Expansion Works**:
   - `~/` correctly represents home directory
   - Paths remain valid and understandable

4. **Test Sample Paths**:
   - Pick 2-3 changed paths
   - Verify they work with tilde notation
</verification>

<success_criteria>
- ✓ All instances of `/Users/alexanderfedin/` replaced with `~/` in documentation
- ✓ Markdown formatting preserved
- ✓ Code blocks and examples remain valid
- ✓ No broken references or links
- ✓ All modified files committed following project git-flow
- ✓ Summary of changes provided
</success_criteria>

<constraints>
- Only modify documentation files (*.md), not code files unless in comments/docs
- Preserve the exact meaning of examples and instructions
- Don't change paths where absolute paths are technically required
- Maintain all markdown formatting and structure
- Follow the project's CLAUDE.md guidelines for git workflow
</constraints>

<implementation_notes>
Why this matters:
- **User Experience**: Other users can follow documentation without adapting paths
- **Professionalism**: Shows attention to detail and consideration for others
- **Maintainability**: Reduces user-specific content that needs updating
- **Standards Compliance**: Follows Unix/Linux conventions for portable paths

The tilde (`~`) is universally understood in Unix-like systems to represent the current user's home directory, making it the standard choice for portable path notation in documentation.
</implementation_notes>
