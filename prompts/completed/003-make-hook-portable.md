<objective>
Ensure the PreToolUse hook fix is portable and not bound to any specific repository structure or configuration.

The hook should work correctly across different projects and environments without requiring repository-specific modifications. This makes the hook reusable and maintainable across all Claude Code projects.
</objective>

<context>
The recently fixed PreToolUse hook at `~/.claude/hooks/validators/approach1-auto-approve.sh` currently works, but may contain repository-specific assumptions or hardcoded paths.

Since hooks are global (stored in `~/.claude/hooks/`), they should be:
- **Repository-agnostic**: Work in any repository without modification
- **Environment-independent**: No hardcoded paths or assumptions about project structure
- **Self-contained**: All logic and dependencies should be within the hook itself

Read and analyze:
@~/.claude/hooks/validators/approach1-auto-approve.sh
@~/.claude/hooks/validators/README.md
</context>

<requirements>
1. **Remove Repository-Specific References**: Eliminate any hardcoded paths, repository names, or project-specific assumptions
2. **Dynamic Path Detection**: Use environment variables and relative paths where needed
3. **Graceful Fallbacks**: Handle missing directories or files without breaking
4. **Universal Patterns**: Detection logic should work regardless of project structure
5. **Documentation Updates**: Ensure README reflects portability improvements
6. **Backward Compatibility**: Don't break existing functionality
</requirements>

<implementation>
Follow these steps to ensure portability:

1. **Analyze Current Hook for Portability Issues**
   - Identify hardcoded repository names or paths
   - Check for assumptions about directory structure
   - Look for environment-specific logic
   - Find any references to specific project files

2. **Common Portability Issues to Fix**
   ```bash
   # BAD - Repository-specific:
   if [[ "$command" =~ "cpp-to-c-website" ]]; then

   # GOOD - Generic:
   if [[ "$command" =~ "/pages" ]]; then

   # BAD - Hardcoded path:
   SCRIPT_DIR="$HOME/.claude/skills/lib/work-items-project"

   # GOOD - Dynamic path with fallback:
   SCRIPT_DIR="${CLAUDE_SKILLS_DIR:-$HOME/.claude/skills}/lib/work-items-project"

   # BAD - Assumes directory exists:
   source "$HOME/.claude/hooks/common.sh"

   # GOOD - Graceful fallback:
   if [[ -f "$HOME/.claude/hooks/common.sh" ]]; then
       source "$HOME/.claude/hooks/common.sh"
   fi
   ```

3. **Make Detection Logic Universal**
   - Pattern matching should identify **operation types**, not specific repos
   - Use command structure analysis, not repo names
   - Environment variables should use standard Claude Code conventions

4. **Test Portability Across Scenarios**
   Test the hook works correctly when:
   - Run from different repositories
   - Different repository structures (monorepo, single project)
   - Script library exists vs doesn't exist
   - Different user home directories
   - Different shell environments (bash, zsh)

5. **Update Documentation**
   - Note portability features in README
   - Document any required environment variables
   - Provide examples from different project types

</implementation>

<output>
Modify files:
- `~/.claude/hooks/validators/approach1-auto-approve.sh` - Remove repository-specific code
- `~/.claude/hooks/validators/README.md` - Document portability features

Provide verification report showing:
- What was made portable
- Test results from different contexts
- Any remaining assumptions (if unavoidable, document them)
</output>

<verification>
Before declaring complete, verify portability:

1. **Test in Different Repositories**:
   - Create a temporary test directory
   - Run the hook with various gh commands
   - Verify it works without project-specific configuration

2. **Test Missing Dependencies**:
   - Temporarily rename script library
   - Verify hook still works (allows admin operations, blocks work items)
   - Restore script library

3. **Check for Hardcoded Values**:
   ```bash
   # Search for potential issues:
   grep -E "(cpp-to-c|alexanderfedin|specific-repo-name)" ~/.claude/hooks/validators/approach1-auto-approve.sh
   ```
   Expected: No matches (or only in comments/examples)

4. **Verify Error Messages**:
   - Error messages should not reference specific projects
   - Path suggestions should use generic patterns

5. **Cross-Shell Compatibility**:
   - Test in bash and zsh (if available)
   - Verify POSIX compliance for maximum portability

</verification>

<success_criteria>
- ✓ No repository-specific hardcoded values in hook code
- ✓ All paths use environment variables or dynamic detection
- ✓ Hook works in different repositories without modification
- ✓ Graceful handling of missing dependencies
- ✓ Error messages are generic and helpful
- ✓ Documentation clearly explains portability features
- ✓ All test scenarios pass
- ✓ Changes committed following project git-flow
</success_criteria>

<constraints>
- Maintain all existing functionality (admin operations allowed, work items blocked)
- Keep hook execution fast (< 100ms)
- Use POSIX-compliant shell syntax for maximum compatibility
- Don't introduce external dependencies
- Follow the project's CLAUDE.md guidelines for git workflow
</constraints>

<implementation_notes>
Why portability matters:
- **Reusability**: One hook works across all projects
- **Maintainability**: Updates in one place benefit all projects
- **Reliability**: No brittle dependencies on specific paths or structures
- **User Experience**: Hook works out-of-the-box without configuration

Common portability principles:
- **Environment variables over hardcoded paths**: `${VAR:-default}` pattern
- **Existence checks before usage**: Test files/dirs exist before referencing
- **Generic pattern matching**: Match operation types, not repo names
- **Graceful degradation**: Work even if optional components are missing

The hook is a **global tool** that should work universally, not tied to any specific project.
</implementation_notes>
