<objective>
Fix the PreToolUse:Bash hook that is incorrectly blocking legitimate GitHub API calls for administrative tasks like enabling GitHub Pages.

The hook should distinguish between:
- **Blocked**: Direct gh CLI usage for work item management (stories, epics, tasks) that should use script abstractions
- **Allowed**: Administrative operations like enabling GitHub Pages, managing repository settings, viewing workflows

This fix ensures developers can perform necessary repository administration while maintaining the script abstraction pattern for work item operations.
</objective>

<context>
The hook at `~/.claude/hooks/validators/approach1-auto-approve.sh` is currently blocking ALL GitHub CLI usage and directing users to create scripts in `~/.claude/skills/lib/work-items-project/`.

This is overly restrictive because:
- Enabling GitHub Pages is a one-time administrative task, not a work item operation
- Administrative tasks don't benefit from script abstractions
- The hook's intended purpose is to enforce script patterns for **work item operations** (stories, epics, tasks, bugs, spikes)

Read and analyze:
@~/.claude/hooks/validators/approach1-auto-approve.sh
@~/.claude/skills/lib/work-items-project/README.md (if exists, to understand the script library's purpose)
</context>

<requirements>
1. **Preserve Core Intent**: Keep blocking direct gh CLI for work item operations (story, epic, task, bug, spike CRUD)
2. **Allow Administrative Tasks**: Permit gh API calls for:
   - Repository settings (Pages, Actions, security)
   - Workflow management (view, list, run)
   - Repository metadata queries (view, list)
   - One-time setup tasks
3. **Clear Error Messages**: When blocking, explain WHY and WHEN to use script abstractions
4. **Pattern Recognition**: Distinguish between work item operations vs administrative operations
5. **Maintainability**: Use clear, documented logic for easy future updates
</requirements>

<implementation>
Follow these steps:

1. **Read Current Hook**
   - Examine the hook logic and blocking conditions
   - Identify what patterns are currently blocked
   - Understand the script library structure it references

2. **Define Allowlist Patterns**
   Create clear categories:
   - **Work item operations** (BLOCK): Issues, projects, stories, epics, tasks - these should use scripts
   - **Administrative operations** (ALLOW): Repository settings, Pages, Actions permissions, workflows
   - **Read-only queries** (ALLOW): gh repo view, gh workflow list, gh workflow view

3. **Implement Smart Detection**
   Update the hook to:
   - Parse the gh command and detect operation type
   - Allow administrative and read-only operations
   - Block work item CRUD operations
   - Provide context-specific error messages

4. **Test Scenarios**
   Verify the hook correctly handles:
   ```bash
   # Should ALLOW:
   gh api repos/owner/repo/pages -X POST -f build_type=workflow
   gh workflow view deploy.yml
   gh workflow list
   gh repo view --json nameWithOwner
   gh api repos/owner/repo/actions/permissions

   # Should BLOCK:
   gh issue create --title "Story"
   gh project item-create
   gh api graphql -f query='mutation {createIssue...}'
   ```

5. **Document Changes**
   Add comments explaining:
   - Why certain patterns are allowed vs blocked
   - How to add new allowed patterns
   - Examples of each category
</implementation>

<output>
Modify the hook file:
- `~/.claude/hooks/validators/approach1-auto-approve.sh` - Updated with smart detection logic

Create documentation:
- `~/.claude/hooks/validators/README.md` - Explain the hook's logic, allowed vs blocked patterns, and how to extend it

Provide a summary of:
- What was changed
- Test results showing the fix works
- Guidelines for future hook maintenance
</output>

<verification>
Before declaring complete, verify:

1. **Hook allows administrative operations**:
   - Test: `gh api repos/o2alexanderfedin/cpp-to-c-website/pages -X POST -f build_type=workflow`
   - Expected: Command executes without being blocked

2. **Hook still blocks work item operations**:
   - Test: `gh issue create --title "Test"`
   - Expected: Blocked with helpful error message

3. **Read-only operations work**:
   - Test: `gh workflow list`
   - Expected: Command executes without being blocked

4. **Error messages are clear**:
   - Blocked commands show WHY and provide guidance
   - Users understand the distinction between allowed vs blocked operations

5. **Hook syntax is valid**:
   - Test the hook with various gh commands
   - No syntax errors or unexpected failures
</verification>

<success_criteria>
- ✓ Hook allows GitHub Pages API calls and other administrative operations
- ✓ Hook still blocks work item operations (issues, projects, stories, epics)
- ✓ Read-only gh commands are permitted
- ✓ Error messages clearly explain blocking rationale
- ✓ Hook logic is documented and maintainable
- ✓ All test scenarios pass
- ✓ Changes are committed following project git-flow
</success_criteria>

<constraints>
- Do not break existing work item operation blocking - that's the hook's primary purpose
- Maintain backward compatibility with existing scripts in `~/.claude/skills/lib/work-items-project/`
- Keep hook execution fast (< 100ms) to avoid slowing down CLI operations
- Use POSIX-compliant shell syntax for maximum compatibility
- Follow the project's CLAUDE.md guidelines for git workflow
</constraints>

<implementation_notes>
Why this matters:
- **Developer productivity**: Administrative tasks shouldn't require script abstraction overhead
- **Appropriate abstraction**: Script libraries are for repeated operations (work items), not one-time setup
- **Clarity of intent**: The hook should enforce patterns where they add value, not universally
- **Maintainability**: Clear allow/block logic makes the hook easier to extend

The key insight: **Work item operations** benefit from abstraction (repeated, structured, complex). **Administrative operations** don't (one-time, simple, varied). The hook should recognize this distinction.
</implementation_notes>
