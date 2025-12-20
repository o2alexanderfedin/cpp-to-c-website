<objective>
Research how to detect execution context in Claude Code PreToolUse hooks to enable context-aware blocking behavior.

**Problem**: The current PreToolUse hook at `~/.claude/hooks/validators/approach1-auto-approve.sh` blocks `gh workflow run` and other legitimate GitHub CLI commands, even when used in normal development workflows. It should ONLY block when invoked from work item execution contexts (epic/user-story/task/spike/bug slash commands and skills).

**Goal**: Discover reliable methods to detect when a hook is being executed from within specific slash commands or skills, enabling the hook to selectively enforce script abstraction patterns only in those contexts.

**Why this matters**: Hooks that block too broadly reduce developer productivity and force workarounds. Context-aware hooks maintain abstraction patterns where needed while allowing normal CLI usage elsewhere.
</objective>

<context>
**Current hook behavior**:
- Blocks ALL `gh` commands except admin operations and read-only queries
- No context detection - applies same rules everywhere
- Location: `~/.claude/hooks/validators/approach1-auto-approve.sh`

**Desired behavior**:
- Block `gh` work item operations ONLY when invoked from:
  - `/execute-epic`
  - `/execute-user-story`
  - `/execute-next-story`
  - `execute-epic` skill
  - `execute-user-story` skill
  - Related work item execution contexts
- Allow ALL `gh` commands in normal usage (chat, other slash commands, etc.)

**Project context**:
Read hook documentation and examples:
@~/.claude/hooks/validators/approach1-auto-approve.sh
@~/.claude/hooks/validators/README.md
@~/.claude/skills/execute-epic/
@~/.claude/skills/execute-user-story/
</context>

<research_requirements>
**Primary Questions**:
1. What environment variables or context is available in PreToolUse hook execution?
2. How can a hook detect which slash command or skill invoked it?
3. Are there execution stack traces, parent process info, or other identifying signals?
4. What patterns do existing Claude Code hooks use for context detection?
5. Can we pass context markers from slash commands/skills to hooks?

**Approach**:
1. **Read hook documentation** - Check for official context detection mechanisms
2. **Examine environment variables** - What's available during hook execution?
3. **Analyze existing hooks** - Look for context-aware patterns in Claude Code
4. **Test with experiments** - Use a separate Claude instance to test detection methods
5. **Review slash command/skill invocation** - How do they call Claude? Can they set markers?

**Depth**: Deep dive - exhaustively explore all detection methods with concrete examples
</research_requirements>

<research_methodology>
<phase1_documentation>
**Read official hook documentation**:
- How are hooks invoked? What context is passed?
- Are there documented environment variables?
- Is there a caller identification mechanism?

Search in:
- `~/.claude/hooks/` documentation
- Claude Code CLI docs (if accessible)
- Hook validator README files
</phase1_documentation>

<phase2_environment>
**Examine available environment variables**:

Create a test hook to dump all environment variables:
```bash
# Test hook: /tmp/test-hook.sh
#!/bin/bash
echo "=== Environment Variables ==="
env | sort
echo "=== Process Info ==="
echo "PID: $$"
echo "PPID: $PPID"
ps -p $$ -o args=
ps -p $PPID -o args=
echo "=== Call Stack ==="
caller 2>/dev/null || echo "No caller info"
```

Run this from different contexts:
1. Normal chat
2. Within a slash command
3. Within a skill

Compare outputs to identify context markers.
</phase2_environment>

<phase3_code_analysis>
**Analyze existing hooks for patterns**:

Search for context-aware hooks:
```bash
# Find all hooks
find ~/.claude/hooks -name "*.sh" -type f

# Search for environment variable usage
grep -r "CLAUDE_" ~/.claude/hooks/
grep -r "SKILL_" ~/.claude/hooks/
grep -r "COMMAND_" ~/.claude/hooks/

# Look for conditional logic
grep -r "if.*CLAUDE\|if.*SKILL" ~/.claude/hooks/
```

Document any context detection patterns found.
</phase3_code_analysis>

<phase4_slash_command_analysis>
**Examine slash command invocation**:

Read slash command files to understand how they invoke Claude:
- Do they set environment variables?
- Do they modify the prompt/context?
- Is there a skill wrapping mechanism?

Check:
- `/execute-epic` command definition
- `/execute-user-story` command definition
- Skill invocation mechanisms
</phase4_slash_command_analysis>

<phase5_experimentation>
**Test detection methods**:

Use a separate Claude instance to test:

1. **Environment variable test**:
   - Create hook that echoes specific env vars
   - Run from different contexts
   - Document which vars are set where

2. **Process tree test**:
   - Check if parent process gives hints
   - Test `pstree`, `ps`, process names

3. **Marker injection test**:
   - Can slash commands set a marker env var before invoking?
   - Test modifying a slash command to export `CLAUDE_EXECUTION_CONTEXT=epic`

4. **Prompt analysis test**:
   - Can hooks access the prompt/context that invoked them?
   - Check for system messages or skill metadata
</phase5_experimentation>

<phase6_solution_synthesis>
After gathering all data, synthesize findings into:

1. **Recommended approach**: Best method for context detection
2. **Alternative approaches**: Backup options if primary fails
3. **Implementation examples**: Concrete code snippets
4. **Trade-offs**: Pros/cons of each method
5. **Reliability assessment**: How robust is each approach?
</phase6_solution_synthesis>
</research_methodology>

<output_specification>
Create comprehensive research output: `.prompts/001-hook-context-detection-research/hook-context-detection-research.md`

Use streaming write technique to avoid memory issues:
- Write incrementally as you discover information
- Don't accumulate everything in memory
- Read back and verify after each phase

**Structure**:
```xml
<research_findings>
  <executive_summary>
    One-paragraph answer to: "How can hooks detect execution context?"
  </executive_summary>

  <environment_variables>
    <available_vars>
      List of all environment variables available in hook execution
    </available_vars>
    <context_markers>
      Which vars (if any) indicate execution context
    </context_markers>
  </environment_variables>

  <process_information>
    <parent_process>What parent process info is available</parent_process>
    <process_tree>Can we walk the process tree for context</process_tree>
  </process_information>

  <existing_patterns>
    Examples from other Claude Code hooks that do context detection
  </existing_patterns>

  <slash_command_mechanics>
    How slash commands invoke Claude and whether they can pass context
  </slash_command_mechanics>

  <experimentation_results>
    <test_name>Results from each experiment</test_name>
  </experimentation_results>

  <recommended_solutions>
    <primary>
      <method>Description of best approach</method>
      <implementation>Code example</implementation>
      <reliability>High/Medium/Low with rationale</reliability>
    </primary>
    <alternatives>
      <option>...</option>
    </alternatives>
  </recommended_solutions>

  <implementation_guide>
    Step-by-step guide to implement the recommended solution
  </implementation_guide>

  <verification_checklist>
    - [ ] Environment variables documented
    - [ ] Process info tested
    - [ ] Existing patterns analyzed
    - [ ] Experiments completed
    - [ ] Solution tested in separate instance
    - [ ] Implementation guide validated
  </verification_checklist>

  <quality_report>
    <verified_claims>
      List of findings verified through testing
    </verified_claims>
    <assumed_claims>
      List of findings based on documentation/inference (not directly tested)
    </assumed_claims>
    <sources_consulted>
      - Source 1 with URL/path
      - Source 2 with URL/path
    </sources_consulted>
  </quality_report>

  <metadata>
    <confidence>high|medium|low - overall confidence in findings</confidence>
    <dependencies>
      What's needed to implement this solution
    </dependencies>
    <open_questions>
      What remains uncertain or requires user input
    </open_questions>
    <assumptions>
      What was assumed during research
    </assumptions>
  </metadata>
</research_findings>
```

Also create: `.prompts/001-hook-context-detection-research/SUMMARY.md`

**SUMMARY.md structure**:
```markdown
# Hook Context Detection Research

**[One substantive sentence describing the key finding]**

## Version
v1 - Initial research

## Key Findings
- [Actionable bullet point 1]
- [Actionable bullet point 2]
- [Actionable bullet point 3]

## Decisions Needed
[What requires user input, or "None" if ready to proceed]

## Blockers
[External impediments, or "None"]

## Next Step
[Concrete forward action - e.g., "Create implementation plan" or "Test approach X"]
```
</output_specification>

<verification>
**Before declaring complete, verify**:

1. **Comprehensiveness**:
   - All 6 research phases completed
   - Environment variables documented
   - Process info tested
   - Existing hooks analyzed
   - Experiments run and documented
   - Solution synthesized

2. **Quality**:
   - Findings are actionable (not just theoretical)
   - Code examples are concrete and testable
   - Reliability assessments are honest
   - Trade-offs clearly explained

3. **Outputs**:
   - `hook-context-detection-research.md` created with full XML structure
   - `SUMMARY.md` created with substantive one-liner
   - Both files validated for completeness

4. **Metadata**:
   - Confidence level assigned with rationale
   - Dependencies identified
   - Open questions documented
   - Assumptions stated

5. **Pre-submission QA**:
   - Re-read executive summary - does it answer the question?
   - Check verification checklist - all items checked?
   - Review quality report - verified vs assumed claims clear?
   - Test recommended solution code snippets for syntax errors
</verification>

<success_criteria>
- ✓ All environment variables available in hooks documented
- ✓ Process tree analysis completed
- ✓ Existing Claude Code hook patterns analyzed
- ✓ Slash command invocation mechanisms understood
- ✓ Experiments conducted with test hooks
- ✓ Recommended solution identified with implementation example
- ✓ Alternative approaches documented
- ✓ Trade-offs and reliability assessed
- ✓ Implementation guide created
- ✓ SUMMARY.md created with substantive findings
- ✓ Quality report distinguishes verified from assumed claims
</success_criteria>

<constraints>
- Use separate Claude instance for experiments (don't modify production hooks during research)
- Don't make assumptions - test everything possible
- Document sources for all claims
- Provide code examples for all recommendations
- Be honest about limitations and unknowns
</constraints>

<intelligence_notes>
**Why exhaustive research matters**:
- Hook context detection is non-trivial - no obvious API
- Wrong approach could be brittle or unreliable
- Multiple approaches may exist with different trade-offs
- Need to validate with real experiments, not just documentation

**Research depth justification**:
- Deep dive requested by user
- Critical functionality (affects all work item execution)
- High impact of getting it wrong (blocking or not blocking inappropriately)
- Investment in thorough research pays off in reliable implementation
</intelligence_notes>
