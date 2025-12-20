---
type: meta-prompt
created: 2025-12-19
purpose: Comprehensive project effort analysis across all development stages
output: JSON file with detailed effort breakdown
---

# Project Effort Analysis Meta-Prompt

## Objective

Analyze the C++ to C transpiler project in the parent directory to determine total development effort (man-hours) across all stages. Output a comprehensive JSON file with detailed breakdowns.

## Three-Phase Approach

### Phase 1: Research & Data Collection (Exploration)

**Goal**: Gather all available planning, documentation, and code metrics.

**Tasks**:

1. **Documentation Analysis**:
   - Find and read: `ARCHITECTURE.md`, `README.md`, planning documents, epic/story files
   - Search for: timeline estimates, phase descriptions, completion reports
   - Extract: planned durations, actual completion dates, scope descriptions
   - Patterns to search: "week", "hours", "phase", "epic", "story", "sprint"

2. **Code Metrics Collection**:
   ```bash
   # Lines of code by language
   find ../src -type f \( -name "*.cpp" -o -name "*.h" \) | xargs wc -l
   find ../tests -type f \( -name "*.cpp" -o -name "*.h" \) | xargs wc -l
   find ../runtime -type f \( -name "*.c" -o -name "*.h" \) | xargs wc -l
   find ../examples -type f \( -name "*.cpp" -o -name "*.h" \) | xargs wc -l
   find ../docs -type f -name "*.md" | xargs wc -l

   # Commit analysis
   cd .. && git log --all --format="%ai|%an|%s" > /tmp/commits.txt
   cd .. && git log --all --numstat --format="" | awk '{added+=$1; removed+=$2} END {print "Added:",added,"Removed:",removed}'

   # File counts
   find ../src -type f | wc -l
   find ../tests -type f -name "*Test.cpp" -o -name "*test.cpp" | wc -l
   find ../examples -type f | wc -l
   ```

3. **Epic/Story Analysis**:
   - Search for: `EPIC_*.md`, `*_COMPLETION_REPORT.md`, GitHub issue references
   - Extract: story counts, epic scopes, completion statuses
   - Identify: features implemented, test coverage, documentation created

4. **Research Archive Mining**:
   - Explore: `research-archive/` or similar directories
   - Catalog: research phases, proof-of-concept work, architecture decisions
   - Extract: research topics, investigation depth, decision documentation

### Phase 2: Effort Estimation (Planning)

**Goal**: Calculate or estimate effort for each development stage.

**Industry Benchmarks** (use for estimation where data is missing):

- **Requirements & Analysis**: 10-15% of total development
- **Architecture & Design**: 15-20% of total development
- **Implementation**: 40-50% of total development
- **Testing**: 20-25% of total development
- **Documentation**: 10-15% of total development
- **Lines of Code productivity**:
  - C++ transpiler (complex): 20-50 LOC/day (160-400 LOC/week, ~6-15 LOC/hour)
  - Runtime library (critical): 30-60 LOC/day
  - Tests: 50-100 LOC/day
  - Documentation: 500-1000 words/day (~2-4 pages)

**Estimation Formulas**:

```javascript
// For documented phases with week estimates
effort_hours = weeks * 40  // Full-time work week

// For code without time estimates
loc_per_hour = 10  // Conservative for complex compiler work
effort_hours = total_loc / loc_per_hour

// For documentation
pages = total_words / 250  // Avg words per page
effort_hours = pages * 2    // 2 hours per page (research + writing)

// For tests
test_files = count_of_test_files
effort_hours_per_test = 4  // Average time to write test file
effort_hours = test_files * effort_hours_per_test

// For research
research_topics = count_of_research_documents
effort_hours_per_topic = 8  // Average research + documentation time
effort_hours = research_topics * effort_hours_per_topic
```

**Breakdown Categories**:

1. **Phase 0: Project Setup & Planning**
   - Initial research and feasibility
   - Project structure setup
   - Build system configuration

2. **Phase 1: Requirements & Research**
   - Requirements gathering
   - Technology research (Clang, LLVM)
   - Competitive analysis
   - Architecture research

3. **Phase 2: Core Architecture**
   - AST infrastructure design
   - Translation layer design
   - Runtime library design
   - Design documentation

4. **Phase 3: Feature Implementation**
   - Classes & inheritance
   - Templates & monomorphization
   - RAII & destructors
   - Exceptions
   - RTTI
   - Lambdas
   - Coroutines
   - Smart pointers
   - Virtual functions

5. **Phase 4: Runtime Library**
   - Exception runtime
   - RTTI runtime
   - Memory management
   - Runtime verification (Frama-C)

6. **Phase 5: Testing**
   - Unit tests (count test files)
   - Integration tests
   - Real-world examples
   - Performance benchmarks

7. **Phase 6: Documentation**
   - User guides
   - Architecture documentation
   - API documentation
   - Example documentation
   - FAQ

8. **Phase 7: Website & Deployment**
   - Website development
   - Playground implementation
   - CI/CD setup
   - GitHub Pages deployment

### Phase 3: JSON Generation (Execution)

**Goal**: Output comprehensive JSON file with all effort data.

**Output Location**: `../project_effort_analysis.json`

**JSON Structure**:

```json
{
  "project": {
    "name": "C++ to C Transpiler",
    "analysis_date": "2025-12-19",
    "repository": "cpp-to-c-transpiler",
    "analysis_version": "1.0"
  },
  "summary": {
    "total_effort_hours": 0,
    "total_effort_weeks": 0,
    "total_effort_months": 0,
    "start_date": "YYYY-MM-DD",
    "completion_date": "YYYY-MM-DD",
    "calendar_duration_weeks": 0,
    "team_size_equivalent": 0
  },
  "metrics": {
    "total_lines_of_code": 0,
    "source_code_loc": 0,
    "test_code_loc": 0,
    "runtime_code_loc": 0,
    "example_code_loc": 0,
    "documentation_words": 0,
    "documentation_pages": 0,
    "total_commits": 0,
    "total_files": 0,
    "test_files": 0,
    "source_files": 0,
    "epic_count": 0,
    "story_count": 0
  },
  "phases": [
    {
      "phase_number": 0,
      "phase_name": "Project Setup & Planning",
      "estimated_effort_hours": 0,
      "actual_effort_hours": 0,
      "effort_source": "documented|estimated",
      "start_date": "YYYY-MM-DD",
      "end_date": "YYYY-MM-DD",
      "deliverables": [],
      "notes": ""
    }
  ],
  "stages": {
    "requirements_analysis": {
      "effort_hours": 0,
      "percentage_of_total": 0,
      "deliverables": [],
      "estimation_method": ""
    },
    "architecture_design": {
      "effort_hours": 0,
      "percentage_of_total": 0,
      "deliverables": [],
      "estimation_method": ""
    },
    "implementation": {
      "effort_hours": 0,
      "percentage_of_total": 0,
      "features": [],
      "estimation_method": ""
    },
    "testing": {
      "effort_hours": 0,
      "percentage_of_total": 0,
      "test_categories": [],
      "estimation_method": ""
    },
    "documentation": {
      "effort_hours": 0,
      "percentage_of_total": 0,
      "document_types": [],
      "estimation_method": ""
    },
    "deployment": {
      "effort_hours": 0,
      "percentage_of_total": 0,
      "deliverables": [],
      "estimation_method": ""
    }
  },
  "features": [
    {
      "feature_name": "Classes & Inheritance",
      "epic_number": 0,
      "story_count": 0,
      "loc": 0,
      "test_loc": 0,
      "effort_hours": 0,
      "estimation_method": ""
    }
  ],
  "epics": [
    {
      "epic_number": 0,
      "epic_name": "",
      "stories": [],
      "total_effort_hours": 0,
      "status": "complete|in_progress|planned"
    }
  ],
  "effort_breakdown": {
    "by_phase": {},
    "by_stage": {},
    "by_feature": {},
    "by_epic": {}
  },
  "estimation_methodology": {
    "documented_estimates": "Description of estimates found in documentation",
    "code_metrics": "Description of LOC-based estimates",
    "industry_benchmarks": "Description of industry standard estimates used",
    "assumptions": []
  },
  "confidence_levels": {
    "overall": "high|medium|low",
    "documented_phases": "high|medium|low",
    "estimated_phases": "high|medium|low",
    "notes": ""
  }
}
```

## Execution Instructions

### Step 1: Data Collection Agent

Launch an Explore agent to gather all planning and metrics data:

```
Use Task tool with subagent_type='Explore' and thoroughness='very thorough'

Prompt: "Search the parent directory for all planning documents, epic/story files,
completion reports, and architecture documentation. Extract any timeline estimates,
effort calculations, or phase descriptions. Also collect code metrics: LOC counts by
category (src, tests, runtime, examples, docs), commit counts, file counts."
```

### Step 2: Metrics Calculation Scripts

Create and run analysis scripts:

```bash
#!/bin/bash
# Calculate all code metrics

# LOC by category
echo "Source LOC:"
find ../src -name "*.cpp" -o -name "*.h" | xargs wc -l | tail -1

echo "Test LOC:"
find ../tests -name "*.cpp" -o -name "*.h" | xargs wc -l | tail -1

echo "Runtime LOC:"
find ../runtime -name "*.c" -o -name "*.h" | xargs wc -l | tail -1

echo "Example LOC:"
find ../examples -name "*.cpp" -o -name "*.h" | xargs wc -l | tail -1

echo "Documentation words:"
find ../docs -name "*.md" -exec wc -w {} + | tail -1

# Git metrics
cd ..
echo "Total commits:"
git log --all --oneline | wc -l

echo "First commit:"
git log --all --reverse --format="%ai" | head -1

echo "Last commit:"
git log --all --format="%ai" | head -1

echo "Unique contributors:"
git log --all --format="%an" | sort -u | wc -l
```

### Step 3: Effort Calculation

For each category:

1. **If documented**: Use documented estimate
2. **If not documented**: Apply formula based on metrics
3. **Validate**: Check against industry benchmarks
4. **Document**: Note estimation method in JSON

### Step 4: JSON Assembly

Create the complete JSON structure with:
- All collected data
- All calculated estimates
- Clear attribution of estimation methods
- Confidence levels
- Assumptions documented

### Step 5: Validation

Review the output JSON for:
- Completeness (all sections filled)
- Reasonableness (totals match industry norms)
- Consistency (sum of parts equals total)
- Documentation (all estimates explained)

## Deliverables

1. **Primary Output**: `../project_effort_analysis.json` - Complete effort breakdown
2. **Supporting Output**: `../effort_analysis_summary.md` - Human-readable summary
3. **Raw Data**: `../effort_metrics_raw.txt` - All collected metrics

## Success Criteria

- ✅ All project phases identified and quantified
- ✅ Both documented and estimated efforts calculated
- ✅ Clear methodology documented for all estimates
- ✅ Industry benchmarks applied where appropriate
- ✅ Total effort makes sense (reasonable for project scope)
- ✅ JSON is valid and complete
- ✅ Confidence levels assigned appropriately

## Notes for Executor

- **Be thorough**: Check research-archive, docs, epics, completion reports
- **Be conservative**: When estimating, err on the high side
- **Show your work**: Document every estimation method
- **Use scripts**: Automate metric collection for accuracy
- **Cross-validate**: Compare multiple estimation methods where possible
- **Industry context**: A compiler/transpiler is complex software (low LOC/hour expected)
