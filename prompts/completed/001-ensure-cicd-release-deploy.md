<objective>
Ensure the CI/CD pipeline is properly configured to build and deploy the Astro website to GitHub Pages when code is pushed to release/** branches.

This verification ensures that the deployment automation is working correctly and follows best practices for release workflows. The configuration should be production-ready, secure, and reliable.
</objective>

<context>
This is an Astro-based website project that uses GitHub Actions for CI/CD and GitHub Pages for hosting.

Project details:
- Tech stack: Astro v5.16.6 with React integration
- Build command: `npm run build`
- Output directory: `./dist`
- Current working directory: `~/Projects/hapyy/hupyy-cpp-to-c/website`

Examine existing workflow configuration:
@.github/workflows/deploy.yml

Review project configuration:
@package.json
@astro.config.mjs (if exists)
</context>

<requirements>
1. **Verify Trigger Configuration**: Confirm workflow triggers on `push` to `release/**` branches
2. **Validate Build Process**: Ensure build job properly installs dependencies and builds the Astro site
3. **Check Deployment Setup**: Verify deploy job has correct permissions and uploads to GitHub Pages
4. **Test Workflow Syntax**: Validate YAML syntax is correct and follows GitHub Actions best practices
5. **Verify Permissions**: Ensure GITHUB_TOKEN has necessary permissions (contents: read, pages: write, id-token: write)
6. **Check Concurrency**: Verify only one deployment runs at a time to prevent conflicts
7. **Validate Artifact Handling**: Ensure build artifacts are properly uploaded and deployed
</requirements>

<verification_steps>
Follow these steps to thoroughly verify the configuration:

1. **Read Current Workflow**
   - Examine `.github/workflows/deploy.yml`
   - Identify all jobs, steps, and configurations

2. **Validate Workflow Structure**
   - Confirm trigger: `on.push.branches` includes `'release/**'`
   - Verify build job builds the Astro site correctly
   - Check deploy job depends on build job (`needs: build`)
   - Ensure proper permissions are set at workflow level

3. **Check Best Practices**
   - Concurrency control is configured to prevent multiple simultaneous deployments
   - Node.js version is specified and modern (v20+)
   - npm cache is configured for faster builds
   - Working directory is properly set for all steps
   - Artifact upload path matches build output directory (`dist`)

4. **Identify Potential Improvements**
   - Missing error handling or notifications
   - Missing build caching for dependencies
   - Missing environment-specific configurations
   - Missing status badges or documentation

5. **Test Workflow Validity** (optional but recommended)
   - Run: `!gh workflow view deploy.yml` to check if workflow is recognized
   - Run: `!gh workflow list` to see all workflows
</verification_steps>

<output>
Provide a comprehensive report with these sections:

1. **Current Status**: Summary of existing CI/CD configuration
2. **Verification Results**: What works correctly
3. **Issues Found**: Any problems or missing configurations (if any)
4. **Recommendations**: Suggested improvements for robustness, security, or performance
5. **Action Items**: Specific changes to implement (if any)

If any issues are found or improvements are needed, implement the fixes directly to the workflow file.

If everything is correctly configured, create a brief verification document:
`./docs/cicd-verification.md` - Document the verification results and configuration details
</output>

<success_criteria>
- ✓ Workflow triggers on `release/**` branches
- ✓ Build job successfully builds Astro site
- ✓ Deploy job has correct permissions for GitHub Pages
- ✓ Concurrency control prevents deployment conflicts
- ✓ Artifact upload and deployment are properly configured
- ✓ Workflow follows GitHub Actions and Astro best practices
- ✓ Any identified issues have been fixed
- ✓ Verification results are documented
</success_criteria>

<constraints>
- Follow the project's CLAUDE.md guidelines for git workflow and testing
- Do not modify the core build process unless issues are found
- Maintain compatibility with Astro v5.16.6
- Ensure changes are backward compatible with existing deployments
- Use relative paths for all file references
</constraints>

<implementation_notes>
Why this verification matters:
- **Automation reliability**: Ensures releases deploy automatically without manual intervention
- **Production safety**: Prevents broken deployments through proper validation and concurrency control
- **Developer experience**: Fast, reliable deployments reduce friction in the release process
- **Audit trail**: Documented verification provides confidence in the deployment infrastructure

When examining the workflow, pay special attention to:
- The `release/**` pattern matches the git-flow release branch naming convention
- Permissions are minimal but sufficient (principle of least privilege)
- Build artifacts are ephemeral and properly cleaned up
- GitHub Pages environment is correctly configured
</implementation_notes>
