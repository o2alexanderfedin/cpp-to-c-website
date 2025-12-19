# C++ to C Transpiler Website

This is the documentation and demonstration website for the C++ to C Transpiler, built with Astro and deployed on Vercel.

**Note**: This repository is a git submodule of the main [cpp-to-c-transpiler](https://github.com/o2alexanderfedin/cpp-to-c-transpiler) repository.

## Technology Stack

- **Framework**: Astro 4.x with React integration
- **TypeScript**: Strict mode enabled
- **Deployment**: Vercel with COOP/COEP headers for WebAssembly support
- **Code Editor**: CodeMirror 6 (Phase 3)

## Project Structure

```
website/
├── src/
│   ├── layouts/          # Layout components
│   │   └── MainLayout.astro
│   ├── pages/            # Routes
│   │   ├── index.astro       # Home page
│   │   ├── playground.astro  # Interactive playground (Phase 3)
│   │   ├── docs.astro        # Documentation (Phase 4)
│   │   └── examples.astro    # Example gallery (Phase 5)
│   └── components/       # React components (coming in Phase 3)
├── public/               # Static assets
├── astro.config.mjs      # Astro configuration
├── vercel.json           # Vercel deployment config with COOP/COEP headers
├── tsconfig.json         # TypeScript configuration
└── package.json
```

## Development

### Prerequisites

- Node.js 18+
- npm or yarn

### Setup

```bash
# Install dependencies
npm install

# Start development server
npm run dev

# Build for production
npm run build

# Preview production build
npm run preview
```

### Development Server

The development server runs at `http://localhost:4321`

## Deployment

### Vercel Deployment

The website is automatically deployed to Vercel with proper COOP/COEP headers for WebAssembly multi-threading support.

**Headers Configuration** (`vercel.json`):
```json
{
  "headers": [
    {
      "source": "/(.*)",
      "headers": [
        {
          "key": "Cross-Origin-Opener-Policy",
          "value": "same-origin"
        },
        {
          "key": "Cross-Origin-Embedder-Policy",
          "value": "credentialless"
        }
      ]
    }
  ]
}
```

### Manual Deployment

1. Install Vercel CLI: `npm install -g vercel`
2. Deploy from website directory: `vercel`
3. Follow prompts to link project

### Verifying Headers

After deployment, verify cross-origin isolation is working:

1. Open the deployed website in your browser
2. Open DevTools Console
3. Run: `typeof SharedArrayBuffer !== 'undefined'`
4. Should return `true`

Or check the console logs on page load:
```
✓ Cross-origin isolation enabled - WebAssembly ready!
```

## Phase Implementation Status

- ✅ **Phase 1: Foundation & Setup** (COMPLETE)
  - Astro project initialized
  - TypeScript configured in strict mode
  - React integration added
  - Vercel deployment configured with COOP/COEP headers
  - Basic routes created (/, /playground, /docs, /examples)
  - Responsive layout implemented

- 🔄 **Phase 2: WebAssembly Integration** (Next)
  - Compile transpiler to WebAssembly
  - WASM loader implementation
  - Transpiler JavaScript API

- ⏳ **Phase 3: Interactive Code Playground** (Upcoming)
  - CodeMirror 6 integration
  - Split-pane editor
  - Real-time transpilation

- ⏳ **Phase 4: Documentation Content** (Upcoming)
  - Migrate existing docs to MDX
  - API reference
  - Feature guides

- ⏳ **Phase 5: Example Gallery & Polish** (Upcoming)
  - Real-world examples
  - Performance optimization
  - SEO and accessibility

## Repository Structure

This website repository is included as a git submodule in the main transpiler project:

```
cpp-to-c-transpiler/         # Main transpiler repository
├── src/                     # Transpiler C++ source
├── include/                 # Transpiler headers
├── tests/                   # Transpiler tests
├── docs/                    # Markdown documentation
└── website/                 # Git submodule → cpp-to-c-website (THIS REPO)
```

### Working with the Submodule

When working on the website:

```bash
# Clone the main repository with submodules
git clone --recursive https://github.com/o2alexanderfedin/cpp-to-c-transpiler.git

# Or initialize submodules after cloning
git submodule update --init --recursive

# Make changes in the website directory
cd website
git checkout -b feature/my-changes
# ... make changes ...
git commit -am "feat: add new feature"
git push origin feature/my-changes

# Update main repository to reference new commit
cd ..
git add website
git commit -m "chore: update website submodule"
git push
```

## Scripts

- `npm run dev` - Start development server
- `npm run build` - Build for production
- `npm run preview` - Preview production build locally
- `npm run astro` - Run Astro CLI commands

## Browser Requirements

For WebAssembly multi-threading support (Phase 2+):

- Chrome 92+
- Firefox 90+
- Safari 15.2+
- Edge 92+

Older browsers will show a compatibility warning.

## Contributing

This is a solo developer project. For issues or suggestions, please open an issue in the main repository.

## License

MIT License - See main repository for details.
