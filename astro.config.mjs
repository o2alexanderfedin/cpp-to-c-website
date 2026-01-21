// @ts-check
import { defineConfig } from 'astro/config';

import react from '@astrojs/react';

// Vite plugin to set COOP/COEP headers for dev server
function crossOriginIsolationHeaders() {
  return {
    name: 'cross-origin-isolation-headers',
    configureServer(server) {
      server.middlewares.use((_req, res, next) => {
        res.setHeader('Cross-Origin-Opener-Policy', 'same-origin');
        res.setHeader('Cross-Origin-Embedder-Policy', 'credentialless');
        next();
      });
    }
  };
}

// https://astro.build/config
export default defineConfig({
  site: 'https://o2alexanderfedin.github.io',
  base: '/cpp-to-c-website',
  integrations: [react()],
  output: 'static',
  build: {
    inlineStylesheets: 'auto',
  },
  vite: {
    plugins: [crossOriginIsolationHeaders()],
    build: {
      rollupOptions: {
        external: ['/wasm/libclang.mjs', '/wasm/clang-headers.mjs']
      }
    },
    // Optimize WASM handling
    optimizeDeps: {
      exclude: ['@hupyy/cpptoc-wasm']
    },
    // Support for WASM files
    assetsInclude: ['**/*.wasm'],
    worker: {
      format: 'es'
    }
  }
});