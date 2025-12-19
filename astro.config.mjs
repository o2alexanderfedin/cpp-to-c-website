// @ts-check
import { defineConfig } from 'astro/config';

import react from '@astrojs/react';

// https://astro.build/config
export default defineConfig({
  site: 'https://o2alexanderfedin.github.io',
  base: '/cpp-to-c',
  integrations: [react()],
  output: 'static',
  build: {
    inlineStylesheets: 'auto',
  },
});