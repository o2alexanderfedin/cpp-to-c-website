import { defineConfig } from 'vitest/config';
import react from '@vitejs/plugin-react';
import path from 'path';

export default defineConfig({
    plugins: [react()],
    test: {
        globals: true,
        environment: 'jsdom',
        include: [
            'src/**/*.test.ts',
            'src/**/*.test.tsx',
            'test/**/*.test.ts',
            'test/**/*.test.tsx'
        ],
        setupFiles: ['./vitest.setup.ts'],
        coverage: {
            provider: 'v8',
            reporter: ['text', 'json', 'html'],
            include: ['src/**/*.ts', 'src/**/*.tsx'],
            exclude: ['src/**/*.test.ts', 'src/**/*.test.tsx', 'src/**/*.spec.ts'],
        },
        testTimeout: 30000,
    },
    resolve: {
        alias: {
            '@': path.resolve(__dirname, './src'),
            '@test': path.resolve(__dirname, './test'),
        },
    },
});
