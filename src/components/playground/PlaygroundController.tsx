import React, { useState, useCallback } from 'react';
import { DirectorySelector } from './DirectorySelector';
import { ProgressIndicator } from './ProgressIndicator';
import { ErrorDisplay } from './ErrorDisplay';
import { TranspileService } from '../../features/transpile/TranspileService';
import { downloadAsZip } from '../../lib/playground/fileDownload';
import type { ITranspiler } from '../../core/interfaces/ITranspiler';
import type { IFileSystem } from '../../core/interfaces/IFileSystem';
import type { TranspileError } from '../../features/transpile/types';

export interface PlaygroundControllerProps {
    transpiler: ITranspiler;
    fileSystem: IFileSystem;
}

type TranspileState = 'idle' | 'running' | 'completed' | 'cancelled' | 'error';

export const PlaygroundController: React.FC<PlaygroundControllerProps> = ({
    transpiler,
    fileSystem,
}) => {
    const [directoryHandle, setDirectoryHandle] = useState<FileSystemDirectoryHandle | null>(null);
    const [directoryPath, setDirectoryPath] = useState<string>('');
    const [transpileState, setTranspileState] = useState<TranspileState>('idle');
    const [progress, setProgress] = useState({ current: 0, total: 0 });
    const [currentFile, setCurrentFile] = useState<string>('');
    const [errors, setErrors] = useState<TranspileError[]>([]);
    const [statusMessage, setStatusMessage] = useState<string>('');
    const [isCancelling, setIsCancelling] = useState(false);
    const [abortController, setAbortController] = useState<AbortController | null>(null);

    const handleDirectorySelected = useCallback((handle: FileSystemDirectoryHandle) => {
        setDirectoryHandle(handle);
        setDirectoryPath(handle.name);
        setErrors([]);
        setTranspileState('idle');
        setProgress({ current: 0, total: 0 });
    }, []);

    const handleTranspile = useCallback(async () => {
        if (!directoryHandle) return;

        setTranspileState('running');
        setErrors([]);
        setProgress({ current: 0, total: 0 });
        setCurrentFile('');
        setIsCancelling(false);

        const controller = new AbortController();
        setAbortController(controller);

        try {
            setStatusMessage('Scanning directory...');

            // Get all files in directory
            const files = await fileSystem.traverseDirectory(directoryHandle);

            // Filter C++ files
            const cppFiles = files.filter(
                file =>
                    !file.isDirectory &&
                    (file.path.endsWith('.cpp') ||
                        file.path.endsWith('.cc') ||
                        file.path.endsWith('.cxx') ||
                        file.path.endsWith('.h') ||
                        file.path.endsWith('.hpp') ||
                        file.path.endsWith('.hxx'))
            );

            setProgress({ current: 0, total: cppFiles.length });
            setStatusMessage(`Processing ${cppFiles.length} files...`);

            const collectedErrors: TranspileError[] = [];
            const transpiledFiles = new Map<string, string>();
            let processedCount = 0;

            // Process each file
            for (const file of cppFiles) {
                if (controller.signal.aborted) {
                    throw new Error('Cancelled');
                }

                setCurrentFile(file.name);

                try {
                    // Read file
                    const content = await fileSystem.readFile(file.path);

                    // Transpile
                    const result = await transpiler.transpile(content, {
                        sourcePath: file.path,
                    });

                    // Collect errors if any
                    if (!result.success) {
                        collectedErrors.push({
                            filePath: file.path,
                            message: result.error || 'Unknown transpilation error',
                        });
                    }

                    // Collect transpiled output
                    if (result.success && result.cCode) {
                        // Convert .cpp/.cc/.cxx to .c for output filename
                        const outputPath = file.path
                            .replace(/\.cpp$/, '.c')
                            .replace(/\.cc$/, '.c')
                            .replace(/\.cxx$/, '.c');
                        transpiledFiles.set(outputPath, result.cCode);
                    }
                } catch (err: any) {
                    collectedErrors.push({
                        filePath: file.path,
                        message: err.message || 'Unknown error',
                    });
                }

                processedCount++;
                setProgress({ current: processedCount, total: cppFiles.length });
            }

            setErrors(collectedErrors);
            setTranspileState('completed');
            setStatusMessage(
                collectedErrors.length === 0
                    ? 'Transpilation completed successfully!'
                    : `Transpilation completed with ${collectedErrors.length} error${collectedErrors.length === 1 ? '' : 's'}`
            );

            // Download transpiled files if any were successfully transpiled
            if (transpiledFiles.size > 0) {
                try {
                    const zipName = directoryPath || 'transpiled-project';
                    await downloadAsZip(transpiledFiles, zipName);
                } catch (downloadErr: any) {
                    console.error('Failed to download ZIP:', downloadErr);
                    // Don't fail the entire transpilation if download fails
                    setStatusMessage(
                        prevMsg =>
                            `${prevMsg} (Note: Download failed - ${downloadErr.message || 'Unknown error'})`
                    );
                }
            }
        } catch (err: any) {
            if (err.message === 'Cancelled') {
                setTranspileState('cancelled');
                setStatusMessage('Transpilation cancelled');
            } else {
                setTranspileState('error');
                setStatusMessage(`Error: ${err.message}`);
                setErrors([
                    {
                        filePath: '',
                        message: err.message || 'Unknown error occurred',
                    },
                ]);
            }
        } finally {
            setAbortController(null);
            setCurrentFile('');
            setIsCancelling(false);
        }
    }, [directoryHandle, fileSystem, transpiler]);

    const handleCancel = useCallback(() => {
        if (abortController) {
            setIsCancelling(true);
            abortController.abort();
        }
    }, [abortController]);

    const handleCopyErrors = useCallback((text: string) => {
        navigator.clipboard.writeText(text);
    }, []);

    const isTranspiling = transpileState === 'running';
    const showProgress = isTranspiling || transpileState === 'completed';

    return (
        <div role="main" aria-label="C++ to C Playground">
            <div className="playground-container">
                <header className="playground-header">
                    <h1>C++ to C Transpilation Playground</h1>
                    <p>Select a directory containing C++ files to transpile them to C</p>
                </header>

                <section className="directory-section">
                    <h2>1. Select Directory</h2>
                    <DirectorySelector
                        onDirectorySelected={handleDirectorySelected}
                        selectedPath={directoryPath}
                    />
                </section>

                {directoryHandle && (
                    <section className="transpile-section">
                        <h2>2. Transpile</h2>
                        <button
                            onClick={handleTranspile}
                            disabled={isTranspiling}
                            aria-label="Start transpilation"
                            className="transpile-button"
                        >
                            {isTranspiling ? 'Transpiling...' : 'Transpile Project'}
                        </button>
                    </section>
                )}

                {showProgress && (
                    <section className="progress-section">
                        <h2>3. Progress</h2>
                        <ProgressIndicator
                            current={progress.current}
                            total={progress.total}
                            currentFile={currentFile}
                            onCancel={isTranspiling ? handleCancel : undefined}
                            isCancelling={isCancelling}
                            statusMessage={statusMessage}
                        />
                    </section>
                )}

                {(transpileState === 'completed' || transpileState === 'error') && (
                    <div role="status" aria-live="polite" className="status-announcement">
                        {statusMessage}
                    </div>
                )}

                <section className="errors-section">
                    <h2>4. Results</h2>
                    <ErrorDisplay errors={errors} onCopy={handleCopyErrors} showSearch={errors.length > 5} />
                </section>
            </div>

            <style>{`
                .playground-container {
                    max-width: 1200px;
                    margin: 0 auto;
                    padding: 2rem;
                    display: flex;
                    flex-direction: column;
                    gap: 2rem;
                }

                .playground-header {
                    text-align: center;
                    margin-bottom: 1rem;
                }

                .playground-header h1 {
                    margin: 0 0 0.5rem 0;
                    font-size: 2rem;
                    color: #333;
                }

                .playground-header p {
                    margin: 0;
                    color: #666;
                }

                .directory-section,
                .transpile-section,
                .progress-section,
                .errors-section {
                    border: 1px solid #ddd;
                    border-radius: 8px;
                    padding: 1.5rem;
                    background-color: #fff;
                }

                section h2 {
                    margin: 0 0 1rem 0;
                    font-size: 1.25rem;
                    color: #333;
                }

                .transpile-button {
                    width: 100%;
                    padding: 1rem 2rem;
                    font-size: 1.125rem;
                    font-weight: 500;
                    background-color: #4caf50;
                    color: white;
                    border: none;
                    border-radius: 4px;
                    cursor: pointer;
                    transition: background-color 0.2s;
                }

                .transpile-button:hover:not(:disabled) {
                    background-color: #45a049;
                }

                .transpile-button:disabled {
                    background-color: #ccc;
                    cursor: not-allowed;
                }

                .transpile-button:focus {
                    outline: 2px solid #4caf50;
                    outline-offset: 2px;
                }

                .status-announcement {
                    padding: 1rem;
                    background-color: #e8f5e9;
                    border: 1px solid #4caf50;
                    border-radius: 4px;
                    text-align: center;
                    font-weight: 500;
                }

                @media (max-width: 768px) {
                    .playground-container {
                        padding: 1rem;
                    }

                    .playground-header h1 {
                        font-size: 1.5rem;
                    }

                    section {
                        padding: 1rem;
                    }
                }
            `}</style>
        </div>
    );
};
