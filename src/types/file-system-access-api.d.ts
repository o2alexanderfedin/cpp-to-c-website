/**
 * TypeScript type definitions for File System Access API
 *
 * @see https://developer.mozilla.org/en-US/docs/Web/API/File_System_Access_API
 * @see https://wicg.github.io/file-system-access/
 */

/**
 * Permission state for File System Access API
 */
type FileSystemPermissionState = 'granted' | 'denied' | 'prompt';

/**
 * Permission mode for File System Access API
 */
type FileSystemPermissionMode = 'read' | 'readwrite';

/**
 * Permission descriptor for File System Access API
 */
interface FileSystemHandlePermissionDescriptor {
  mode?: FileSystemPermissionMode;
}

/**
 * Base interface for file and directory handles
 */
interface FileSystemHandle {
  readonly kind: 'file' | 'directory';
  readonly name: string;

  /**
   * Check if this handle represents the same entry as another handle
   */
  isSameEntry(other: FileSystemHandle): Promise<boolean>;

  /**
   * Query the current permission state
   */
  queryPermission(descriptor?: FileSystemHandlePermissionDescriptor): Promise<FileSystemPermissionState>;

  /**
   * Request permission from the user
   */
  requestPermission(descriptor?: FileSystemHandlePermissionDescriptor): Promise<FileSystemPermissionState>;
}

/**
 * Handle for a file
 */
interface FileSystemFileHandle extends FileSystemHandle {
  readonly kind: 'file';

  /**
   * Get the File object for this file handle
   */
  getFile(): Promise<File>;

  /**
   * Create a writable stream for this file
   */
  createWritable(options?: FileSystemCreateWritableOptions): Promise<FileSystemWritableFileStream>;
}

/**
 * Options for creating a writable stream
 */
interface FileSystemCreateWritableOptions {
  keepExistingData?: boolean;
}

/**
 * Writable stream for a file
 */
interface FileSystemWritableFileStream extends WritableStream {
  /**
   * Write data to the file
   */
  write(data: BufferSource | Blob | string | WriteParams): Promise<void>;

  /**
   * Seek to a position in the file
   */
  seek(position: number): Promise<void>;

  /**
   * Truncate the file to a given size
   */
  truncate(size: number): Promise<void>;

  /**
   * Close the stream
   */
  close(): Promise<void>;
}

/**
 * Parameters for write operations
 */
interface WriteParams {
  type: 'write' | 'seek' | 'truncate';
  data?: BufferSource | Blob | string;
  position?: number;
  size?: number;
}

/**
 * Handle for a directory
 */
interface FileSystemDirectoryHandle extends FileSystemHandle {
  readonly kind: 'directory';

  /**
   * Get a file handle from this directory
   */
  getFileHandle(name: string, options?: FileSystemGetFileOptions): Promise<FileSystemFileHandle>;

  /**
   * Get a directory handle from this directory
   */
  getDirectoryHandle(name: string, options?: FileSystemGetDirectoryOptions): Promise<FileSystemDirectoryHandle>;

  /**
   * Remove an entry from this directory
   */
  removeEntry(name: string, options?: FileSystemRemoveOptions): Promise<void>;

  /**
   * Resolve the path of a handle relative to this directory
   */
  resolve(possibleDescendant: FileSystemHandle): Promise<string[] | null>;

  /**
   * Async iterator for entries
   */
  entries(): AsyncIterableIterator<[string, FileSystemHandle]>;

  /**
   * Async iterator for keys (entry names)
   */
  keys(): AsyncIterableIterator<string>;

  /**
   * Async iterator for values (handles)
   */
  values(): AsyncIterableIterator<FileSystemHandle>;

  /**
   * Async iterator (default)
   */
  [Symbol.asyncIterator](): AsyncIterableIterator<[string, FileSystemHandle]>;
}

/**
 * Options for getting a file handle
 */
interface FileSystemGetFileOptions {
  create?: boolean;
}

/**
 * Options for getting a directory handle
 */
interface FileSystemGetDirectoryOptions {
  create?: boolean;
}

/**
 * Options for removing an entry
 */
interface FileSystemRemoveOptions {
  recursive?: boolean;
}

/**
 * Options for directory picker
 */
interface DirectoryPickerOptions {
  id?: string;
  mode?: FileSystemPermissionMode;
  startIn?: FileSystemHandle | WellKnownDirectory;
}

/**
 * Well-known directories
 */
type WellKnownDirectory = 'desktop' | 'documents' | 'downloads' | 'music' | 'pictures' | 'videos';

/**
 * Options for file picker
 */
interface OpenFilePickerOptions {
  multiple?: boolean;
  excludeAcceptAllOption?: boolean;
  types?: FilePickerAcceptType[];
  id?: string;
  startIn?: FileSystemHandle | WellKnownDirectory;
}

/**
 * File type for picker
 */
interface FilePickerAcceptType {
  description?: string;
  accept: Record<string, string | string[]>;
}

/**
 * Options for save file picker
 */
interface SaveFilePickerOptions {
  excludeAcceptAllOption?: boolean;
  types?: FilePickerAcceptType[];
  id?: string;
  startIn?: FileSystemHandle | WellKnownDirectory;
  suggestedName?: string;
}

/**
 * Window interface extensions for File System Access API
 */
interface Window {
  /**
   * Show directory picker
   */
  showDirectoryPicker(options?: DirectoryPickerOptions): Promise<FileSystemDirectoryHandle>;

  /**
   * Show open file picker
   */
  showOpenFilePicker(options?: OpenFilePickerOptions): Promise<FileSystemFileHandle[]>;

  /**
   * Show save file picker
   */
  showSaveFilePicker(options?: SaveFilePickerOptions): Promise<FileSystemFileHandle>;
}

/**
 * DataTransferItem extensions for File System Access API
 */
interface DataTransferItem {
  /**
   * Get file system handle from drag-and-drop
   */
  getAsFileSystemHandle(): Promise<FileSystemHandle | null>;

  /**
   * Legacy API for getting entry (read-only)
   */
  webkitGetAsEntry(): FileSystemEntry | null;
}

/**
 * Legacy File System Entry (read-only)
 */
interface FileSystemEntry {
  readonly isFile: boolean;
  readonly isDirectory: boolean;
  readonly name: string;
  readonly fullPath: string;
  readonly filesystem: FileSystem;

  getParent(successCallback?: FileSystemEntryCallback, errorCallback?: ErrorCallback): void;
}

/**
 * Legacy File System Entry callback
 */
interface FileSystemEntryCallback {
  (entry: FileSystemEntry): void;
}

/**
 * Legacy File System Directory Entry (read-only)
 */
interface FileSystemDirectoryEntry extends FileSystemEntry {
  readonly isDirectory: true;

  createReader(): FileSystemDirectoryReader;
  getFile(path?: string, options?: FileSystemFlags, successCallback?: FileSystemFileEntryCallback, errorCallback?: ErrorCallback): void;
  getDirectory(path?: string, options?: FileSystemFlags, successCallback?: FileSystemDirectoryEntryCallback, errorCallback?: ErrorCallback): void;
}

/**
 * Legacy File System File Entry (read-only)
 */
interface FileSystemFileEntry extends FileSystemEntry {
  readonly isFile: true;

  file(successCallback: FileCallback, errorCallback?: ErrorCallback): void;
}

/**
 * Legacy File System Directory Reader
 */
interface FileSystemDirectoryReader {
  readEntries(successCallback: FileSystemEntriesCallback, errorCallback?: ErrorCallback): void;
}

/**
 * Callbacks for legacy API
 */
interface FileSystemFileEntryCallback {
  (entry: FileSystemFileEntry): void;
}

interface FileSystemDirectoryEntryCallback {
  (entry: FileSystemDirectoryEntry): void;
}

interface FileSystemEntriesCallback {
  (entries: FileSystemEntry[]): void;
}

interface FileCallback {
  (file: File): void;
}

interface FileSystemFlags {
  create?: boolean;
  exclusive?: boolean;
}

interface FileSystem {
  readonly name: string;
  readonly root: FileSystemDirectoryEntry;
}
