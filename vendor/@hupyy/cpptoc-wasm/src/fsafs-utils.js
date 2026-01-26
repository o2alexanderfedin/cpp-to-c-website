/**
 * Utility functions for mounting and managing FSAFS
 */

const FSAFSUtils = {
  /**
   * Request directory access from user and mount it
   * Must be called from a user gesture (click handler, etc.)
   *
   * @param {string} mountPoint - Virtual path to mount at (e.g., '/project')
   * @param {object} options - Options for showDirectoryPicker
   * @returns {Promise<FileSystemDirectoryHandle>} The mounted handle
   */
  async mountDirectory(mountPoint, options = {}) {
    // Request permission
    const handle = await window.showDirectoryPicker({
      mode: 'readwrite',
      ...options
    });

    // Explicitly verify and request write permission
    const permissionStatus = await handle.requestPermission({ mode: 'readwrite' });
    if (permissionStatus !== 'granted') {
      throw new Error(`Write permission not granted: ${permissionStatus}. Please allow read and write access.`);
    }

    // Clean up existing mount point if needed
    try {
      const existingNode = FS.lookupPath(mountPoint);
      if (existingNode.node && existingNode.node.mounted) {
        console.log(`Unmounting existing filesystem at ${mountPoint}`);
        FS.unmount(mountPoint);
      }
      // Remove the directory to start fresh
      FS.rmdir(mountPoint);
    } catch (e) {
      // Mount point doesn't exist yet - this is fine
    }

    // Create mount point directory (required before mount)
    FS.mkdir(mountPoint);

    // Mount the filesystem
    FS.mount(FSAFS, { handle: handle }, mountPoint);

    return handle;
  },

  /**
   * Mount multiple directories for a typical compiler workflow
   *
   * @param {object} config - Configuration with srcDir, includeDir, outputDir paths
   * @returns {Promise<object>} Object with mounted handles
   */
  async mountCompilerDirs(config = {}) {
    const {
      srcMount = '/src',
      includeMount = '/include',
      outputMount = '/out'
    } = config;

    const result = {};

    // Source directory
    console.log('Select SOURCE directory...');
    result.srcHandle = await this.mountDirectory(srcMount, {
      id: 'source',
      startIn: 'documents'
    });

    // Include directory
    console.log('Select INCLUDE directory...');
    result.includeHandle = await this.mountDirectory(includeMount, {
      id: 'include',
      startIn: 'documents'
    });

    // Output directory
    console.log('Select OUTPUT directory...');
    result.outputHandle = await this.mountDirectory(outputMount, {
      id: 'output',
      startIn: 'documents'
    });

    return result;
  },

  /**
   * Mount a single project directory with conventional structure
   * Expects: project/src, project/include, project/build
   *
   * @param {string} mountPoint - Where to mount (default '/project')
   * @returns {Promise<FileSystemDirectoryHandle>}
   */
  async mountProject(mountPoint = '/project') {
    console.log('Select PROJECT directory...');
    return await this.mountDirectory(mountPoint, {
      id: 'project',
      startIn: 'documents'
    });
  },

  /**
   * Check if File System Access API is available
   */
  isSupported() {
    return 'showDirectoryPicker' in window;
  },

  /**
   * Unmount a previously mounted directory
   */
  unmount(mountPoint) {
    try {
      FS.unmount(mountPoint);
    } catch (e) {
      console.warn('Unmount failed:', e);
    }
  }
};

// Export for use in module
if (typeof module !== 'undefined') {
  module.exports = FSAFSUtils;
}
