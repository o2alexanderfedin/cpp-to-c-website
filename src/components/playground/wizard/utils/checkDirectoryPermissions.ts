/**
 * Permission status for a directory
 */
export interface PermissionStatus {
  read: boolean;
  write: boolean;
}

/**
 * Check if we have read/write permissions for a directory
 * @param dirHandle - FileSystemDirectoryHandle to check
 * @returns Object with read and write permission status
 */
export async function checkDirectoryPermissions(
  dirHandle: FileSystemDirectoryHandle
): Promise<PermissionStatus> {
  try {
    // Check read permission
    const readPermission = await dirHandle.queryPermission({ mode: 'read' });

    // Check write permission
    const writePermission = await dirHandle.queryPermission({ mode: 'readwrite' });

    return {
      read: readPermission === 'granted',
      write: writePermission === 'granted'
    };
  } catch (error) {
    console.error('Permission check failed:', error);
    return {
      read: false,
      write: false
    };
  }
}

/**
 * Request write permission for a directory
 * @param dirHandle - FileSystemDirectoryHandle to request permission for
 * @returns true if permission granted, false otherwise
 */
export async function requestWritePermission(
  dirHandle: FileSystemDirectoryHandle
): Promise<boolean> {
  try {
    const permission = await dirHandle.requestPermission({ mode: 'readwrite' });
    return permission === 'granted';
  } catch (error) {
    console.error('Permission request failed:', error);
    return false;
  }
}
