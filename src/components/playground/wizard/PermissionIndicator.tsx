import React from 'react';

export interface PermissionIndicatorProps {
  hasRead: boolean;
  hasWrite: boolean;
  onRequestPermission?: () => void;
}

export const PermissionIndicator: React.FC<PermissionIndicatorProps> = ({
  hasRead,
  hasWrite,
  onRequestPermission
}) => {
  const allPermissionsGranted = hasRead && hasWrite;

  return (
    <div className="permission-indicator">
      <div className="permission-status">
        <span className={`status-badge ${hasRead ? 'granted' : 'denied'}`}>
          {hasRead ? '✓' : '✗'} Read
        </span>
        <span className={`status-badge ${hasWrite ? 'granted' : 'denied'}`}>
          {hasWrite ? '✓' : '✗'} Write
        </span>
      </div>

      {!allPermissionsGranted && onRequestPermission && (
        <button
          className="request-permission-button"
          onClick={onRequestPermission}
        >
          Request Permissions
        </button>
      )}

      {!hasWrite && (
        <p className="permission-warning">
          Write permission is required to save transpiled files.
        </p>
      )}

      <style>{`
        .permission-indicator {
          margin-top: 1rem;
          padding: 1rem;
          background-color: #f9f9f9;
          border-radius: 4px;
          border: 1px solid #ddd;
        }

        .permission-status {
          display: flex;
          gap: 0.75rem;
          margin-bottom: 0.75rem;
        }

        .status-badge {
          padding: 0.25rem 0.75rem;
          border-radius: 4px;
          font-size: 0.875rem;
          font-weight: 500;
        }

        .status-badge.granted {
          background-color: #d4edda;
          color: #155724;
          border: 1px solid #c3e6cb;
        }

        .status-badge.denied {
          background-color: #f8d7da;
          color: #721c24;
          border: 1px solid #f5c6cb;
        }

        .request-permission-button {
          padding: 0.5rem 1rem;
          background-color: #4A90E2;
          color: white;
          border: none;
          border-radius: 4px;
          cursor: pointer;
          font-size: 0.875rem;
          font-weight: 500;
          transition: background-color 0.15s;
        }

        .request-permission-button:hover {
          background-color: #357abd;
        }

        .permission-warning {
          margin-top: 0.75rem;
          margin-bottom: 0;
          font-size: 0.875rem;
          color: #856404;
          background-color: #fff3cd;
          padding: 0.5rem;
          border-radius: 4px;
          border: 1px solid #ffeaa7;
        }
      `}</style>
    </div>
  );
};
