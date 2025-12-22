import { describe, it, expect, vi } from 'vitest';
import { render, screen, fireEvent } from '@testing-library/react';
import { PermissionIndicator } from './PermissionIndicator';

describe('PermissionIndicator', () => {
  it('shows granted status for both permissions', () => {
    render(<PermissionIndicator hasRead={true} hasWrite={true} />);

    expect(screen.getByText(/✓ Read/)).toBeInTheDocument();
    expect(screen.getByText(/✓ Write/)).toBeInTheDocument();
  });

  it('shows denied status for missing permissions', () => {
    render(<PermissionIndicator hasRead={false} hasWrite={false} />);

    expect(screen.getByText(/✗ Read/)).toBeInTheDocument();
    expect(screen.getByText(/✗ Write/)).toBeInTheDocument();
  });

  it('shows mixed permission status', () => {
    render(<PermissionIndicator hasRead={true} hasWrite={false} />);

    expect(screen.getByText(/✓ Read/)).toBeInTheDocument();
    expect(screen.getByText(/✗ Write/)).toBeInTheDocument();
  });

  it('shows request button when permissions not granted', () => {
    const handleRequest = vi.fn();
    render(
      <PermissionIndicator
        hasRead={true}
        hasWrite={false}
        onRequestPermission={handleRequest}
      />
    );

    const button = screen.getByText('Request Permissions');
    expect(button).toBeInTheDocument();

    fireEvent.click(button);
    expect(handleRequest).toHaveBeenCalledTimes(1);
  });

  it('shows warning when write permission missing', () => {
    render(<PermissionIndicator hasRead={true} hasWrite={false} />);

    expect(screen.getByText(/Write permission is required/)).toBeInTheDocument();
  });

  it('does not show request button when all permissions granted', () => {
    render(<PermissionIndicator hasRead={true} hasWrite={true} />);

    expect(screen.queryByText('Request Permissions')).not.toBeInTheDocument();
  });

  it('does not show request button when callback not provided', () => {
    render(<PermissionIndicator hasRead={false} hasWrite={false} />);

    expect(screen.queryByText('Request Permissions')).not.toBeInTheDocument();
  });

  it('does not show warning when write permission granted', () => {
    render(<PermissionIndicator hasRead={true} hasWrite={true} />);

    expect(screen.queryByText(/Write permission is required/)).not.toBeInTheDocument();
  });

  it('shows warning when only read permission denied', () => {
    render(<PermissionIndicator hasRead={false} hasWrite={true} />);

    // Should not show write permission warning if write is granted
    expect(screen.queryByText(/Write permission is required/)).not.toBeInTheDocument();
  });
});
