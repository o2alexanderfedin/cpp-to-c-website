/**
 * PlaygroundWrapper - Client-side wrapper for PlaygroundController
 *
 * This wrapper is necessary because Astro's client:only components receive
 * JSON-serialized props, which strips methods from class instances.
 *
 * Solution: Create service instances on the client side instead of passing them as props.
 */

import React, { useMemo } from 'react';
import { PlaygroundController } from './PlaygroundController';
import { createPlaygroundServices } from '../../lib/playground/setup';

/**
 * Client-side wrapper that creates services and renders PlaygroundController
 *
 * This component should be used with client:only="react" in Astro pages.
 */
const PlaygroundWrapper: React.FC = () => {
  // Create services once on the client side
  const { transpiler, fileSystem } = useMemo(() => {
    return createPlaygroundServices();
  }, []);

  return <PlaygroundController transpiler={transpiler} fileSystem={fileSystem} />;
};

export default PlaygroundWrapper;
