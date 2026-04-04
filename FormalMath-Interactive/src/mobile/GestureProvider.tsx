import React, { createContext, useContext, useCallback, useRef, useState } from 'react';
import { useGesture, type GestureState, type UseGestureOptions } from '@hooks/mobile/useGesture';

interface GestureContextType {
  gesture: GestureState;
  isGesturing: boolean;
  registerGesture: (id: string, options: UseGestureOptions) => void;
  unregisterGesture: (id: string) => void;
}

const GestureContext = createContext<GestureContextType | null>(null);

export interface GestureProviderProps {
  children: React.ReactNode;
}

/**
 * 手势提供者组件
 * 提供全局手势状态管理和协调
 */
export const GestureProvider: React.FC<GestureProviderProps> = ({ children }) => {
  const [gesture, setGesture] = useState<GestureState>({
    type: null,
    direction: null,
    distance: 0,
    velocity: 0,
    scale: 1,
    rotation: 0,
    centerX: 0,
    centerY: 0,
    deltaX: 0,
    deltaY: 0,
  });
  const [isGesturing, setIsGesturing] = useState(false);
  const gestureRegistry = useRef<Map<string, UseGestureOptions>>(new Map());

  const registerGesture = useCallback((id: string, options: UseGestureOptions) => {
    gestureRegistry.current.set(id, options);
  }, []);

  const unregisterGesture = useCallback((id: string) => {
    gestureRegistry.current.delete(id);
  }, []);

  const handleGestureStart = useCallback(() => {
    setIsGesturing(true);
  }, []);

  const handleGestureEnd = useCallback(() => {
    setIsGesturing(false);
  }, []);

  const { bind } = useGesture({
    onSwipe: (g) => {
      setGesture(g);
      gestureRegistry.current.forEach((options) => {
        options.onSwipe?.(g);
      });
    },
    onPinch: (g) => {
      setGesture(g);
      gestureRegistry.current.forEach((options) => {
        options.onPinch?.(g);
      });
    },
    onTap: (g) => {
      setGesture(g);
      gestureRegistry.current.forEach((options) => {
        options.onTap?.(g);
      });
    },
    onDoubleTap: (g) => {
      setGesture(g);
      gestureRegistry.current.forEach((options) => {
        options.onDoubleTap?.(g);
      });
    },
    onLongPress: (g) => {
      setGesture(g);
      gestureRegistry.current.forEach((options) => {
        options.onLongPress?.(g);
      });
    },
    onPanStart: handleGestureStart,
    onPanEnd: handleGestureEnd,
  });

  return (
    <GestureContext.Provider value={{ gesture, isGesturing, registerGesture, unregisterGesture }}>
      <div {...bind} className="touch-pan-y">
        {children}
      </div>
    </GestureContext.Provider>
  );
};

/**
 * 使用手势上下文的 Hook
 */
export const useGestureContext = () => {
  const context = useContext(GestureContext);
  if (!context) {
    throw new Error('useGestureContext must be used within a GestureProvider');
  }
  return context;
};

export default GestureProvider;
