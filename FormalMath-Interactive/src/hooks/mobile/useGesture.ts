import { useState, useCallback, useRef, useEffect } from 'react';

export interface GestureState {
  type: 'swipe' | 'pinch' | 'rotate' | 'tap' | 'doubleTap' | 'longPress' | 'pan' | null;
  direction: 'left' | 'right' | 'up' | 'down' | null;
  distance: number;
  velocity: number;
  scale: number;
  rotation: number;
  centerX: number;
  centerY: number;
  deltaX: number;
  deltaY: number;
}

export interface UseGestureOptions {
  onSwipe?: (gesture: GestureState) => void;
  onPinch?: (gesture: GestureState) => void;
  onRotate?: (gesture: GestureState) => void;
  onTap?: (gesture: GestureState) => void;
  onDoubleTap?: (gesture: GestureState) => void;
  onLongPress?: (gesture: GestureState) => void;
  onPan?: (gesture: GestureState) => void;
  onPanStart?: (gesture: GestureState) => void;
  onPanEnd?: (gesture: GestureState) => void;
  swipeThreshold?: number;
  longPressDelay?: number;
  doubleTapDelay?: number;
  preventDefaultTouch?: boolean;
}

/**
 * 高级手势检测 Hook
 * 支持：滑动、缩放、旋转、轻触、双击、长按、拖动
 */
export const useGesture = (options: UseGestureOptions = {}) => {
  const {
    onSwipe,
    onPinch,
    onRotate,
    onTap,
    onDoubleTap,
    onLongPress,
    onPan,
    onPanStart,
    onPanEnd,
    swipeThreshold = 50,
    longPressDelay = 500,
    doubleTapDelay = 300,
    preventDefaultTouch = true,
  } = options;

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

  const touchState = useRef({
    startTime: 0,
    startX: 0,
    startY: 0,
    lastX: 0,
    lastY: 0,
    startDistance: 0,
    startAngle: 0,
    touches: 0,
    isPinching: false,
    isPanning: false,
    lastTapTime: 0,
    longPressTimer: null as number | null,
    initialScale: 1,
    initialRotation: 0,
  });

  // 计算两点间距离
  const getDistance = useCallback((touches: TouchList) => {
    if (touches.length < 2) return 0;
    const dx = touches[0].clientX - touches[1].clientX;
    const dy = touches[0].clientY - touches[1].clientY;
    return Math.sqrt(dx * dx + dy * dy);
  }, []);

  // 计算两点间角度
  const getAngle = useCallback((touches: TouchList) => {
    if (touches.length < 2) return 0;
    const dx = touches[1].clientX - touches[0].clientX;
    const dy = touches[1].clientY - touches[0].clientY;
    return Math.atan2(dy, dx) * (180 / Math.PI);
  }, []);

  // 计算中心点
  const getCenter = useCallback((touches: TouchList) => {
    if (touches.length === 0) return { x: 0, y: 0 };
    if (touches.length === 1) return { x: touches[0].clientX, y: touches[0].clientY };
    return {
      x: (touches[0].clientX + touches[1].clientX) / 2,
      y: (touches[0].clientY + touches[1].clientY) / 2,
    };
  }, []);

  // 清除长按定时器
  const clearLongPressTimer = useCallback(() => {
    if (touchState.current.longPressTimer) {
      clearTimeout(touchState.current.longPressTimer);
      touchState.current.longPressTimer = null;
    }
  }, []);

  // 处理触摸开始
  const handleTouchStart = useCallback((e: React.TouchEvent) => {
    const { touches } = e;
    const now = Date.now();
    const center = getCenter(touches);

    touchState.current.touches = touches.length;
    touchState.current.startTime = now;
    touchState.current.startX = center.x;
    touchState.current.startY = center.y;
    touchState.current.lastX = center.x;
    touchState.current.lastY = center.y;

    if (touches.length === 2) {
      // 双指手势开始
      touchState.current.isPinching = true;
      touchState.current.startDistance = getDistance(touches);
      touchState.current.startAngle = getAngle(touches);
      touchState.current.initialScale = gesture.scale;
      touchState.current.initialRotation = gesture.rotation;
    } else if (touches.length === 1) {
      // 单指手势开始
      touchState.current.isPanning = true;
      touchState.current.isPinching = false;

      // 检测双击
      if (now - touchState.current.lastTapTime < doubleTapDelay) {
        clearLongPressTimer();
        const newGesture: GestureState = {
          type: 'doubleTap',
          direction: null,
          distance: 0,
          velocity: 0,
          scale: 1,
          rotation: 0,
          centerX: center.x,
          centerY: center.y,
          deltaX: 0,
          deltaY: 0,
        };
        setGesture(newGesture);
        onDoubleTap?.(newGesture);
        touchState.current.lastTapTime = 0;
        return;
      }

      touchState.current.lastTapTime = now;

      // 设置长按检测
      clearLongPressTimer();
      touchState.current.longPressTimer = window.setTimeout(() => {
        const newGesture: GestureState = {
          type: 'longPress',
          direction: null,
          distance: 0,
          velocity: 0,
          scale: 1,
          rotation: 0,
          centerX: center.x,
          centerY: center.y,
          deltaX: 0,
          deltaY: 0,
        };
        setGesture(newGesture);
        onLongPress?.(newGesture);
        touchState.current.isPanning = false;
      }, longPressDelay);

      const newGesture: GestureState = {
        type: 'pan',
        direction: null,
        distance: 0,
        velocity: 0,
        scale: gesture.scale,
        rotation: gesture.rotation,
        centerX: center.x,
        centerY: center.y,
        deltaX: 0,
        deltaY: 0,
      };
      onPanStart?.(newGesture);
    }

    if (preventDefaultTouch && touches.length > 1) {
      e.preventDefault();
    }
  }, [gesture.scale, gesture.rotation, getCenter, getDistance, getAngle, doubleTapDelay, longPressDelay, clearLongPressTimer, onDoubleTap, onLongPress, onPanStart, preventDefaultTouch]);

  // 处理触摸移动
  const handleTouchMove = useCallback((e: React.TouchEvent) => {
    const { touches } = e;
    const now = Date.now();
    const center = getCenter(touches);

    if (touches.length === 2 && touchState.current.isPinching) {
      // 双指缩放和旋转
      e.preventDefault();
      clearLongPressTimer();

      const currentDistance = getDistance(touches);
      const currentAngle = getAngle(touches);
      const scale = touchState.current.initialScale * (currentDistance / touchState.current.startDistance);
      const rotation = touchState.current.initialRotation + (currentAngle - touchState.current.startAngle);

      const newGesture: GestureState = {
        type: 'pinch',
        direction: null,
        distance: currentDistance - touchState.current.startDistance,
        velocity: 0,
        scale,
        rotation,
        centerX: center.x,
        centerY: center.y,
        deltaX: center.x - touchState.current.startX,
        deltaY: center.y - touchState.current.startY,
      };
      setGesture(newGesture);
      onPinch?.(newGesture);
      onRotate?.(newGesture);
    } else if (touches.length === 1 && touchState.current.isPanning) {
      // 单指拖动
      const deltaX = center.x - touchState.current.startX;
      const deltaY = center.y - touchState.current.startY;
      const distance = Math.sqrt(deltaX * deltaX + deltaY * deltaY);
      const duration = now - touchState.current.startTime;
      const velocity = duration > 0 ? distance / duration : 0;

      // 判断方向
      let direction: GestureState['direction'] = null;
      if (distance > 10) {
        if (Math.abs(deltaX) > Math.abs(deltaY)) {
          direction = deltaX > 0 ? 'right' : 'left';
        } else {
          direction = deltaY > 0 ? 'down' : 'up';
        }
      }

      // 如果移动距离超过阈值，取消长按
      if (distance > 10) {
        clearLongPressTimer();
      }

      const newGesture: GestureState = {
        type: 'pan',
        direction,
        distance,
        velocity,
        scale: gesture.scale,
        rotation: gesture.rotation,
        centerX: center.x,
        centerY: center.y,
        deltaX,
        deltaY,
      };
      setGesture(newGesture);
      onPan?.(newGesture);
    }

    touchState.current.lastX = center.x;
    touchState.current.lastY = center.y;
  }, [gesture.scale, gesture.rotation, getCenter, getDistance, getAngle, clearLongPressTimer, onPinch, onRotate, onPan, preventDefaultTouch]);

  // 处理触摸结束
  const handleTouchEnd = useCallback((e: React.TouchEvent) => {
    const now = Date.now();
    const duration = now - touchState.current.startTime;
    const center = { x: touchState.current.lastX, y: touchState.current.lastY };

    clearLongPressTimer();

    // 检测滑动
    if (touchState.current.isPanning && e.changedTouches.length === 1) {
      const deltaX = center.x - touchState.current.startX;
      const deltaY = center.y - touchState.current.startY;
      const distance = Math.sqrt(deltaX * deltaX + deltaY * deltaY);
      const velocity = duration > 0 ? distance / duration : 0;

      // 判断是否为滑动
      if (distance > swipeThreshold && velocity > 0.5) {
        let direction: GestureState['direction'] = null;
        if (Math.abs(deltaX) > Math.abs(deltaY)) {
          direction = deltaX > 0 ? 'right' : 'left';
        } else {
          direction = deltaY > 0 ? 'down' : 'up';
        }

        const newGesture: GestureState = {
          type: 'swipe',
          direction,
          distance,
          velocity,
          scale: gesture.scale,
          rotation: gesture.rotation,
          centerX: center.x,
          centerY: center.y,
          deltaX,
          deltaY,
        };
        setGesture(newGesture);
        onSwipe?.(newGesture);
      } else if (duration < 300 && distance < 10) {
        // 轻触
        const newGesture: GestureState = {
          type: 'tap',
          direction: null,
          distance: 0,
          velocity: 0,
          scale: 1,
          rotation: 0,
          centerX: center.x,
          centerY: center.y,
          deltaX: 0,
          deltaY: 0,
        };
        setGesture(newGesture);
        onTap?.(newGesture);
      }

      const endGesture: GestureState = {
        type: 'pan',
        direction: null,
        distance,
        velocity,
        scale: gesture.scale,
        rotation: gesture.rotation,
        centerX: center.x,
        centerY: center.y,
        deltaX,
        deltaY,
      };
      onPanEnd?.(endGesture);
    }

    touchState.current.isPanning = false;
    touchState.current.isPinching = false;
    touchState.current.touches = e.touches.length;
  }, [gesture.scale, gesture.rotation, swipeThreshold, clearLongPressTimer, onSwipe, onTap, onPanEnd]);

  // 清理
  useEffect(() => {
    return () => {
      clearLongPressTimer();
    };
  }, [clearLongPressTimer]);

  const bind = useCallback(() => ({
    onTouchStart: handleTouchStart,
    onTouchMove: handleTouchMove,
    onTouchEnd: handleTouchEnd,
    onTouchCancel: handleTouchEnd,
  }), [handleTouchStart, handleTouchMove, handleTouchEnd]);

  return {
    gesture,
    bind: bind(),
  };
};

/**
 * 简化的滑动手势 Hook
 */
export const useSwipe = (onSwipe: (direction: 'left' | 'right' | 'up' | 'down') => void, threshold = 50) => {
  const { bind } = useGesture({
    onSwipe: (gesture) => {
      if (gesture.direction) {
        onSwipe(gesture.direction);
      }
    },
    swipeThreshold: threshold,
  });

  return bind;
};

/**
 * 简化的缩放手势 Hook
 */
export const usePinch = (onPinch: (scale: number, delta: number) => void) => {
  const { bind } = useGesture({
    onPinch: (gesture) => {
      onPinch(gesture.scale, gesture.distance);
    },
  });

  return bind;
};

/**
 * 简化的双击手势 Hook
 */
export const useDoubleTap = (onDoubleTap: () => void) => {
  const { bind } = useGesture({
    onDoubleTap: () => {
      onDoubleTap();
    },
  });

  return bind;
};

export default useGesture;
