import React, { useState, useEffect, useCallback } from 'react';

interface MobileDetectState {
  isMobile: boolean;
  isTablet: boolean;
  isDesktop: boolean;
  isPortrait: boolean;
  isLandscape: boolean;
  screenWidth: number;
  screenHeight: number;
  touchSupported: boolean;
  devicePixelRatio: number;
}

interface PWAState {
  isStandalone: boolean;
  canInstall: boolean;
  isOnline: boolean;
  connectionType: string;
  saveData: boolean;
}

// 断点定义
const BREAKPOINTS = {
  mobile: 640,
  tablet: 1024,
  desktop: 1280,
};

/**
 * 检测移动设备的 Hook
 */
export const useMobileDetect = (): MobileDetectState => {
  const [state, setState] = useState<MobileDetectState>({
    isMobile: false,
    isTablet: false,
    isDesktop: true,
    isPortrait: true,
    isLandscape: false,
    screenWidth: window.innerWidth,
    screenHeight: window.innerHeight,
    touchSupported: 'ontouchstart' in window || navigator.maxTouchPoints > 0,
    devicePixelRatio: window.devicePixelRatio || 1,
  });

  useEffect(() => {
    const updateState = () => {
      const width = window.innerWidth;
      const height = window.innerHeight;
      
      setState({
        isMobile: width < BREAKPOINTS.mobile,
        isTablet: width >= BREAKPOINTS.mobile && width < BREAKPOINTS.tablet,
        isDesktop: width >= BREAKPOINTS.tablet,
        isPortrait: height > width,
        isLandscape: width > height,
        screenWidth: width,
        screenHeight: height,
        touchSupported: 'ontouchstart' in window || navigator.maxTouchPoints > 0,
        devicePixelRatio: window.devicePixelRatio || 1,
      });
    };

    // 初始检测
    updateState();

    // 监听窗口变化
    window.addEventListener('resize', updateState);
    window.addEventListener('orientationchange', updateState);

    return () => {
      window.removeEventListener('resize', updateState);
      window.removeEventListener('orientationchange', updateState);
    };
  }, []);

  return state;
};

/**
 * PWA 状态检测 Hook
 */
export const usePWAState = (): PWAState & { promptInstall: () => Promise<void> } => {
  const [state, setState] = useState<PWAState>({
    isStandalone: window.matchMedia('(display-mode: standalone)').matches || 
                  (window.navigator as any).standalone === true,
    canInstall: false,
    isOnline: navigator.onLine,
    connectionType: 'unknown',
    saveData: false,
  });

  const [deferredPrompt, setDeferredPrompt] = useState<any>(null);

  useEffect(() => {
    // 检测网络状态
    const handleOnline = () => setState(prev => ({ ...prev, isOnline: true }));
    const handleOffline = () => setState(prev => ({ ...prev, isOnline: false }));

    window.addEventListener('online', handleOnline);
    window.addEventListener('offline', handleOffline);

    // 检测连接信息
    const connection = (navigator as any).connection;
    if (connection) {
      const updateConnectionInfo = () => {
        setState(prev => ({
          ...prev,
          connectionType: connection.effectiveType || 'unknown',
          saveData: connection.saveData || false,
        }));
      };
      updateConnectionInfo();
      connection.addEventListener('change', updateConnectionInfo);
    }

    // 监听安装提示
    const handleBeforeInstallPrompt = (e: Event) => {
      e.preventDefault();
      setDeferredPrompt(e);
      setState(prev => ({ ...prev, canInstall: true }));
    };

    // 监听应用安装完成
    const handleAppInstalled = () => {
      setDeferredPrompt(null);
      setState(prev => ({ ...prev, canInstall: false, isStandalone: true }));
    };

    window.addEventListener('beforeinstallprompt', handleBeforeInstallPrompt);
    window.addEventListener('appinstalled', handleAppInstalled);

    return () => {
      window.removeEventListener('online', handleOnline);
      window.removeEventListener('offline', handleOffline);
      window.removeEventListener('beforeinstallprompt', handleBeforeInstallPrompt);
      window.removeEventListener('appinstalled', handleAppInstalled);
      if (connection) {
        connection.removeEventListener('change', updateConnectionInfo);
      }
    };
  }, []);

  // 触发安装提示
  const promptInstall = useCallback(async () => {
    if (!deferredPrompt) return;
    
    deferredPrompt.prompt();
    const { outcome } = await deferredPrompt.userChoice;
    
    if (outcome === 'accepted') {
      console.log('用户接受了安装提示');
    } else {
      console.log('用户拒绝了安装提示');
    }
    
    setDeferredPrompt(null);
    setState(prev => ({ ...prev, canInstall: false }));
  }, [deferredPrompt]);

  return { ...state, promptInstall };
};

/**
 * 触摸手势检测 Hook
 */
export const useTouchGesture = () => {
  const [gesture, setGesture] = useState<{
    type: 'swipe' | 'pinch' | 'tap' | 'longPress' | null;
    direction: 'left' | 'right' | 'up' | 'down' | null;
    distance: number;
    velocity: number;
  }>({
    type: null,
    direction: null,
    distance: 0,
    velocity: 0,
  });

  const touchStart = useCallback((e: React.TouchEvent) => {
    const touch = e.touches[0];
    return {
      startX: touch.clientX,
      startY: touch.clientY,
      startTime: Date.now(),
    };
  }, []);

  const touchEnd = useCallback((
    e: React.TouchEvent,
    startData: { startX: number; startY: number; startTime: number }
  ) => {
    const touch = e.changedTouches[0];
    const endX = touch.clientX;
    const endY = touch.clientY;
    const endTime = Date.now();

    const deltaX = endX - startData.startX;
    const deltaY = endY - startData.startY;
    const deltaTime = endTime - startData.startTime;
    const distance = Math.sqrt(deltaX * deltaX + deltaY * deltaY);
    const velocity = distance / deltaTime;

    // 判断手势类型
    let type: typeof gesture.type = null;
    let direction: typeof gesture.direction = null;

    // 长按检测（超过500ms）
    if (deltaTime > 500 && distance < 10) {
      type = 'longPress';
    }
    // 滑动检测（距离超过50px）
    else if (distance > 50) {
      type = 'swipe';
      if (Math.abs(deltaX) > Math.abs(deltaY)) {
        direction = deltaX > 0 ? 'right' : 'left';
      } else {
        direction = deltaY > 0 ? 'down' : 'up';
      }
    }
    // 轻触检测
    else if (distance < 10 && deltaTime < 300) {
      type = 'tap';
    }

    const newGesture = { type, direction, distance, velocity };
    setGesture(newGesture);
    return newGesture;
  }, []);

  return { gesture, touchStart, touchEnd };
};

/**
 * 摇一摇检测 Hook
 */
export const useShakeDetection = (options: {
  threshold?: number;
  timeout?: number;
  onShake?: () => void;
}) => {
  const { threshold = 15, timeout = 1000, onShake } = options;
  const [isShaking, setIsShaking] = useState(false);
  const lastShake = React.useRef(0);
  const lastX = React.useRef(0);
  const lastY = React.useRef(0);
  const lastZ = React.useRef(0);

  useEffect(() => {
    if (!window.DeviceMotionEvent) return;

    const handleMotion = (e: DeviceMotionEvent) => {
      const current = Date.now();
      if (current - lastShake.current < timeout) return;

      const { x = 0, y = 0, z = 0 } = e.accelerationIncludingGravity || {};
      const deltaX = Math.abs(x - lastX.current);
      const deltaY = Math.abs(y - lastY.current);
      const deltaZ = Math.abs(z - lastZ.current);

      if (deltaX > threshold || deltaY > threshold || deltaZ > threshold) {
        lastShake.current = current;
        setIsShaking(true);
        onShake?.();
        setTimeout(() => setIsShaking(false), 500);
      }

      lastX.current = x;
      lastY.current = y;
      lastZ.current = z;
    };

    window.addEventListener('devicemotion', handleMotion);
    return () => window.removeEventListener('devicemotion', handleMotion);
  }, [threshold, timeout, onShake]);

  return { isShaking };
};

import React from 'react';

export default useMobileDetect;
