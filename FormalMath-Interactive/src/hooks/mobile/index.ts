// 移动端专用 hooks 导出
export { 
  useMobileDetect, 
  usePWAState, 
  useTouchGesture,
  useShakeDetection 
} from './useMobileDetect';

export { 
  usePushNotification, 
  useStudyReminder 
} from './usePushNotification';

export { 
  useDarkMode, 
  useAutoDarkMode 
} from './useDarkMode';

// 类型导出
export type { MobileDetectState, PWAState } from './useMobileDetect';
