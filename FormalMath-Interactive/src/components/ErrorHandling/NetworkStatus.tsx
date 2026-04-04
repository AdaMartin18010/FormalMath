import React, { useState, useEffect } from 'react';
import { Wifi, WifiOff, RefreshCw, AlertCircle } from 'lucide-react';
import { cn } from '@utils/classNames';

/**
 * 网络状态指示器
 * 实时显示网络连接状态
 */
export const NetworkStatus: React.FC = () => {
  const [isOnline, setIsOnline] = useState(navigator.onLine);
  const [showToast, setShowToast] = useState(false);
  const [lastOffline, setLastOffline] = useState<number | null>(null);

  useEffect(() => {
    const handleOnline = () => {
      setIsOnline(true);
      setShowToast(true);
      setTimeout(() => setShowToast(false), 3000);
    };

    const handleOffline = () => {
      setIsOnline(false);
      setLastOffline(Date.now());
      setShowToast(true);
    };

    window.addEventListener('online', handleOnline);
    window.addEventListener('offline', handleOffline);

    return () => {
      window.removeEventListener('online', handleOnline);
      window.removeEventListener('offline', handleOffline);
    };
  }, []);

  if (!showToast) return null;

  return (
    <div className="fixed top-20 left-1/2 -translate-x-1/2 z-50">
      <div
        className={cn(
          'flex items-center gap-3 px-6 py-3 rounded-full shadow-lg transition-all',
          isOnline 
            ? 'bg-green-500 text-white' 
            : 'bg-red-500 text-white'
        )}
      >
        {isOnline ? (
          <>
            <Wifi className="w-5 h-5" />
            <span className="font-medium">网络已恢复</span>
          </>
        ) : (
          <>
            <WifiOff className="w-5 h-5" />
            <span className="font-medium">网络已断开</span>
            <span className="text-sm opacity-80">部分功能可能不可用</span>
          </>
        )}
      </div>
    </div>
  );
};

/**
 * 离线提示组件
 */
interface OfflinePromptProps {
  onRetry?: () => void;
  children: React.ReactNode;
}

export const OfflinePrompt: React.FC<OfflinePromptProps> = ({ onRetry, children }) => {
  const [isOnline, setIsOnline] = useState(navigator.onLine);

  useEffect(() => {
    const updateOnlineStatus = () => setIsOnline(navigator.onLine);
    window.addEventListener('online', updateOnlineStatus);
    window.addEventListener('offline', updateOnlineStatus);
    return () => {
      window.removeEventListener('online', updateOnlineStatus);
      window.removeEventListener('offline', updateOnlineStatus);
    };
  }, []);

  if (isOnline) return <>{children}</>;

  return (
    <div className="relative">
      {children}
      <div className="absolute inset-0 bg-white/80 dark:bg-slate-900/80 backdrop-blur-sm flex items-center justify-center rounded-lg">
        <div className="text-center p-6">
          <WifiOff className="w-12 h-12 text-gray-400 mx-auto mb-4" />
          <h3 className="text-lg font-semibold text-gray-900 dark:text-white mb-2">
            当前处于离线状态
          </h3>
          <p className="text-gray-500 dark:text-gray-400 mb-4">
            请检查网络连接后重试
          </p>
          {onRetry && (
            <button
              onClick={onRetry}
              className="inline-flex items-center gap-2 px-4 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors"
            >
              <RefreshCw className="w-4 h-4" />
              重试
            </button>
          )}
        </div>
      </div>
    </div>
  );
};

/**
 * 请求重试按钮
 */
interface RetryButtonProps {
  onRetry: () => void;
  error?: Error | null;
  className?: string;
}

export const RetryButton: React.FC<RetryButtonProps> = ({
  onRetry,
  error,
  className,
}) => {
  const [isRetrying, setIsRetrying] = useState(false);

  const handleRetry = async () => {
    setIsRetrying(true);
    try {
      await onRetry();
    } finally {
      setIsRetrying(false);
    }
  };

  const isNetworkError = error?.message.includes('network') || 
                        error?.message.includes('fetch') ||
                        error?.message.includes('timeout');

  return (
    <div className={cn('text-center py-8', className)}>
      <div className="w-16 h-16 bg-red-100 dark:bg-red-900/30 rounded-full flex items-center justify-center mx-auto mb-4">
        <AlertCircle className="w-8 h-8 text-red-600 dark:text-red-400" />
      </div>
      <h3 className="text-lg font-semibold text-gray-900 dark:text-white mb-2">
        {isNetworkError ? '加载失败' : '出现错误'}
      </h3>
      <p className="text-gray-500 dark:text-gray-400 mb-4 max-w-sm mx-auto">
        {isNetworkError 
          ? '网络连接不稳定，请检查网络后重试' 
          : error?.message || '发生了意外错误'}
      </p>
      <button
        onClick={handleRetry}
        disabled={isRetrying}
        className="inline-flex items-center gap-2 px-6 py-2.5 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors disabled:opacity-50"
      >
        <RefreshCw className={cn('w-4 h-4', isRetrying && 'animate-spin')} />
        {isRetrying ? '重试中...' : '重新加载'}
      </button>
    </div>
  );
};

export default NetworkStatus;
