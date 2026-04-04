import React, { useState, useEffect } from 'react';
import { WifiOff, Wifi, RefreshCw, CloudOff, Cloud } from 'lucide-react';
import { cn } from '@utils/classNames';
import { useNetworkStatus } from '@hooks/useOffline';

export interface OfflineIndicatorProps {
  className?: string;
  showWhenOnline?: boolean;
}

/**
 * 离线状态指示器
 * 显示网络状态，支持重试操作
 */
export const OfflineIndicator: React.FC<OfflineIndicatorProps> = ({
  className,
  showWhenOnline = false,
}) => {
  const { isOnline, connectionType, effectiveType, isSlowConnection } = useNetworkStatus();
  const [isVisible, setIsVisible] = useState(false);
  const [isRetrying, setIsRetrying] = useState(false);

  // 当网络状态变化时显示指示器
  useEffect(() => {
    if (!isOnline || (isOnline && showWhenOnline)) {
      setIsVisible(true);
      const timer = setTimeout(() => {
        if (isOnline) {
          setIsVisible(false);
        }
      }, 3000);
      return () => clearTimeout(timer);
    }
  }, [isOnline, showWhenOnline]);

  // 处理重试
  const handleRetry = async () => {
    setIsRetrying(true);
    // 模拟网络检查
    await new Promise(resolve => setTimeout(resolve, 1000));
    window.location.reload();
  };

  if (!isVisible) return null;

  return (
    <div
      className={cn(
        'fixed top-0 left-0 right-0 z-50 transition-all duration-300',
        isOnline ? 'bg-green-500' : 'bg-amber-500',
        className
      )}
      style={{
        paddingTop: 'env(safe-area-inset-top, 0px)',
      }}
    >
      <div className="flex items-center justify-between px-4 py-2">
        <div className="flex items-center gap-2 text-white">
          {isOnline ? (
            <>
              <Wifi className="w-4 h-4" />
              <span className="text-sm font-medium">
                已连接到网络
                {effectiveType !== 'unknown' && ` (${effectiveType})`}
              </span>
            </>
          ) : (
            <>
              <WifiOff className="w-4 h-4" />
              <span className="text-sm font-medium">无网络连接</span>
            </>
          )}
        </div>

        {!isOnline && (
          <button
            onClick={handleRetry}
            disabled={isRetrying}
            className="flex items-center gap-1 px-3 py-1 bg-white/20 hover:bg-white/30 rounded-lg text-white text-xs font-medium transition-colors disabled:opacity-50"
          >
            <RefreshCw className={cn('w-3 h-3', isRetrying && 'animate-spin')} />
            {isRetrying ? '重试中...' : '重试'}
          </button>
        )}
      </div>
    </div>
  );
};

/**
 * 离线内容卡片
 * 显示离线可用内容的状态
 */
interface OfflineContentCardProps {
  title: string;
  description?: string;
  isCached: boolean;
  lastUpdated?: string;
  onSync?: () => void;
  className?: string;
}

export const OfflineContentCard: React.FC<OfflineContentCardProps> = ({
  title,
  description,
  isCached,
  lastUpdated,
  onSync,
  className,
}) => {
  return (
    <div className={cn(
      'p-4 rounded-xl border transition-colors',
      isCached 
        ? 'bg-blue-50 dark:bg-blue-900/20 border-blue-200 dark:border-blue-800' 
        : 'bg-gray-50 dark:bg-slate-800 border-gray-200 dark:border-slate-700',
      className
    )}>
      <div className="flex items-start gap-3">
        <div className={cn(
          'p-2 rounded-lg',
          isCached 
            ? 'bg-blue-100 dark:bg-blue-900/50 text-blue-600 dark:text-blue-400' 
            : 'bg-gray-200 dark:bg-slate-700 text-gray-500'
        )}>
          {isCached ? <Cloud className="w-5 h-5" /> : <CloudOff className="w-5 h-5" />}
        </div>
        
        <div className="flex-1 min-w-0">
          <h4 className="font-medium text-gray-900 dark:text-white truncate">{title}</h4>
          {description && (
            <p className="text-sm text-gray-500 dark:text-gray-400 mt-0.5">{description}</p>
          )}
          {isCached && lastUpdated && (
            <p className="text-xs text-gray-400 dark:text-gray-500 mt-1">
              上次更新: {lastUpdated}
            </p>
          )}
        </div>

        {onSync && (
          <button
            onClick={onSync}
            className="p-2 text-gray-400 hover:text-blue-500 rounded-lg hover:bg-white dark:hover:bg-slate-700 transition-colors"
          >
            <RefreshCw className="w-4 h-4" />
          </button>
        )}
      </div>
    </div>
  );
};

/**
 * 离线模式提示
 * 当用户处于离线模式时显示
 */
interface OfflineModeBannerProps {
  cachedItemCount?: number;
  className?: string;
}

export const OfflineModeBanner: React.FC<OfflineModeBannerProps> = ({
  cachedItemCount,
  className,
}) => {
  const { isOnline } = useNetworkStatus();
  const [isDismissed, setIsDismissed] = useState(false);

  if (isOnline || isDismissed) return null;

  return (
    <div className={cn(
      'bg-amber-50 dark:bg-amber-900/20 border border-amber-200 dark:border-amber-800 rounded-xl p-4',
      className
    )}>
      <div className="flex items-start gap-3">
        <div className="p-2 bg-amber-100 dark:bg-amber-900/50 rounded-lg">
          <WifiOff className="w-5 h-5 text-amber-600 dark:text-amber-400" />
        </div>
        
        <div className="flex-1">
          <h4 className="font-medium text-amber-900 dark:text-amber-100">
            离线模式
          </h4>
          <p className="text-sm text-amber-700 dark:text-amber-300 mt-0.5">
            您当前处于离线状态。
            {cachedItemCount !== undefined && (
              <span> 有 {cachedItemCount} 个内容可在离线时访问。</span>
            )}
          </p>
        </div>

        <button
          onClick={() => setIsDismissed(true)}
          className="text-amber-400 hover:text-amber-600 dark:hover:text-amber-300"
        >
          ×
        </button>
      </div>
    </div>
  );
};

export default OfflineIndicator;
