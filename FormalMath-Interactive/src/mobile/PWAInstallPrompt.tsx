import React, { useState, useEffect } from 'react';
import { X, Download, Smartphone, Share2 } from 'lucide-react';
import { cn } from '@utils/classNames';
import { usePWAState } from '@hooks/mobile/useMobileDetect';

interface PWAInstallPromptProps {
  className?: string;
  delay?: number; // 延迟显示时间（毫秒）
}

/**
 * PWA 安装提示组件
 */
export const PWAInstallPrompt: React.FC<PWAInstallPromptProps> = ({
  className,
  delay = 3000,
}) => {
  const { isStandalone, canInstall, promptInstall } = usePWAState();
  const [isVisible, setIsVisible] = useState(false);
  const [isDismissed, setIsDismissed] = useState(false);

  // 检测是否是 iOS Safari
  const isIOS = /iPad|iPhone|iPod/.test(navigator.userAgent) && !(window as any).MSStream;
  const isSafari = /^((?!chrome|android).)*safari/i.test(navigator.userAgent);
  const isIOSSafari = isIOS && isSafari;

  useEffect(() => {
    // 如果已经安装或用户已关闭提示，不显示
    if (isStandalone || isDismissed) return;

    // 检查本地存储
    const dismissed = localStorage.getItem('pwa-prompt-dismissed');
    if (dismissed) {
      const dismissedTime = parseInt(dismissed, 10);
      // 7天后再次显示
      if (Date.now() - dismissedTime < 7 * 24 * 60 * 60 * 1000) {
        return;
      }
    }

    // 延迟显示
    const timer = setTimeout(() => {
      setIsVisible(true);
    }, delay);

    return () => clearTimeout(timer);
  }, [isStandalone, isDismissed, delay]);

  const handleDismiss = () => {
    setIsVisible(false);
    setIsDismissed(true);
    localStorage.setItem('pwa-prompt-dismissed', Date.now().toString());
  };

  const handleInstall = async () => {
    if (canInstall) {
      await promptInstall();
    }
    handleDismiss();
  };

  // 如果已安装或不满足显示条件，不渲染
  if (isStandalone || (!canInstall && !isIOSSafari)) return null;

  return (
    <div
      className={cn(
        'fixed bottom-20 left-4 right-4 z-50',
        'transition-all duration-300 ease-out',
        isVisible ? 'opacity-100 translate-y-0' : 'opacity-0 translate-y-4 pointer-events-none',
        className
      )}
    >
      <div className="bg-white dark:bg-slate-800 rounded-2xl shadow-2xl border border-gray-200 dark:border-slate-700 p-4">
        {/* 头部 */}
        <div className="flex items-start gap-3">
          {/* 图标 */}
          <div className="flex-shrink-0 w-12 h-12 bg-blue-600 rounded-xl flex items-center justify-center">
            <span className="text-xl font-bold text-white">F</span>
          </div>

          {/* 内容 */}
          <div className="flex-1 min-w-0">
            <h3 className="font-semibold text-gray-900 dark:text-white text-sm">
              安装 FormalMath
            </h3>
            <p className="text-xs text-gray-500 dark:text-gray-400 mt-0.5">
              {isIOSSafari 
                ? '添加到主屏幕，随时随地学习数学' 
                : '安装应用，获得更好的体验'}
            </p>
          </div>

          {/* 关闭按钮 */}
          <button
            onClick={handleDismiss}
            className="flex-shrink-0 p-1 text-gray-400 hover:text-gray-600 dark:hover:text-gray-200 transition-colors"
          >
            <X className="w-4 h-4" />
          </button>
        </div>

        {/* iOS Safari 安装说明 */}
        {isIOSSafari ? (
          <div className="mt-3 p-3 bg-gray-50 dark:bg-slate-700/50 rounded-lg">
            <ol className="text-xs text-gray-600 dark:text-gray-300 space-y-2">
              <li className="flex items-center gap-2">
                <span className="flex-shrink-0 w-5 h-5 bg-blue-100 dark:bg-blue-900/30 text-blue-600 dark:text-blue-400 rounded-full flex items-center justify-center text-[10px] font-medium">1</span>
                <span>点击底部分享按钮</span>
                <Share2 className="w-3 h-3 text-gray-400" />
              </li>
              <li className="flex items-center gap-2">
                <span className="flex-shrink-0 w-5 h-5 bg-blue-100 dark:bg-blue-900/30 text-blue-600 dark:text-blue-400 rounded-full flex items-center justify-center text-[10px] font-medium">2</span>
                <span>选择"添加到主屏幕"</span>
                <span className="text-lg leading-none">➕</span>
              </li>
            </ol>
          </div>
        ) : (
          /* 安装按钮 */
          <button
            onClick={handleInstall}
            className="mt-3 w-full flex items-center justify-center gap-2 px-4 py-2.5 bg-blue-600 hover:bg-blue-700 text-white text-sm font-medium rounded-xl transition-colors"
          >
            <Download className="w-4 h-4" />
            安装应用
          </button>
        )}

        {/* 底部提示 */}
        <div className="mt-2 flex items-center justify-center gap-1 text-[10px] text-gray-400">
          <Smartphone className="w-3 h-3" />
          <span>无需下载，添加到主屏幕即可使用</span>
        </div>
      </div>
    </div>
  );
};

export default PWAInstallPrompt;
