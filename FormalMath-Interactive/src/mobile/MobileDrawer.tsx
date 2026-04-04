import React, { useEffect, useCallback } from 'react';
import { X, BarChart3, Layout, History, Settings, Moon, Sun, Monitor, Download } from 'lucide-react';
import { cn } from '@utils/classNames';
import { useDarkMode } from '@hooks/mobile/useDarkMode';
import { usePWAState } from '@hooks/mobile/useMobileDetect';

interface MobileDrawerProps {
  isOpen: boolean;
  onClose: () => void;
  onNavigate: (path: string) => void;
}

interface MenuItem {
  icon: React.ReactNode;
  label: string;
  action: () => void;
  variant?: 'default' | 'danger' | 'primary';
}

interface MenuSection {
  title: string;
  items: MenuItem[];
}

export const MobileDrawer: React.FC<MobileDrawerProps> = ({ 
  isOpen, 
  onClose,
  onNavigate 
}) => {
  const { theme, isDark, enableDark, enableLight, enableSystem } = useDarkMode();
  const { isStandalone, canInstall, promptInstall } = usePWAState();

  // 处理返回键关闭
  useEffect(() => {
    const handlePopState = () => {
      if (isOpen) {
        onClose();
      }
    };

    if (isOpen) {
      window.history.pushState({ drawer: true }, '');
      window.addEventListener('popstate', handlePopState);
      document.body.style.overflow = 'hidden';
    }

    return () => {
      window.removeEventListener('popstate', handlePopState);
      document.body.style.overflow = '';
    };
  }, [isOpen, onClose]);

  // 处理 ESC 键关闭
  useEffect(() => {
    const handleKeyDown = (e: KeyboardEvent) => {
      if (e.key === 'Escape' && isOpen) {
        onClose();
      }
    };

    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, [isOpen, onClose]);

  const handleInstall = useCallback(async () => {
    await promptInstall();
    onClose();
  }, [promptInstall, onClose]);

  const handleNavigate = useCallback((path: string) => {
    onNavigate(path);
    onClose();
  }, [onNavigate, onClose]);

  const menuSections: MenuSection[] = [
    {
      title: '功能',
      items: [
        {
          icon: <BarChart3 className="w-5 h-5" />,
          label: '对比分析',
          action: () => handleNavigate('/comparison'),
        },
        {
          icon: <Layout className="w-5 h-5" />,
          label: '决策树',
          action: () => handleNavigate('/decision-tree'),
        },
        {
          icon: <History className="w-5 h-5" />,
          label: '演化历史',
          action: () => handleNavigate('/evolution'),
        },
      ],
    },
    {
      title: '外观',
      items: [
        {
          icon: <Sun className="w-5 h-5" />,
          label: '浅色模式',
          action: enableLight,
          variant: theme === 'light' ? 'primary' : 'default',
        },
        {
          icon: <Moon className="w-5 h-5" />,
          label: '深色模式',
          action: enableDark,
          variant: theme === 'dark' ? 'primary' : 'default',
        },
        {
          icon: <Monitor className="w-5 h-5" />,
          label: '跟随系统',
          action: enableSystem,
          variant: theme === 'system' ? 'primary' : 'default',
        },
      ],
    },
  ];

  // 如果可以安装 PWA，添加安装选项
  if (canInstall && !isStandalone) {
    menuSections.push({
      title: '应用',
      items: [
        {
          icon: <Download className="w-5 h-5" />,
          label: '安装应用',
          action: handleInstall,
          variant: 'primary',
        },
      ],
    });
  }

  return (
    <>
      {/* 遮罩层 */}
      <div
        className={cn(
          'fixed inset-0 z-50 bg-black/50 backdrop-blur-sm transition-opacity duration-300',
          isOpen ? 'opacity-100' : 'opacity-0 pointer-events-none'
        )}
        onClick={onClose}
      />

      {/* 抽屉 */}
      <div
        className={cn(
          'fixed right-0 top-0 bottom-0 z-50 w-[280px]',
          'bg-white dark:bg-slate-900',
          'shadow-2xl',
          'transform transition-transform duration-300 ease-out',
          isOpen ? 'translate-x-0' : 'translate-x-full'
        )}
      >
        {/* 头部 */}
        <div className="flex items-center justify-between p-4 border-b border-gray-200 dark:border-slate-800">
          <div>
            <h2 className="text-lg font-semibold text-gray-900 dark:text-white">
              更多选项
            </h2>
            <p className="text-sm text-gray-500 dark:text-gray-400">
              FormalMath v1.0.0
            </p>
          </div>
          <button
            onClick={onClose}
            className="p-2 text-gray-500 hover:text-gray-700 dark:text-gray-400 dark:hover:text-gray-200 hover:bg-gray-100 dark:hover:bg-slate-800 rounded-lg transition-colors"
          >
            <X className="w-5 h-5" />
          </button>
        </div>

        {/* 菜单内容 */}
        <div className="overflow-y-auto h-[calc(100%-80px)] pb-safe">
          {menuSections.map((section, sectionIndex) => (
            <div 
              key={section.title}
              className={cn(
                'px-4 py-3',
                sectionIndex > 0 && 'border-t border-gray-200 dark:border-slate-800'
              )}
            >
              <h3 className="text-xs font-semibold text-gray-500 dark:text-gray-400 uppercase tracking-wider mb-2 px-2">
                {section.title}
              </h3>
              <div className="space-y-1">
                {section.items.map((item, itemIndex) => (
                  <button
                    key={`${section.title}-${itemIndex}`}
                    onClick={item.action}
                    className={cn(
                      'w-full flex items-center gap-3 px-3 py-2.5 rounded-lg text-sm font-medium transition-colors',
                      item.variant === 'primary' 
                        ? 'bg-blue-50 dark:bg-blue-900/30 text-blue-600 dark:text-blue-400' 
                        : 'text-gray-700 dark:text-gray-300 hover:bg-gray-100 dark:hover:bg-slate-800'
                    )}
                  >
                    <span className={cn(
                      item.variant === 'primary' 
                        ? 'text-blue-600 dark:text-blue-400' 
                        : 'text-gray-500 dark:text-gray-400'
                    )}>
                      {item.icon}
                    </span>
                    {item.label}
                    {item.variant === 'primary' && (
                      <span className="ml-auto w-2 h-2 bg-blue-600 rounded-full" />
                    )}
                  </button>
                ))}
              </div>
            </div>
          ))}

          {/* 关于 */}
          <div className="px-4 py-3 border-t border-gray-200 dark:border-slate-800">
            <div className="px-3 py-2 text-xs text-gray-500 dark:text-gray-400">
              <p>© 2024 FormalMath Team</p>
              <p className="mt-1">MIT License</p>
            </div>
          </div>
        </div>
      </div>
    </>
  );
};

export default MobileDrawer;
