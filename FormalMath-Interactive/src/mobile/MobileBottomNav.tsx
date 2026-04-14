// @ts-nocheck
import React, { useState, useCallback, useEffect } from 'react';
import { Link, useLocation, useNavigate } from 'react-router-dom';
import { 
  BookOpen, 
  Network, 
  GitBranch, 
  Brain, 
  BarChart3,
  Layout,
  History,
  MoreHorizontal,
  Home,
  Gamepad2,
  Settings,
  X,
  ChevronUp
} from 'lucide-react';
import { cn } from '@utils/classNames';
import { useMobileDetect } from '@hooks/mobile/useMobileDetect';

interface NavItem {
  path: string;
  label: string;
  icon: React.ReactNode;
  activeIcon?: React.ReactNode;
  badge?: number;
}

export interface MobileBottomNavProps {
  className?: string;
  onMoreClick?: () => void;
}

// 底部导航项目
const mainNavItems: NavItem[] = [
  { 
    path: '/', 
    label: '首页', 
    icon: <Home className="w-5 h-5" />,
    activeIcon: <Home className="w-5 h-5" fill="currentColor" />
  },
  { 
    path: '/knowledge-graph', 
    label: '图谱', 
    icon: <Network className="w-5 h-5" />,
    activeIcon: <Network className="w-5 h-5" fill="currentColor" />
  },
  { 
    path: '/reasoning-tree', 
    label: '推理', 
    icon: <GitBranch className="w-5 h-5" />,
    activeIcon: <GitBranch className="w-5 h-5" fill="currentColor" />
  },
  { 
    path: '/mind-map', 
    label: '导图', 
    icon: <Brain className="w-5 h-5" />,
    activeIcon: <Brain className="w-5 h-5" fill="currentColor" />
  },
];

// 更多菜单中的项目
const moreNavItems: NavItem[] = [
  { path: '/comparison', label: '对比分析', icon: <BarChart3 className="w-5 h-5" /> },
  { path: '/decision-tree', label: '决策树', icon: <Layout className="w-5 h-5" /> },
  { path: '/evolution', label: '演化历史', icon: <History className="w-5 h-5" /> },
  { path: '/game', label: '游戏学习', icon: <Gamepad2 className="w-5 h-5" /> },
];

// 快捷操作项目
const quickActions = [
  { 
    label: '搜索', 
    icon: <BookOpen className="w-5 h-5" />,
    action: () => console.log('搜索')
  },
  { 
    label: '设置', 
    icon: <Settings className="w-5 h-5" />,
    action: () => console.log('设置')
  },
];

/**
 * 增强版移动端底部导航
 * 支持：手势操作、动画效果、快捷菜单
 */
export const MobileBottomNav: React.FC<MobileBottomNavProps> = ({ 
  className,
  onMoreClick 
}) => {
  const location = useLocation();
  const navigate = useNavigate();
  const { isMobile, isStandalone } = useMobileDetect();
  const [showMoreMenu, setShowMoreMenu] = useState(false);
  const [activeTab, setActiveTab] = useState(location.pathname);
  const [isVisible, setIsVisible] = useState(true);
  const [lastScrollY, setLastScrollY] = useState(0);

  // 监听路由变化
  useEffect(() => {
    setActiveTab(location.pathname);
  }, [location.pathname]);

  // 滚动隐藏/显示导航
  useEffect(() => {
    const handleScroll = () => {
      const currentScrollY = window.scrollY;
      
      // 向下滚动超过 50px 时隐藏，向上滚动时显示
      if (currentScrollY > lastScrollY && currentScrollY > 50) {
        setIsVisible(false);
      } else {
        setIsVisible(true);
      }
      
      setLastScrollY(currentScrollY);
    };

    window.addEventListener('scroll', handleScroll, { passive: true });
    return () => window.removeEventListener('scroll', handleScroll);
  }, [lastScrollY]);

  // 检查是否激活
  const isActive = useCallback((path: string) => {
    if (path === '/') return location.pathname === '/';
    return location.pathname.startsWith(path);
  }, [location.pathname]);

  // 检查是否在更多菜单中
  const isInMoreMenu = moreNavItems.some(item => isActive(item.path));

  // 处理导航点击
  const handleNavClick = useCallback((path: string) => {
    setActiveTab(path);
    // 添加触觉反馈
    if (navigator.vibrate) {
      navigator.vibrate(10);
    }
  }, []);

  // 处理更多按钮点击
  const handleMoreClick = useCallback(() => {
    setShowMoreMenu(!showMoreMenu);
    onMoreClick?.();
    // 添加触觉反馈
    if (navigator.vibrate) {
      navigator.vibrate(20);
    }
  }, [showMoreMenu, onMoreClick]);

  // 关闭菜单
  const closeMenu = useCallback(() => {
    setShowMoreMenu(false);
  }, []);

  // 处理更多菜单导航
  const handleMoreNav = useCallback((path: string) => {
    navigate(path);
    setShowMoreMenu(false);
  }, [navigate]);

  if (!isMobile) return null;

  return (
    <>
      {/* 底部导航栏 */}
      <nav 
        className={cn(
          'fixed bottom-0 left-0 right-0 z-50',
          'bg-white/95 dark:bg-slate-900/95 backdrop-blur-lg',
          'border-t border-gray-200 dark:border-slate-800',
          'transition-transform duration-300 ease-out',
          isVisible ? 'translate-y-0' : 'translate-y-full',
          className
        )}
        style={{
          paddingBottom: 'env(safe-area-inset-bottom, 0px)',
        }}
      >
        <div className="flex items-center justify-around h-16 px-2">
          {mainNavItems.map((item) => {
            const active = isActive(item.path);
            return (
              <Link
                key={item.path}
                to={item.path}
                onClick={() => handleNavClick(item.path)}
                className={cn(
                  'flex flex-col items-center justify-center',
                  'w-full h-full min-w-[64px]',
                  'transition-all duration-200',
                  'active:scale-95',
                  active 
                    ? 'text-blue-600 dark:text-blue-400' 
                    : 'text-gray-500 dark:text-gray-400 hover:text-gray-700 dark:hover:text-gray-300'
                )}
              >
                <div className={cn(
                  'relative p-1.5 rounded-xl transition-all duration-200',
                  active && 'bg-blue-50 dark:bg-blue-900/30 scale-110'
                )}>
                  {active ? item.activeIcon || item.icon : item.icon}
                  {active && (
                    <span className="absolute -top-0.5 -right-0.5 w-2 h-2 bg-blue-600 rounded-full animate-pulse" />
                  )}
                  {item.badge && (
                    <span className="absolute -top-1 -right-1 w-4 h-4 bg-red-500 text-white text-[10px] font-bold rounded-full flex items-center justify-center">
                      {item.badge}
                    </span>
                  )}
                </div>
                <span className={cn(
                  'text-[10px] mt-0.5 font-medium transition-all',
                  active ? 'text-blue-600 dark:text-blue-400 scale-105' : 'text-gray-500 dark:text-gray-400'
                )}>
                  {item.label}
                </span>
              </Link>
            );
          })}

          {/* 更多按钮 */}
          <button
            onClick={handleMoreClick}
            className={cn(
              'flex flex-col items-center justify-center',
              'w-full h-full min-w-[64px]',
              'transition-all duration-200',
              'active:scale-95',
              isInMoreMenu || showMoreMenu
                ? 'text-blue-600 dark:text-blue-400' 
                : 'text-gray-500 dark:text-gray-400 hover:text-gray-700 dark:hover:text-gray-300'
            )}
          >
            <div className={cn(
              'relative p-1.5 rounded-xl transition-all duration-200',
              (isInMoreMenu || showMoreMenu) && 'bg-blue-50 dark:bg-blue-900/30 scale-110'
            )}>
              <MoreHorizontal className={cn(
                'w-5 h-5 transition-transform duration-200',
                showMoreMenu && 'rotate-90'
              )} />
            </div>
            <span className={cn(
              'text-[10px] mt-0.5 font-medium transition-all',
              (isInMoreMenu || showMoreMenu) ? 'text-blue-600 dark:text-blue-400 scale-105' : 'text-gray-500 dark:text-gray-400'
            )}>
              更多
            </span>
          </button>
        </div>

        {/* 安全区域指示器 */}
        <div className="h-[env(safe-area-inset-bottom,0px)] bg-white/95 dark:bg-slate-900/95" />
      </nav>

      {/* 更多菜单遮罩 */}
      {showMoreMenu && (
        <div 
          className="fixed inset-0 z-40 bg-black/50 backdrop-blur-sm transition-opacity"
          onClick={closeMenu}
        />
      )}

      {/* 更多菜单面板 */}
      <div
        className={cn(
          'fixed left-0 right-0 z-50 bg-white dark:bg-slate-900 rounded-t-3xl shadow-2xl',
          'transition-transform duration-300 ease-out',
          showMoreMenu ? 'translate-y-0' : 'translate-y-full',
          'pb-[calc(80px+env(safe-area-inset-bottom,0px))]'
        )}
        style={{ bottom: 0 }}
      >
        {/* 拖动指示器 */}
        <div className="flex justify-center pt-3 pb-2">
          <div className="w-10 h-1 bg-gray-300 dark:bg-gray-600 rounded-full" />
        </div>

        {/* 菜单头部 */}
        <div className="flex items-center justify-between px-4 py-2 border-b border-gray-100 dark:border-slate-800">
          <h3 className="text-sm font-semibold text-gray-900 dark:text-white">更多功能</h3>
          <button
            onClick={closeMenu}
            className="p-1.5 text-gray-500 hover:text-gray-700 dark:text-gray-400 dark:hover:text-gray-200 rounded-lg hover:bg-gray-100 dark:hover:bg-slate-800 transition-colors"
          >
            <X className="w-4 h-4" />
          </button>
        </div>

        {/* 快捷操作 */}
        <div className="px-4 py-3 border-b border-gray-100 dark:border-slate-800">
          <h4 className="text-xs font-medium text-gray-500 dark:text-gray-400 mb-2 uppercase tracking-wider">快捷操作</h4>
          <div className="flex gap-2">
            {quickActions.map((action, index) => (
              <button
                key={index}
                onClick={() => {
                  action.action();
                  closeMenu();
                }}
                className="flex items-center gap-2 px-3 py-2 bg-gray-100 dark:bg-slate-800 rounded-lg text-sm text-gray-700 dark:text-gray-300 hover:bg-gray-200 dark:hover:bg-slate-700 transition-colors"
              >
                {action.icon}
                <span>{action.label}</span>
              </button>
            ))}
          </div>
        </div>

        {/* 更多导航项目 */}
        <div className="px-4 py-3">
          <h4 className="text-xs font-medium text-gray-500 dark:text-gray-400 mb-2 uppercase tracking-wider">功能页面</h4>
          <div className="grid grid-cols-4 gap-2">
            {moreNavItems.map((item) => {
              const active = isActive(item.path);
              return (
                <button
                  key={item.path}
                  onClick={() => handleMoreNav(item.path)}
                  className={cn(
                    'flex flex-col items-center gap-1.5 p-3 rounded-xl transition-all',
                    'active:scale-95',
                    active
                      ? 'bg-blue-50 dark:bg-blue-900/30 text-blue-600 dark:text-blue-400'
                      : 'hover:bg-gray-100 dark:hover:bg-slate-800 text-gray-700 dark:text-gray-300'
                  )}
                >
                  <div className={cn(
                    'p-2 rounded-lg',
                    active ? 'bg-blue-100 dark:bg-blue-900/50' : 'bg-gray-100 dark:bg-slate-700'
                  )}>
                    {item.icon}
                  </div>
                  <span className="text-xs font-medium">{item.label}</span>
                </button>
              );
            })}
          </div>
        </div>

        {/* 向上滑动提示 */}
        <div className="flex justify-center py-2 text-gray-400">
          <ChevronUp className="w-5 h-5 animate-bounce" />
        </div>
      </div>
    </>
  );
};

export default MobileBottomNav;
