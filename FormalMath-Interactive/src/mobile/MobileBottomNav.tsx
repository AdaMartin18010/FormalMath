import React from 'react';
import { Link, useLocation } from 'react-router-dom';
import { 
  BookOpen, 
  Network, 
  GitBranch, 
  Brain, 
  BarChart3,
  Layout,
  History,
  MoreHorizontal
} from 'lucide-react';
import { cn } from '@utils/classNames';

interface NavItem {
  path: string;
  label: string;
  icon: React.ReactNode;
  activeIcon?: React.ReactNode;
}

// 底部导航项目（最多5个）
const bottomNavItems: NavItem[] = [
  { 
    path: '/', 
    label: '首页', 
    icon: <BookOpen className="w-5 h-5" />,
    activeIcon: <BookOpen className="w-5 h-5" fill="currentColor" />
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
];

interface MobileBottomNavProps {
  className?: string;
  onMoreClick?: () => void;
}

export const MobileBottomNav: React.FC<MobileBottomNavProps> = ({ 
  className,
  onMoreClick 
}) => {
  const location = useLocation();

  const isActive = (path: string) => {
    if (path === '/') return location.pathname === '/';
    return location.pathname.startsWith(path);
  };

  // 检查是否在更多菜单中
  const isInMoreMenu = moreNavItems.some(item => isActive(item.path));

  return (
    <nav 
      className={cn(
        'fixed bottom-0 left-0 right-0 z-50',
        'bg-white/95 dark:bg-slate-900/95 backdrop-blur-lg',
        'border-t border-gray-200 dark:border-slate-800',
        'safe-area-bottom',
        className
      )}
      style={{
        paddingBottom: 'env(safe-area-inset-bottom, 0px)',
      }}
    >
      <div className="flex items-center justify-around h-16">
        {bottomNavItems.map((item) => {
          const active = isActive(item.path);
          return (
            <Link
              key={item.path}
              to={item.path}
              className={cn(
                'flex flex-col items-center justify-center',
                'w-full h-full min-w-[64px]',
                'transition-colors duration-200',
                active 
                  ? 'text-blue-600 dark:text-blue-400' 
                  : 'text-gray-500 dark:text-gray-400 hover:text-gray-700 dark:hover:text-gray-300'
              )}
            >
              <div className={cn(
                'relative p-1.5 rounded-xl transition-all duration-200',
                active && 'bg-blue-50 dark:bg-blue-900/30'
              )}>
                {active ? item.activeIcon || item.icon : item.icon}
                {active && (
                  <span className="absolute -top-0.5 -right-0.5 w-2 h-2 bg-blue-600 rounded-full" />
                )}
              </div>
              <span className={cn(
                'text-[10px] mt-0.5 font-medium',
                active ? 'text-blue-600 dark:text-blue-400' : 'text-gray-500 dark:text-gray-400'
              )}>
                {item.label}
              </span>
            </Link>
          );
        })}

        {/* 更多按钮 */}
        <button
          onClick={onMoreClick}
          className={cn(
            'flex flex-col items-center justify-center',
            'w-full h-full min-w-[64px]',
            'transition-colors duration-200',
            isInMoreMenu 
              ? 'text-blue-600 dark:text-blue-400' 
              : 'text-gray-500 dark:text-gray-400 hover:text-gray-700 dark:hover:text-gray-300'
          )}
        >
          <div className={cn(
            'relative p-1.5 rounded-xl transition-all duration-200',
            isInMoreMenu && 'bg-blue-50 dark:bg-blue-900/30'
          )}>
            <MoreHorizontal className="w-5 h-5" />
          </div>
          <span className={cn(
            'text-[10px] mt-0.5 font-medium',
            isInMoreMenu ? 'text-blue-600 dark:text-blue-400' : 'text-gray-500 dark:text-gray-400'
          )}>
            更多
          </span>
        </button>
      </div>

      {/* 安全区域指示器（iPhone X+） */}
      <div className="h-[env(safe-area-inset-bottom,0px)] bg-white/95 dark:bg-slate-900/95" />
    </nav>
  );
};

export default MobileBottomNav;
