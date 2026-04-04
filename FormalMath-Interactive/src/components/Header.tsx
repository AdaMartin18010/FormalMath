import React, { useState } from 'react';
import { Link, useLocation } from 'react-router-dom';
import { 
  Menu, 
  X, 
  Search, 
  Bell, 
  User, 
  Settings,
  Github,
  BookOpen,
  Network,
  GitBranch,
  Brain,
  BarChart3,
  Sitemap,
  History
} from 'lucide-react';
import { cn } from '@utils/classNames';

interface NavItem {
  path: string;
  label: string;
  icon: React.ReactNode;
}

const navItems: NavItem[] = [
  { path: '/', label: '首页', icon: <BookOpen className="w-4 h-4" /> },
  { path: '/knowledge-graph', label: '知识图谱', icon: <Network className="w-4 h-4" /> },
  { path: '/reasoning-tree', label: '推理树', icon: <GitBranch className="w-4 h-4" /> },
  { path: '/mind-map', label: '思维导图', icon: <Brain className="w-4 h-4" /> },
  { path: '/comparison', label: '对比分析', icon: <BarChart3 className="w-4 h-4" /> },
  { path: '/decision-tree', label: '决策树', icon: <Sitemap className="w-4 h-4" /> },
  { path: '/evolution', label: '演化历史', icon: <History className="w-4 h-4" /> },
];

export const Header: React.FC = () => {
  const location = useLocation();
  const [isMobileMenuOpen, setIsMobileMenuOpen] = useState(false);
  const [isSearchOpen, setIsSearchOpen] = useState(false);

  const isActive = (path: string) => {
    if (path === '/') return location.pathname === '/';
    return location.pathname.startsWith(path);
  };

  return (
    <header className="sticky top-0 z-50 w-full bg-white border-b border-gray-200 shadow-sm">
      <div className="px-4 mx-auto max-w-7xl sm:px-6 lg:px-8">
        <div className="flex items-center justify-between h-16">
          {/* Logo */}
          <Link to="/" className="flex items-center gap-2">
            <div className="flex items-center justify-center w-10 h-10 bg-blue-600 rounded-lg">
              <span className="text-xl font-bold text-white">F</span>
            </div>
            <div className="hidden sm:block">
              <h1 className="text-lg font-bold text-gray-900">FormalMath</h1>
              <p className="text-xs text-gray-500">交互式可视化平台</p>
            </div>
          </Link>

          {/* Desktop Navigation */}
          <nav className="hidden lg:flex items-center gap-1">
            {navItems.map((item) => (
              <Link
                key={item.path}
                to={item.path}
                className={cn(
                  'flex items-center gap-1.5 px-3 py-2 rounded-md text-sm font-medium transition-colors',
                  isActive(item.path)
                    ? 'bg-blue-50 text-blue-700'
                    : 'text-gray-600 hover:bg-gray-100 hover:text-gray-900'
                )}
              >
                {item.icon}
                {item.label}
              </Link>
            ))}
          </nav>

          {/* Right Actions */}
          <div className="flex items-center gap-2">
            {/* Search Button */}
            <button
              onClick={() => setIsSearchOpen(!isSearchOpen)}
              className="p-2 text-gray-500 hover:text-gray-700 hover:bg-gray-100 rounded-lg transition-colors"
              title="搜索"
            >
              <Search className="w-5 h-5" />
            </button>

            {/* Notifications */}
            <button
              className="relative p-2 text-gray-500 hover:text-gray-700 hover:bg-gray-100 rounded-lg transition-colors"
              title="通知"
            >
              <Bell className="w-5 h-5" />
              <span className="absolute top-1.5 right-1.5 w-2 h-2 bg-red-500 rounded-full" />
            </button>

            {/* Settings */}
            <button
              className="hidden sm:flex p-2 text-gray-500 hover:text-gray-700 hover:bg-gray-100 rounded-lg transition-colors"
              title="设置"
            >
              <Settings className="w-5 h-5" />
            </button>

            {/* User Menu */}
            <button
              className="flex items-center gap-2 p-2 text-gray-500 hover:text-gray-700 hover:bg-gray-100 rounded-lg transition-colors"
              title="用户"
            >
              <User className="w-5 h-5" />
            </button>

            {/* GitHub */}
            <a
              href="https://github.com/formalmath"
              target="_blank"
              rel="noopener noreferrer"
              className="hidden sm:flex p-2 text-gray-500 hover:text-gray-700 hover:bg-gray-100 rounded-lg transition-colors"
              title="GitHub"
            >
              <Github className="w-5 h-5" />
            </a>

            {/* Mobile Menu Toggle */}
            <button
              onClick={() => setIsMobileMenuOpen(!isMobileMenuOpen)}
              className="lg:hidden p-2 text-gray-500 hover:text-gray-700 hover:bg-gray-100 rounded-lg transition-colors"
            >
              {isMobileMenuOpen ? <X className="w-5 h-5" /> : <Menu className="w-5 h-5" />}
            </button>
          </div>
        </div>

        {/* Search Bar */}
        {isSearchOpen && (
          <div className="py-3 border-t border-gray-100">
            <div className="relative">
              <Search className="absolute left-3 top-1/2 -translate-y-1/2 w-5 h-5 text-gray-400" />
              <input
                type="text"
                placeholder="搜索概念、定理、证明..."
                className="w-full pl-10 pr-4 py-2 border border-gray-300 rounded-lg focus:ring-2 focus:ring-blue-500 focus:border-blue-500"
                autoFocus
              />
            </div>
          </div>
        )}
      </div>

      {/* Mobile Navigation */}
      {isMobileMenuOpen && (
        <div className="lg:hidden border-t border-gray-200 bg-white">
          <div className="px-4 py-3 space-y-1">
            {navItems.map((item) => (
              <Link
                key={item.path}
                to={item.path}
                onClick={() => setIsMobileMenuOpen(false)}
                className={cn(
                  'flex items-center gap-3 px-3 py-2.5 rounded-lg text-sm font-medium transition-colors',
                  isActive(item.path)
                    ? 'bg-blue-50 text-blue-700'
                    : 'text-gray-600 hover:bg-gray-100 hover:text-gray-900'
                )}
              >
                {item.icon}
                {item.label}
              </Link>
            ))}
          </div>
        </div>
      )}
    </header>
  );
};

export default Header;
