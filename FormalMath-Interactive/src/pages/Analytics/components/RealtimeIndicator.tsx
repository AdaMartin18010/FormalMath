/**
 * 实时数据状态指示器组件
 * 显示数据连接状态和最后更新时间
 */

import React from 'react';
import { Wifi, WifiOff, RefreshCw, AlertCircle } from 'lucide-react';

interface RealtimeIndicatorProps {
  isConnected: boolean;
  lastUpdate: Date | null;
  connectionStatus: 'connected' | 'disconnected' | 'connecting' | 'error';
  onRefresh?: () => void;
  isRefreshing?: boolean;
}

export const RealtimeIndicator: React.FC<RealtimeIndicatorProps> = ({
  isConnected,
  lastUpdate,
  connectionStatus,
  onRefresh,
  isRefreshing = false,
}) => {
  // 格式化相对时间
  const getRelativeTime = (date: Date): string => {
    const now = new Date();
    const diff = now.getTime() - date.getTime();
    const seconds = Math.floor(diff / 1000);
    const minutes = Math.floor(seconds / 60);
    const hours = Math.floor(minutes / 60);

    if (seconds < 10) return '刚刚';
    if (seconds < 60) return `${seconds}秒前`;
    if (minutes < 60) return `${minutes}分钟前`;
    if (hours < 24) return `${hours}小时前`;
    return date.toLocaleTimeString('zh-CN', { hour: '2-digit', minute: '2-digit' });
  };

  // 获取状态配置
  const getStatusConfig = () => {
    switch (connectionStatus) {
      case 'connected':
        return {
          icon: <Wifi className="w-4 h-4" />,
          text: '实时更新中',
          color: 'text-green-600 dark:text-green-400',
          bgColor: 'bg-green-50 dark:bg-green-900/20',
        };
      case 'connecting':
        return {
          icon: <RefreshCw className="w-4 h-4 animate-spin" />,
          text: '连接中...',
          color: 'text-blue-600 dark:text-blue-400',
          bgColor: 'bg-blue-50 dark:bg-blue-900/20',
        };
      case 'error':
        return {
          icon: <AlertCircle className="w-4 h-4" />,
          text: '连接错误',
          color: 'text-red-600 dark:text-red-400',
          bgColor: 'bg-red-50 dark:bg-red-900/20',
        };
      default:
        return {
          icon: <WifiOff className="w-4 h-4" />,
          text: '已断开',
          color: 'text-gray-500 dark:text-gray-400',
          bgColor: 'bg-gray-100 dark:bg-slate-700',
        };
    }
  };

  const status = getStatusConfig();

  return (
    <div className="flex items-center gap-3">
      {/* 连接状态 */}
      <div className={`flex items-center gap-2 px-3 py-1.5 rounded-full ${status.bgColor}`}>
        <span className={status.color}>{status.icon}</span>
        <span className={`text-sm font-medium ${status.color}`}>{status.text}</span>
      </div>

      {/* 最后更新时间 */}
      {lastUpdate && (
        <span className="text-sm text-gray-500 dark:text-gray-400">
          更新于 {getRelativeTime(lastUpdate)}
        </span>
      )}

      {/* 手动刷新按钮 */}
      {onRefresh && (
        <button
          onClick={onRefresh}
          disabled={isRefreshing}
          className="p-1.5 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-lg 
                   transition-colors disabled:opacity-50"
          title="刷新数据"
        >
          <RefreshCw className={`w-4 h-4 text-gray-500 ${isRefreshing ? 'animate-spin' : ''}`} />
        </button>
      )}
    </div>
  );
};

export default RealtimeIndicator;
