import React from 'react';
import { 
  AlertTriangle, 
  RefreshCw, 
  Home, 
  MessageCircle, 
  ArrowLeft,
  Bug,
  Wifi,
  Clock
} from 'lucide-react';
import { cn } from '@utils/classNames';

interface ErrorBoundaryProps {
  children: React.ReactNode;
  fallback?: React.ReactNode;
  onError?: (error: Error, errorInfo: React.ErrorInfo) => void;
}

interface ErrorBoundaryState {
  hasError: boolean;
  error: Error | null;
  errorInfo: React.ErrorInfo | null;
  errorType: 'runtime' | 'network' | 'timeout' | 'unknown';
}

/**
 * 增强型错误边界组件
 * 提供友好的错误提示和恢复选项
 */
export class ErrorBoundary extends React.Component<ErrorBoundaryProps, ErrorBoundaryState> {
  constructor(props: ErrorBoundaryProps) {
    super(props);
    this.state = {
      hasError: false,
      error: null,
      errorInfo: null,
      errorType: 'unknown',
    };
  }

  static getDerivedStateFromError(error: Error): Partial<ErrorBoundaryState> {
    // 根据错误信息判断错误类型
    let errorType: ErrorBoundaryState['errorType'] = 'unknown';
    
    if (error.message.includes('network') || error.message.includes('fetch')) {
      errorType = 'network';
    } else if (error.message.includes('timeout')) {
      errorType = 'timeout';
    } else if (error.message.includes('runtime') || error.name === 'TypeError') {
      errorType = 'runtime';
    }
    
    return {
      hasError: true,
      error,
      errorType,
    };
  }

  componentDidCatch(error: Error, errorInfo: React.ErrorInfo) {
    console.error('Error caught by boundary:', error, errorInfo);
    
    this.setState({ errorInfo });
    
    // 调用自定义错误处理
    this.props.onError?.(error, errorInfo);
    
    // 可以在这里发送错误报告到分析服务
    this.reportError(error, errorInfo);
  }

  private reportError(error: Error, errorInfo: React.ErrorInfo) {
    // 发送到错误追踪服务
    if ('gtag' in window) {
      (window as any).gtag('event', 'exception', {
        description: `${error.message} ${errorInfo.componentStack}`,
        fatal: true,
      });
    }
    
    // 发送到自定义错误报告API
    try {
      fetch('/api/errors/report', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          error: error.message,
          stack: error.stack,
          componentStack: errorInfo.componentStack,
          url: window.location.href,
          userAgent: navigator.userAgent,
          timestamp: new Date().toISOString(),
        }),
      }).catch(() => {}); // 忽略报告发送失败
    } catch {
      // 忽略发送错误
    }
  }

  private handleRetry = () => {
    this.setState({
      hasError: false,
      error: null,
      errorInfo: null,
      errorType: 'unknown',
    });
  };

  private handleReload = () => {
    window.location.reload();
  };

  private handleGoHome = () => {
    window.location.href = '/';
  };

  private handleGoBack = () => {
    window.history.back();
  };

  render() {
    if (this.state.hasError) {
      // 使用自定义fallback或默认错误UI
      if (this.props.fallback) {
        return this.props.fallback;
      }
      
      return (
        <ErrorFallback
          error={this.state.error}
          errorType={this.state.errorType}
          onRetry={this.handleRetry}
          onReload={this.handleReload}
          onGoHome={this.handleGoHome}
          onGoBack={this.handleGoBack}
        />
      );
    }

    return this.props.children;
  }
}

/**
 * 错误回退UI组件
 */
interface ErrorFallbackProps {
  error: Error | null;
  errorType: 'runtime' | 'network' | 'timeout' | 'unknown';
  onRetry: () => void;
  onReload: () => void;
  onGoHome: () => void;
  onGoBack: () => void;
}

const ErrorFallback: React.FC<ErrorFallbackProps> = ({
  error,
  errorType,
  onRetry,
  onReload,
  onGoHome,
  onGoBack,
}) => {
  const config = errorConfig[errorType];
  
  return (
    <div className="min-h-screen flex items-center justify-center bg-gray-50 dark:bg-slate-900 p-4">
      <div className="max-w-md w-full bg-white dark:bg-slate-800 rounded-2xl shadow-xl overflow-hidden">
        {/* 顶部装饰 */}
        <div className={cn('h-2', config.color)} />
        
        <div className="p-8">
          {/* 错误图标 */}
          <div className={cn(
            'w-20 h-20 rounded-2xl flex items-center justify-center mx-auto mb-6',
            config.bgColor
          )}>
            {config.icon}
          </div>
          
          {/* 错误标题 */}
          <h1 className="text-2xl font-bold text-center text-gray-900 dark:text-white mb-2">
            {config.title}
          </h1>
          
          {/* 错误描述 */}
          <p className="text-center text-gray-600 dark:text-gray-400 mb-2">
            {config.description}
          </p>
          
          {/* 技术错误信息（可折叠） */}
          {error && (
            <details className="mt-4 mb-6">
              <summary className="text-sm text-gray-500 cursor-pointer hover:text-gray-700 flex items-center gap-2">
                <Bug className="w-4 h-4" />
                查看技术详情
              </summary>
              <div className="mt-2 p-3 bg-gray-100 dark:bg-slate-700 rounded-lg">
                <code className="text-xs text-red-600 dark:text-red-400 break-all">
                  {error.message}
                </code>
              </div>
            </details>
          )}
          
          {/* 操作按钮 */}
          <div className="space-y-3">
            {/* 主要操作 */}
            <button
              onClick={onRetry}
              className={cn(
                'w-full flex items-center justify-center gap-2 px-6 py-3 rounded-xl font-medium transition-colors',
                config.buttonColor
              )}
            >
              <RefreshCw className="w-5 h-5" />
              {config.actionText}
            </button>
            
            {/* 次要操作 */}
            <div className="grid grid-cols-3 gap-2">
              <button
                onClick={onReload}
                className="flex flex-col items-center gap-1 p-3 text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-xl transition-colors"
              >
                <RefreshCw className="w-5 h-5" />
                <span className="text-xs">刷新页面</span>
              </button>
              
              <button
                onClick={onGoBack}
                className="flex flex-col items-center gap-1 p-3 text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-xl transition-colors"
              >
                <ArrowLeft className="w-5 h-5" />
                <span className="text-xs">返回上一页</span>
              </button>
              
              <button
                onClick={onGoHome}
                className="flex flex-col items-center gap-1 p-3 text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-xl transition-colors"
              >
                <Home className="w-5 h-5" />
                <span className="text-xs">返回首页</span>
              </button>
            </div>
          </div>
          
          {/* 帮助链接 */}
          <div className="mt-6 pt-6 border-t border-gray-200 dark:border-slate-700 text-center">
            <p className="text-sm text-gray-500">
              问题持续存在？
              <a
                href="mailto:support@formalmath.example.com"
                className="text-blue-600 hover:text-blue-700 ml-1 inline-flex items-center gap-1"
              >
                <MessageCircle className="w-4 h-4" />
                联系我们
              </a>
            </p>
          </div>
        </div>
      </div>
    </div>
  );
};

// 错误配置
const errorConfig = {
  network: {
    icon: <Wifi className="w-10 h-10 text-orange-600" />,
    title: '网络连接错误',
    description: '无法连接到服务器，请检查您的网络连接后重试。',
    actionText: '重新连接',
    color: 'bg-orange-500',
    bgColor: 'bg-orange-100 dark:bg-orange-900/30',
    buttonColor: 'bg-orange-600 text-white hover:bg-orange-700',
  },
  timeout: {
    icon: <Clock className="w-10 h-10 text-yellow-600" />,
    title: '请求超时',
    description: '服务器响应时间过长，请稍后重试。',
    actionText: '重试',
    color: 'bg-yellow-500',
    bgColor: 'bg-yellow-100 dark:bg-yellow-900/30',
    buttonColor: 'bg-yellow-600 text-white hover:bg-yellow-700',
  },
  runtime: {
    icon: <Bug className="w-10 h-10 text-red-600" />,
    title: '应用程序错误',
    description: '抱歉，应用程序遇到了意外错误。',
    actionText: '重试',
    color: 'bg-red-500',
    bgColor: 'bg-red-100 dark:bg-red-900/30',
    buttonColor: 'bg-red-600 text-white hover:bg-red-700',
  },
  unknown: {
    icon: <AlertTriangle className="w-10 h-10 text-blue-600" />,
    title: '出错了',
    description: '抱歉，发生了意外错误。我们已经收到错误报告并会尽快修复。',
    actionText: '重试',
    color: 'bg-blue-500',
    bgColor: 'bg-blue-100 dark:bg-blue-900/30',
    buttonColor: 'bg-blue-600 text-white hover:bg-blue-700',
  },
};

export default ErrorBoundary;
