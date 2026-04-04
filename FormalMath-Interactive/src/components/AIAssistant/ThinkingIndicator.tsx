import React from 'react';
import { Brain, Sparkles } from 'lucide-react';

interface ThinkingIndicatorProps {
  message?: string;
  showSparkles?: boolean;
  size?: 'sm' | 'md' | 'lg';
}

/**
 * AI思考状态指示器组件
 * 
 * 显示AI正在思考的动画效果，包含波动的点动画和可选的闪光效果
 */
export const ThinkingIndicator: React.FC<ThinkingIndicatorProps> = ({
  message = 'AI正在思考',
  showSparkles = true,
  size = 'md',
}) => {
  const sizeClasses = {
    sm: {
      container: 'gap-1.5 p-2',
      icon: 'w-3 h-3',
      text: 'text-xs',
      dot: 'w-1 h-1',
    },
    md: {
      container: 'gap-2 p-3',
      icon: 'w-4 h-4',
      text: 'text-sm',
      dot: 'w-1.5 h-1.5',
    },
    lg: {
      container: 'gap-3 p-4',
      icon: 'w-5 h-5',
      text: 'text-base',
      dot: 'w-2 h-2',
    },
  };

  const classes = sizeClasses[size];

  return (
    <div className={`flex items-center ${classes.container}`}>
      {/* 图标 */}
      <div className="relative">
        <Brain className={`${classes.icon} text-blue-500`} />
        
        {/* 闪光效果 */}
        {showSparkles && (
          <>
            <Sparkles 
              className={`absolute -top-1 -right-1 ${size === 'sm' ? 'w-2 h-2' : 'w-3 h-3'} 
                         text-yellow-400 animate-pulse`} 
            />
            <div className="absolute inset-0 bg-blue-400 rounded-full animate-ping opacity-20" />
          </>
        )}
      </div>

      {/* 文字 */}
      <span className={`${classes.text} text-gray-600 font-medium`}>
        {message}
      </span>

      {/* 波动点动画 */}
      <div className="flex gap-1">
        {[0, 1, 2].map((i) => (
          <span
            key={i}
            className={`${classes.dot} bg-blue-400 rounded-full animate-bounce`}
            style={{
              animationDelay: `${i * 0.15}s`,
              animationDuration: '0.8s',
            }}
          />
        ))}
      </div>
    </div>
  );
};

/**
 * 流式响应指示器
 * 显示AI正在生成响应的状态
 */
export const StreamingIndicator: React.FC = () => {
  return (
    <div className="flex items-center gap-2 px-3 py-2 bg-blue-50 rounded-lg">
      <div className="flex gap-1">
        {[0, 1, 2].map((i) => (
          <span
            key={i}
            className="w-1.5 h-1.5 bg-blue-500 rounded-full animate-pulse"
            style={{
              animationDelay: `${i * 0.1}s`,
            }}
          />
        ))}
      </div>
      <span className="text-xs text-blue-600">正在输入...</span>
    </div>
  );
};

/**
 * 思考步骤指示器
 * 显示AI思考的各个步骤
 */
interface ThinkingStep {
  id: string;
  label: string;
  status: 'pending' | 'active' | 'completed';
}

interface ThinkingStepsProps {
  steps: ThinkingStep[];
}

export const ThinkingSteps: React.FC<ThinkingStepsProps> = ({ steps }) => {
  return (
    <div className="space-y-2 py-2">
      {steps.map((step, index) => (
        <div
          key={step.id}
          className={`flex items-center gap-2 text-sm transition-colors duration-300 ${
            step.status === 'completed'
              ? 'text-green-600'
              : step.status === 'active'
              ? 'text-blue-600'
              : 'text-gray-400'
          }`}
        >
          {/* 状态图标 */}
          <div className="w-5 h-5 flex items-center justify-center">
            {step.status === 'completed' ? (
              <svg className="w-4 h-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                <path strokeLinecap="round" strokeLinejoin="round" strokeWidth={2} d="M5 13l4 4L19 7" />
              </svg>
            ) : step.status === 'active' ? (
              <div className="w-3 h-3 border-2 border-blue-600 border-t-transparent rounded-full animate-spin" />
            ) : (
              <div className="w-2 h-2 bg-gray-300 rounded-full" />
            )}
          </div>

          {/* 步骤标签 */}
          <span className={step.status === 'active' ? 'font-medium' : ''}>
            {step.label}
          </span>

          {/* 连接线 */}
          {index < steps.length - 1 && (
            <div
              className={`absolute left-2.5 top-6 w-0.5 h-4 ${
                step.status === 'completed' ? 'bg-green-400' : 'bg-gray-200'
              }`}
            />
          )}
        </div>
      ))}
    </div>
  );
};

export default ThinkingIndicator;
