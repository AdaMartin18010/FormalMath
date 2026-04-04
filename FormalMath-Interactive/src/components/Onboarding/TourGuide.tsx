import React, { useState, useEffect, useCallback } from 'react';
import { 
  X, 
  ChevronRight, 
  ChevronLeft, 
  Sparkles, 
  Target,
  BookOpen,
  Network,
  GitBranch,
  CheckCircle2
} from 'lucide-react';
import { cn } from '@utils/classNames';

interface TourStep {
  id: string;
  title: string;
  description: string;
  icon?: React.ReactNode;
  target?: string; // CSS选择器
  placement?: 'top' | 'bottom' | 'left' | 'right';
}

interface TourGuideProps {
  steps: TourStep[];
  isOpen: boolean;
  onClose: () => void;
  onComplete?: () => void;
  storageKey?: string; // 用于保存完成状态
}

/**
 * 用户引导组件
 * 提供分步骤的产品导览
 */
export const TourGuide: React.FC<TourGuideProps> = ({
  steps,
  isOpen,
  onClose,
  onComplete,
  storageKey = 'tour-completed',
}) => {
  const [currentStep, setCurrentStep] = useState(0);
  const [targetRect, setTargetRect] = useState<DOMRect | null>(null);
  const [showSpotlight, setShowSpotlight] = useState(false);

  const currentStepData = steps[currentStep];
  const isFirstStep = currentStep === 0;
  const isLastStep = currentStep === steps.length - 1;

  useEffect(() => {
    if (isOpen && currentStepData?.target) {
      const target = document.querySelector(currentStepData.target);
      if (target) {
        const rect = target.getBoundingClientRect();
        setTargetRect(rect);
        setShowSpotlight(true);
        
        // 滚动到目标元素
        target.scrollIntoView({ behavior: 'smooth', block: 'center' });
      }
    } else {
      setShowSpotlight(false);
    }
  }, [isOpen, currentStep, currentStepData]);

  const handleNext = useCallback(() => {
    if (isLastStep) {
      handleComplete();
    } else {
      setCurrentStep(prev => prev + 1);
    }
  }, [isLastStep]);

  const handlePrev = () => {
    setCurrentStep(prev => Math.max(0, prev - 1));
  };

  const handleComplete = () => {
    localStorage.setItem(storageKey, 'true');
    onComplete?.();
    onClose();
    setCurrentStep(0);
  };

  const handleSkip = () => {
    localStorage.setItem(storageKey, 'skipped');
    onClose();
    setCurrentStep(0);
  };

  if (!isOpen) return null;

  return (
    <div className="fixed inset-0 z-50">
      {/* 遮罩层 */}
      <div className="absolute inset-0 bg-black/50 backdrop-blur-sm" onClick={handleSkip} />
      
      {/* 高亮区域 */}
      {showSpotlight && targetRect && (
        <div
          className="absolute rounded-lg ring-4 ring-blue-500 ring-offset-4 transition-all duration-300"
          style={{
            top: targetRect.top - 8,
            left: targetRect.left - 8,
            width: targetRect.width + 16,
            height: targetRect.height + 16,
          }}
        />
      )}
      
      {/* 引导卡片 */}
      <div
        className={cn(
          'absolute bg-white dark:bg-slate-800 rounded-2xl shadow-2xl p-6 max-w-sm transition-all duration-300',
          showSpotlight && targetRect
            ? getTooltipPosition(targetRect, currentStepData?.placement || 'bottom')
            : 'top-1/2 left-1/2 -translate-x-1/2 -translate-y-1/2'
        )}
      >
        {/* 关闭按钮 */}
        <button
          onClick={handleSkip}
          className="absolute top-4 right-4 p-1 text-gray-400 hover:text-gray-600 dark:hover:text-gray-200 transition-colors"
        >
          <X className="w-5 h-5" />
        </button>
        
        {/* 步骤指示器 */}
        <div className="flex items-center gap-1 mb-6">
          {steps.map((_, index) => (
            <div
              key={index}
              className={cn(
                'h-1.5 rounded-full transition-all duration-300',
                index === currentStep 
                  ? 'w-8 bg-blue-600' 
                  : index < currentStep 
                    ? 'w-4 bg-blue-300' 
                    : 'w-4 bg-gray-200 dark:bg-slate-700'
              )}
            />
          ))}
        </div>
        
        {/* 图标 */}
        {currentStepData.icon && (
          <div className="w-14 h-14 bg-blue-100 dark:bg-blue-900/30 rounded-xl flex items-center justify-center mb-4">
            {React.cloneElement(currentStepData.icon as React.ReactElement, {
              className: 'w-7 h-7 text-blue-600 dark:text-blue-400',
            })}
          </div>
        )}
        
        {/* 内容 */}
        <h3 className="text-xl font-bold text-gray-900 dark:text-white mb-2">
          {currentStepData.title}
        </h3>
        <p className="text-gray-600 dark:text-gray-400 mb-6">
          {currentStepData.description}
        </p>
        
        {/* 按钮 */}
        <div className="flex items-center justify-between">
          <button
            onClick={handleSkip}
            className="text-sm text-gray-500 hover:text-gray-700 dark:hover:text-gray-300 transition-colors"
          >
            跳过导览
          </button>
          
          <div className="flex items-center gap-2">
            {!isFirstStep && (
              <button
                onClick={handlePrev}
                className="p-2 text-gray-600 hover:bg-gray-100 dark:hover:bg-slate-700 rounded-lg transition-colors"
              >
                <ChevronLeft className="w-5 h-5" />
              </button>
            )}
            
            <button
              onClick={handleNext}
              className="flex items-center gap-2 px-4 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors"
            >
              {isLastStep ? (
                <>
                  开始使用
                  <CheckCircle2 className="w-4 h-4" />
                </>
              ) : (
                <>
                  下一步
                  <ChevronRight className="w-4 h-4" />
                </>
              )}
            </button>
          </div>
        </div>
      </div>
    </div>
  );
};

// 计算提示框位置
function getTooltipPosition(
  targetRect: DOMRect,
  placement: 'top' | 'bottom' | 'left' | 'right'
): React.CSSProperties {
  const tooltipWidth = 384; // max-w-sm
  const tooltipHeight = 300; // 估算高度
  const gap = 16;

  switch (placement) {
    case 'top':
      return {
        top: targetRect.top - tooltipHeight - gap,
        left: targetRect.left + targetRect.width / 2 - tooltipWidth / 2,
      };
    case 'bottom':
      return {
        top: targetRect.bottom + gap,
        left: targetRect.left + targetRect.width / 2 - tooltipWidth / 2,
      };
    case 'left':
      return {
        top: targetRect.top + targetRect.height / 2 - tooltipHeight / 2,
        left: targetRect.left - tooltipWidth - gap,
      };
    case 'right':
      return {
        top: targetRect.top + targetRect.height / 2 - tooltipHeight / 2,
        left: targetRect.right + gap,
      };
    default:
      return {};
  }
}

/**
 * 首页功能介绍卡片
 */
export const FeatureIntro: React.FC = () => {
  const [isVisible, setIsVisible] = useState(true);

  if (!isVisible) return null;

  return (
    <div className="bg-gradient-to-r from-blue-600 to-indigo-700 rounded-2xl p-6 mb-8 text-white">
      <div className="flex items-start justify-between mb-4">
        <div className="flex items-center gap-3">
          <div className="w-12 h-12 bg-white/20 rounded-xl flex items-center justify-center">
            <Sparkles className="w-6 h-6" />
          </div>
          <div>
            <h2 className="text-xl font-bold">欢迎使用 FormalMath</h2>
            <p className="text-blue-200">探索数学知识的新方式</p>
          </div>
        </div>
        <button
          onClick={() => setIsVisible(false)}
          className="p-1 text-white/60 hover:text-white transition-colors"
        >
          <X className="w-5 h-5" />
        </button>
      </div>
      
      <div className="grid grid-cols-1 sm:grid-cols-3 gap-4">
        {[
          { icon: <Network className="w-5 h-5" />, text: '知识图谱可视化' },
          { icon: <GitBranch className="w-5 h-5" />, text: '推理树探索' },
          { icon: <BookOpen className="w-5 h-5" />, text: '交互式学习' },
        ].map((item, index) => (
          <div
            key={index}
            className="flex items-center gap-3 p-3 bg-white/10 rounded-xl"
          >
            {item.icon}
            <span className="font-medium">{item.text}</span>
          </div>
        ))}
      </div>
    </div>
  );
};

/**
 * 快捷操作提示
 */
interface QuickTipProps {
  title: string;
  description: string;
  onDismiss: () => void;
}

export const QuickTip: React.FC<QuickTipProps> = ({
  title,
  description,
  onDismiss,
}) => {
  const [isVisible, setIsVisible] = useState(true);

  if (!isVisible) return null;

  return (
    <div className="fixed bottom-4 right-4 z-40 max-w-sm">
      <div className="bg-white dark:bg-slate-800 rounded-xl shadow-lg border border-gray-200 dark:border-slate-700 p-4 animate-in slide-in-from-bottom-2">
        <div className="flex items-start gap-3">
          <div className="w-10 h-10 bg-yellow-100 dark:bg-yellow-900/30 rounded-lg flex items-center justify-center flex-shrink-0">
            <Target className="w-5 h-5 text-yellow-600 dark:text-yellow-400" />
          </div>
          <div className="flex-1">
            <h4 className="font-semibold text-gray-900 dark:text-white mb-1">
              {title}
            </h4>
            <p className="text-sm text-gray-600 dark:text-gray-400">
              {description}
            </p>
          </div>
          <button
            onClick={() => {
              setIsVisible(false);
              onDismiss();
            }}
            className="p-1 text-gray-400 hover:text-gray-600 transition-colors"
          >
            <X className="w-4 h-4" />
          </button>
        </div>
      </div>
    </div>
  );
};

export default TourGuide;
