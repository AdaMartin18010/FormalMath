// @ts-nocheck
import React, { useState, useCallback, useEffect, useRef } from 'react';
import { Volume2, VolumeX, Settings, ChevronDown, ChevronUp } from 'lucide-react';

// 数学符号到可读文本的映射
const mathSymbolMap: Record<string, string> = {
  // 基本运算符
  '+': '加',
  '-': '减',
  '*': '乘',
  '/': '除以',
  '=': '等于',
  '≠': '不等于',
  '≈': '约等于',
  '<': '小于',
  '>': '大于',
  '≤': '小于等于',
  '≥': '大于等于',
  
  // 希腊字母
  'α': '阿尔法',
  'β': '贝塔',
  'γ': '伽马',
  'δ': '德尔塔',
  'ε': '艾普西隆',
  'θ': '西塔',
  'λ': '拉姆达',
  'μ': '缪',
  'π': '派',
  'σ': '西格玛',
  'φ': '斐',
  'ω': '欧米伽',
  
  // 数学符号
  '∑': '求和',
  '∏': '求积',
  '∫': '积分',
  '∂': '偏导',
  '√': '根号',
  '∞': '无穷大',
  '∈': '属于',
  '∉': '不属于',
  '⊂': '包含于',
  '⊃': '包含',
  '∪': '并集',
  '∩': '交集',
  '∀': '对于所有',
  '∃': '存在',
  '∧': '且',
  '∨': '或',
  '¬': '非',
  '→': '推出',
  '⇒': '蕴含',
  '⇔': '当且仅当',
  
  // 上标/下标
  '^2': '的平方',
  '^3': '的立方',
  '^n': '的n次方',
  '_': '下标',
  
  // 括号
  '(': '左括号',
  ')': '右括号',
  '[': '左方括号',
  ']': '右方括号',
  '{': '左花括号',
  '}': '右花括号',
  
  // 分数
  '\frac': '分数',
  '/': '分之',
  
  // 其他
  'lim': '极限',
  'sin': '正弦',
  'cos': '余弦',
  'tan': '正切',
  'log': '对数',
  'ln': '自然对数',
  'exp': '指数',
  'max': '最大值',
  'min': '最小值',
  'sup': '上确界',
  'inf': '下确界',
};

interface MathVoiceReaderProps {
  content: string;
  title?: string;
  autoRead?: boolean;
  showControls?: boolean;
  className?: string;
  onProgress?: (progress: number) => void;
}

interface ReaderSettings {
  rate: number;
  pitch: number;
  volume: number;
  readMathSymbols: boolean;
  highlightCurrent: boolean;
  splitParagraphs: boolean;
}

export const MathVoiceReader: React.FC<MathVoiceReaderProps> = ({
  content,
  title,
  autoRead = false,
  showControls = true,
  className = '',
  onProgress,
}) => {
  const [isPlaying, setIsPlaying] = useState(false);
  const [currentIndex, setCurrentIndex] = useState(0);
  const [showSettings, setShowSettings] = useState(false);
  const [settings, setSettings] = useState<ReaderSettings>({
    rate: 1,
    pitch: 1,
    volume: 1,
    readMathSymbols: true,
    highlightCurrent: true,
    splitParagraphs: true,
  });

  const synthesisRef = useRef<SpeechSynthesis | null>(null);
  const utteranceQueueRef = useRef<SpeechSynthesisUtterance[]>([]);
  const currentUtteranceRef = useRef<SpeechSynthesisUtterance | null>(null);
  const sentencesRef = useRef<string[]>([]);

  // 解析内容，将数学表达式转换为可朗读的文本
  const parseContent = useCallback((text: string): string[] => {
    let processedText = text;

    if (settings.readMathSymbols) {
      // 转换 LaTeX 数学表达式
      processedText = processedText
        // 行间公式 $$...$$
        .replace(/\$\$([^$]+)\$\$/g, (_, math) => convertLatexToReadable(math))
        // 行内公式 $...$
        .replace(/\$([^$]+)\$/g, (_, math) => convertLatexToReadable(math))
        // \( ... \)
        .replace(/\\\(([^)]+)\\\)/g, (_, math) => convertLatexToReadable(math))
        // \[ ... \]
        .replace(/\\\[([^\]]+)\\\]/g, (_, math) => convertLatexToReadable(math));
      
      // 转换常见数学符号
      Object.entries(mathSymbolMap).forEach(([symbol, readable]) => {
        processedText = processedText.split(symbol).join(` ${readable} `);
      });
    }

    // 分割成句子
    if (settings.splitParagraphs) {
      return processedText
        .split(/[。！？.!?]\s+/)
        .map(s => s.trim())
        .filter(s => s.length > 0);
    }

    return [processedText];
  }, [settings.readMathSymbols, settings.splitParagraphs]);

  // 将 LaTeX 转换为可朗读文本
  const convertLatexToReadable = (latex: string): string => {
    const readable = latex
      // 分数
      .replace(/\\frac\{([^}]+)\}\{([^}]+)\}/g, '$1 分之 $2')
      // 上标
      .replace(/\^\{([^}]+)\}/g, '的 $1 次方')
      .replace(/\^([0-9a-zA-Z])/g, '的 $1 次方')
      // 下标
      .replace(/_\{([^}]+)\}/g, '下标 $1')
      .replace(/_([0-9a-zA-Z])/g, '下标 $1')
      // 根号
      .replace(/\\sqrt\{([^}]+)\}/g, '根号 $1')
      .replace(/\\sqrt\[([^\]]+)\]\{([^}]+)\}/g, '$1 次根号 $2')
      // 求和、积分等
      .replace(/\\sum_/g, '求和')
      .replace(/\\int_/g, '积分')
      .replace(/\\prod_/g, '求积')
      // 极限
      .replace(/\\lim_/g, '极限')
      // 函数
      .replace(/\\sin/g, '正弦')
      .replace(/\\cos/g, '余弦')
      .replace(/\\tan/g, '正切')
      .replace(/\\log/g, '对数')
      .replace(/\\ln/g, '自然对数')
      // 希腊字母
      .replace(/\\alpha/g, '阿尔法')
      .replace(/\\beta/g, '贝塔')
      .replace(/\\gamma/g, '伽马')
      .replace(/\\delta/g, '德尔塔')
      .replace(/\\epsilon|\\varepsilon/g, '艾普西隆')
      .replace(/\\theta|\\vartheta/g, '西塔')
      .replace(/\\lambda/g, '拉姆达')
      .replace(/\\mu/g, '缪')
      .replace(/\\pi/g, '派')
      .replace(/\\sigma/g, '西格玛')
      .replace(/\\phi|\\varphi/g, '斐')
      .replace(/\\omega/g, '欧米伽')
      // 无穷
      .replace(/\\infty/g, '无穷大')
      // 箭头
      .replace(/\\to|\\rightarrow/g, '趋向于')
      .replace(/\\Rightarrow/g, '推出')
      .replace(/\\Leftrightarrow/g, '当且仅当')
      // 约等于
      .replace(/\\approx/g, '约等于')
      // 不等于
      .replace(/\\neq|\\ne/g, '不等于')
      // 小于等于、大于等于
      .replace(/\\leq|\\le/g, '小于等于')
      .replace(/\\geq|\\ge/g, '大于等于')
      // 花括号
      .replace(/\\\{/g, '左花括号')
      .replace(/\\\}/g, '右花括号')
      // 移除剩余的LaTeX命令
      .replace(/\\[a-zA-Z]+/g, '')
      // 清理多余的花括号
      .replace(/[{}]/g, '');

    return readable;
  };

  // 初始化
  useEffect(() => {
    synthesisRef.current = window.speechSynthesis;
    sentencesRef.current = parseContent(content);

    return () => {
      synthesisRef.current?.cancel();
    };
  }, [content, parseContent]);

  // 自动播放
  useEffect(() => {
    if (autoRead) {
      startReading();
    }
  }, [autoRead]);

  const startReading = () => {
    if (!synthesisRef.current || sentencesRef.current.length === 0) return;

    synthesisRef.current.cancel();
    utteranceQueueRef.current = [];

    // 创建所有 utterance
    sentencesRef.current.forEach((sentence, index) => {
      const utterance = new SpeechSynthesisUtterance(sentence);
      utterance.lang = 'zh-CN';
      utterance.rate = settings.rate;
      utterance.pitch = settings.pitch;
      utterance.volume = settings.volume;

      utterance.onstart = () => {
        setCurrentIndex(index);
      };

      utterance.onend = () => {
        if (index === sentencesRef.current.length - 1) {
          setIsPlaying(false);
          setCurrentIndex(0);
        }
      };

      utterance.onboundary = () => {
        const progress = ((index + 1) / sentencesRef.current.length) * 100;
        onProgress?.(progress);
      };

      utteranceQueueRef.current.push(utterance);
    });

    // 开始播放
    playNext(0);
    setIsPlaying(true);
  };

  const playNext = (index: number) => {
    if (index >= utteranceQueueRef.current.length) {
      setIsPlaying(false);
      return;
    }

    currentUtteranceRef.current = utteranceQueueRef.current[index];
    synthesisRef.current?.speak(currentUtteranceRef.current);
  };

  const pauseReading = () => {
    synthesisRef.current?.pause();
    setIsPlaying(false);
  };

  const resumeReading = () => {
    synthesisRef.current?.resume();
    setIsPlaying(true);
  };

  const stopReading = () => {
    synthesisRef.current?.cancel();
    setIsPlaying(false);
    setCurrentIndex(0);
  };

  // 渲染带高亮的文本
  const renderHighlightedText = () => {
    if (!settings.highlightCurrent) {
      return <div className="prose max-w-none">{content}</div>;
    }

    return (
      <div className="prose max-w-none">
        {sentencesRef.current.map((sentence, index) => (
          <span
            key={index}
            className={`transition-colors duration-300 ${
              index === currentIndex
                ? 'bg-yellow-200 px-1 rounded'
                : ''
            }`}
          >
            {sentence}
            {index < sentencesRef.current.length - 1 && '。'}
          </span>
        ))}
      </div>
    );
  };

  return (
    <div className={`bg-white rounded-lg shadow ${className}`}>
      {/* 标题栏 */}
      {(title || showControls) && (
        <div className="flex items-center justify-between p-4 border-b border-gray-200">
          {title && <h3 className="font-semibold text-gray-800">{title}</h3>}
          
          {showControls && (
            <div className="flex items-center gap-2">
              <button
                onClick={() => setShowSettings(!showSettings)}
                className="p-2 text-gray-500 hover:text-gray-700 rounded-lg hover:bg-gray-100"
              >
                <Settings size={20} />
              </button>
              
              {isPlaying ? (
                <button
                  onClick={pauseReading}
                  className="p-2 text-blue-500 hover:text-blue-600 rounded-lg hover:bg-blue-50"
                >
                  <Volume2 size={20} />
                </button>
              ) : (
                <button
                  onClick={currentIndex > 0 ? resumeReading : startReading}
                  className="p-2 text-gray-500 hover:text-gray-700 rounded-lg hover:bg-gray-100"
                >
                  <VolumeX size={20} />
                </button>
              )}
              
              {isPlaying && (
                <button
                  onClick={stopReading}
                  className="p-2 text-red-500 hover:text-red-600 rounded-lg hover:bg-red-50"
                >
                  停止
                </button>
              )}
            </div>
          )}
        </div>
      )}

      {/* 设置面板 */}
      {showSettings && (
        <div className="p-4 bg-gray-50 border-b border-gray-200">
          <div className="space-y-4">
            <div>
              <label className="block text-sm text-gray-600 mb-1">
                语速: {settings.rate.toFixed(1)}x
              </label>
              <input
                type="range"
                min="0.5"
                max="2"
                step="0.1"
                value={settings.rate}
                onChange={(e) => setSettings(prev => ({ 
                  ...prev, 
                  rate: parseFloat(e.target.value) 
                }))}
                className="w-full"
              />
            </div>

            <div>
              <label className="block text-sm text-gray-600 mb-1">
                音调: {settings.pitch.toFixed(1)}
              </label>
              <input
                type="range"
                min="0.5"
                max="2"
                step="0.1"
                value={settings.pitch}
                onChange={(e) => setSettings(prev => ({ 
                  ...prev, 
                  pitch: parseFloat(e.target.value) 
                }))}
                className="w-full"
              />
            </div>

            <div>
              <label className="block text-sm text-gray-600 mb-1">
                音量: {Math.round(settings.volume * 100)}%
              </label>
              <input
                type="range"
                min="0"
                max="1"
                step="0.1"
                value={settings.volume}
                onChange={(e) => setSettings(prev => ({ 
                  ...prev, 
                  volume: parseFloat(e.target.value) 
                }))}
                className="w-full"
              />
            </div>

            <div className="flex items-center gap-4">
              <label className="flex items-center gap-2 cursor-pointer">
                <input
                  type="checkbox"
                  checked={settings.readMathSymbols}
                  onChange={(e) => setSettings(prev => ({ 
                    ...prev, 
                    readMathSymbols: e.target.checked 
                  }))}
                  className="rounded"
                />
                <span className="text-sm text-gray-600">朗读数学符号</span>
              </label>

              <label className="flex items-center gap-2 cursor-pointer">
                <input
                  type="checkbox"
                  checked={settings.highlightCurrent}
                  onChange={(e) => setSettings(prev => ({ 
                    ...prev, 
                    highlightCurrent: e.target.checked 
                  }))}
                  className="rounded"
                />
                <span className="text-sm text-gray-600">高亮当前句</span>
              </label>
            </div>
          </div>
        </div>
      )}

      {/* 内容区 */}
      <div className="p-4">
        {renderHighlightedText()}
      </div>

      {/* 进度条 */}
      {isPlaying && (
        <div className="px-4 pb-4">
          <div className="w-full h-1 bg-gray-200 rounded-full overflow-hidden">
            <div
              className="h-full bg-blue-500 transition-all duration-300"
              style={{ 
                width: `${((currentIndex + 1) / sentencesRef.current.length) * 100}%` 
              }}
            />
          </div>
          <div className="mt-2 text-sm text-gray-500 text-center">
            {currentIndex + 1} / {sentencesRef.current.length}
          </div>
        </div>
      )}
    </div>
  );
};

export default MathVoiceReader;
