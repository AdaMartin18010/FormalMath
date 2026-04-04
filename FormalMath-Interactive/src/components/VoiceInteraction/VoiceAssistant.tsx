import React, { useState, useCallback, useRef, useEffect } from 'react';
import { Mic, MicOff, Volume2, Settings } from 'lucide-react';

// 语音命令类型
interface VoiceCommand {
  pattern: RegExp;
  action: (params: string[]) => void;
  description: string;
}

// 语音交互状态
interface VoiceState {
  isListening: boolean;
  isSpeaking: boolean;
  transcript: string;
  interimTranscript: string;
  error: string | null;
  language: string;
}

interface VoiceAssistantProps {
  onCommand?: (command: string, params: string[]) => void;
  onTranscript?: (transcript: string) => void;
  onError?: (error: string) => void;
  commands?: VoiceCommand[];
  language?: string;
  continuous?: boolean;
  interimResults?: boolean;
  className?: string;
}

// Web Speech API 类型声明
declare global {
  interface Window {
    SpeechRecognition: new () => SpeechRecognition;
    webkitSpeechRecognition: new () => SpeechRecognition;
  }
}

interface SpeechRecognition extends EventTarget {
  lang: string;
  continuous: boolean;
  interimResults: boolean;
  maxAlternatives: number;
  start(): void;
  stop(): void;
  abort(): void;
  onresult: (event: SpeechRecognitionEvent) => void;
  onerror: (event: SpeechRecognitionErrorEvent) => void;
  onend: () => void;
  onstart: () => void;
}

interface SpeechRecognitionEvent {
  results: SpeechRecognitionResultList;
  resultIndex: number;
}

interface SpeechRecognitionResultList {
  length: number;
  item(index: number): SpeechRecognitionResult;
  [index: number]: SpeechRecognitionResult;
}

interface SpeechRecognitionResult {
  isFinal: boolean;
  length: number;
  item(index: number): SpeechRecognitionAlternative;
  [index: number]: SpeechRecognitionAlternative;
}

interface SpeechRecognitionAlternative {
  transcript: string;
  confidence: number;
}

interface SpeechRecognitionErrorEvent {
  error: string;
  message: string;
}

export const VoiceAssistant: React.FC<VoiceAssistantProps> = ({
  onCommand,
  onTranscript,
  onError,
  commands = [],
  language = 'zh-CN',
  continuous = true,
  interimResults = true,
  className = '',
}) => {
  const [state, setState] = useState<VoiceState>({
    isListening: false,
    isSpeaking: false,
    transcript: '',
    interimTranscript: '',
    error: null,
    language,
  });

  const [showSettings, setShowSettings] = useState(false);
  const [voiceSettings, setVoiceSettings] = useState({
    rate: 1,
    pitch: 1,
    volume: 1,
  });

  const recognitionRef = useRef<SpeechRecognition | null>(null);
  const synthesisRef = useRef<SpeechSynthesis | null>(null);

  // 初始化语音识别
  useEffect(() => {
    if ('webkitSpeechRecognition' in window || 'SpeechRecognition' in window) {
      const SpeechRecognition = window.SpeechRecognition || window.webkitSpeechRecognition;
      recognitionRef.current = new SpeechRecognition();
      
      if (recognitionRef.current) {
        recognitionRef.current.lang = language;
        recognitionRef.current.continuous = continuous;
        recognitionRef.current.interimResults = interimResults;

        recognitionRef.current.onstart = () => {
          setState(prev => ({ ...prev, isListening: true, error: null }));
        };

        recognitionRef.current.onresult = (event) => {
          let finalTranscript = '';
          let interimTranscript = '';

          for (let i = event.resultIndex; i < event.results.length; i++) {
            const transcript = event.results[i][0].transcript;
            if (event.results[i].isFinal) {
              finalTranscript += transcript;
            } else {
              interimTranscript += transcript;
            }
          }

          setState(prev => ({
            ...prev,
            transcript: finalTranscript || prev.transcript,
            interimTranscript,
          }));

          if (finalTranscript) {
            onTranscript?.(finalTranscript);
            processVoiceCommand(finalTranscript);
          }
        };

        recognitionRef.current.onerror = (event) => {
          const errorMsg = getErrorMessage(event.error);
          setState(prev => ({ ...prev, error: errorMsg, isListening: false }));
          onError?.(errorMsg);
        };

        recognitionRef.current.onend = () => {
          setState(prev => ({ ...prev, isListening: false }));
        };
      }
    }

    synthesisRef.current = window.speechSynthesis;

    return () => {
      recognitionRef.current?.abort();
      synthesisRef.current?.cancel();
    };
  }, [language, continuous, interimResults]);

  // 处理语音命令
  const processVoiceCommand = useCallback((transcript: string) => {
    for (const command of commands) {
      const match = transcript.match(command.pattern);
      if (match) {
        const params = match.slice(1);
        command.action(params);
        onCommand?.(command.description, params);
        return;
      }
    }
  }, [commands, onCommand]);

  // 开始/停止录音
  const toggleListening = useCallback(() => {
    if (!recognitionRef.current) {
      onError?.('浏览器不支持语音识别');
      return;
    }

    if (state.isListening) {
      recognitionRef.current.stop();
    } else {
      setState(prev => ({ ...prev, transcript: '', interimTranscript: '' }));
      recognitionRef.current.start();
    }
  }, [state.isListening, onError]);

  // 文本转语音
  const speak = useCallback((text: string) => {
    if (!synthesisRef.current) {
      onError?.('浏览器不支持语音合成');
      return;
    }

    synthesisRef.current.cancel();

    const utterance = new SpeechSynthesisUtterance(text);
    utterance.lang = language;
    utterance.rate = voiceSettings.rate;
    utterance.pitch = voiceSettings.pitch;
    utterance.volume = voiceSettings.volume;

    utterance.onstart = () => {
      setState(prev => ({ ...prev, isSpeaking: true }));
    };

    utterance.onend = () => {
      setState(prev => ({ ...prev, isSpeaking: false }));
    };

    utterance.onerror = () => {
      setState(prev => ({ ...prev, isSpeaking: false }));
    };

    synthesisRef.current.speak(utterance);
  }, [language, voiceSettings, onError]);

  // 停止语音
  const stopSpeaking = useCallback(() => {
    synthesisRef.current?.cancel();
    setState(prev => ({ ...prev, isSpeaking: false }));
  }, []);

  // 获取错误信息
  const getErrorMessage = (error: string): string => {
    const errorMessages: Record<string, string> = {
      'no-speech': '未检测到语音，请重试',
      'audio-capture': '无法访问麦克风',
      'not-allowed': '麦克风权限被拒绝',
      'network': '网络错误，请检查连接',
      'aborted': '语音识别已取消',
    };
    return errorMessages[error] || `语音识别错误: ${error}`;
  };

  // 检查浏览器支持
  const isSupported = 'webkitSpeechRecognition' in window || 'SpeechRecognition' in window;

  if (!isSupported) {
    return (
      <div className={`p-4 bg-yellow-50 rounded-lg text-yellow-700 ${className}`}>
        <p className="text-sm">您的浏览器不支持语音识别功能</p>
      </div>
    );
  }

  return (
    <div className={`bg-white rounded-lg shadow-lg overflow-hidden ${className}`}>
      {/* 主控制区 */}
      <div className="p-4">
        <div className="flex items-center justify-between mb-4">
          <h3 className="text-lg font-semibold text-gray-800">语音助手</h3>
          <button
            onClick={() => setShowSettings(!showSettings)}
            className="p-2 text-gray-500 hover:text-gray-700 rounded-lg hover:bg-gray-100 transition-colors"
          >
            <Settings size={20} />
          </button>
        </div>

        {/* 录音按钮 */}
        <div className="flex justify-center mb-4">
          <button
            onClick={toggleListening}
            className={`
              relative w-20 h-20 rounded-full flex items-center justify-center
              transition-all duration-300 transform
              ${state.isListening 
                ? 'bg-red-500 hover:bg-red-600 scale-110 shadow-lg shadow-red-200' 
                : 'bg-blue-500 hover:bg-blue-600 hover:scale-105 shadow-lg shadow-blue-200'
              }
            `}
          >
            {state.isListening ? (
              <>
                <MicOff size={32} className="text-white" />
                {/* 录音动画 */}
                <span className="absolute inset-0 rounded-full animate-ping bg-red-400 opacity-30" />
              </>
            ) : (
              <Mic size={32} className="text-white" />
            )}
          </button>
        </div>

        {/* 状态指示 */}
        <div className="text-center mb-4">
          {state.isListening ? (
            <div className="flex items-center justify-center gap-2 text-green-600">
              <span className="relative flex h-3 w-3">
                <span className="animate-ping absolute inline-flex h-full w-full rounded-full bg-green-400 opacity-75" />
                <span className="relative inline-flex rounded-full h-3 w-3 bg-green-500" />
              </span>
              <span className="text-sm font-medium">正在聆听...</span>
            </div>
          ) : state.isSpeaking ? (
            <div className="flex items-center justify-center gap-2 text-blue-600">
              <Volume2 size={16} />
              <span className="text-sm font-medium">正在播放...</span>
            </div>
          ) : (
            <p className="text-sm text-gray-500">
              点击麦克风开始语音交互
            </p>
          )}
        </div>

        {/* 转录文本显示 */}
        <div className="bg-gray-50 rounded-lg p-3 min-h-[80px]">
          {state.interimTranscript && (
            <p className="text-gray-400 italic">{state.interimTranscript}</p>
          )}
          {state.transcript && (
            <p className="text-gray-800 mt-2">{state.transcript}</p>
          )}
          {!state.interimTranscript && !state.transcript && (
            <p className="text-gray-400 text-center py-4">语音识别内容将显示在这里</p>
          )}
        </div>

        {/* 错误提示 */}
        {state.error && (
          <div className="mt-3 p-3 bg-red-50 rounded-lg flex items-center gap-2 text-red-600">
            <span className="text-sm">{state.error}</span>
          </div>
        )}

        {/* 快速操作 */}
        <div className="mt-4 flex gap-2">
          <button
            onClick={() => speak(state.transcript || '请说些什么')}
            disabled={!state.transcript || state.isSpeaking}
            className="flex-1 py-2 px-4 bg-gray-100 hover:bg-gray-200 disabled:opacity-50 
                       disabled:cursor-not-allowed rounded-lg text-sm font-medium transition-colors
                       flex items-center justify-center gap-2"
          >
            <Volume2 size={16} />
            朗读
          </button>
          <button
            onClick={stopSpeaking}
            disabled={!state.isSpeaking}
            className="flex-1 py-2 px-4 bg-gray-100 hover:bg-gray-200 disabled:opacity-50 
                       disabled:cursor-not-allowed rounded-lg text-sm font-medium transition-colors"
          >
            停止朗读
          </button>
        </div>
      </div>

      {/* 设置面板 */}
      {showSettings && (
        <div className="border-t border-gray-200 p-4 bg-gray-50">
          <h4 className="font-medium text-gray-800 mb-3">语音设置</h4>
          
          <div className="space-y-4">
            <div>
              <label className="block text-sm text-gray-600 mb-1">
                语速: {voiceSettings.rate.toFixed(1)}x
              </label>
              <input
                type="range"
                min="0.5"
                max="2"
                step="0.1"
                value={voiceSettings.rate}
                onChange={(e) => setVoiceSettings(prev => ({ 
                  ...prev, 
                  rate: parseFloat(e.target.value) 
                }))}
                className="w-full"
              />
            </div>

            <div>
              <label className="block text-sm text-gray-600 mb-1">
                音调: {voiceSettings.pitch.toFixed(1)}
              </label>
              <input
                type="range"
                min="0.5"
                max="2"
                step="0.1"
                value={voiceSettings.pitch}
                onChange={(e) => setVoiceSettings(prev => ({ 
                  ...prev, 
                  pitch: parseFloat(e.target.value) 
                }))}
                className="w-full"
              />
            </div>

            <div>
              <label className="block text-sm text-gray-600 mb-1">
                音量: {Math.round(voiceSettings.volume * 100)}%
              </label>
              <input
                type="range"
                min="0"
                max="1"
                step="0.1"
                value={voiceSettings.volume}
                onChange={(e) => setVoiceSettings(prev => ({ 
                  ...prev, 
                  volume: parseFloat(e.target.value) 
                }))}
                className="w-full"
              />
            </div>
          </div>
        </div>
      )}
    </div>
  );
};

// 数学专用语音命令
export const mathVoiceCommands: VoiceCommand[] = [
  {
    pattern: /计算\s*(.+)/i,
    action: (params) => {
      console.log('计算:', params[0]);
    },
    description: '计算表达式',
  },
  {
    pattern: /搜索\s*(.+)/i,
    action: (params) => {
      console.log('搜索:', params[0]);
    },
    description: '搜索内容',
  },
  {
    pattern: /打开\s*(知识图谱|推理树|思维导图|练习)/i,
    action: (params) => {
      console.log('打开页面:', params[0]);
    },
    description: '打开页面',
  },
  {
    pattern: /朗读|读一下/i,
    action: () => {
      console.log('朗读当前内容');
    },
    description: '朗读内容',
  },
  {
    pattern: /停止|暂停/i,
    action: () => {
      console.log('停止朗读');
    },
    description: '停止朗读',
  },
];

export default VoiceAssistant;
