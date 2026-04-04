import { useState, useCallback, useRef, useEffect } from 'react';

// 语音合成 Hook
export const useSpeechSynthesis = () => {
  const [isSpeaking, setIsSpeaking] = useState(false);
  const [isPaused, setIsPaused] = useState(false);
  const [voices, setVoices] = useState<SpeechSynthesisVoice[]>([]);
  const synthesisRef = useRef<SpeechSynthesis | null>(null);

  useEffect(() => {
    synthesisRef.current = window.speechSynthesis;
    
    // 加载可用语音
    const loadVoices = () => {
      const availableVoices = window.speechSynthesis.getVoices();
      setVoices(availableVoices);
    };
    
    loadVoices();
    window.speechSynthesis.onvoiceschanged = loadVoices;

    return () => {
      synthesisRef.current?.cancel();
    };
  }, []);

  const speak = useCallback((
    text: string,
    options?: {
      rate?: number;
      pitch?: number;
      volume?: number;
      lang?: string;
      voice?: SpeechSynthesisVoice;
      onStart?: () => void;
      onEnd?: () => void;
      onError?: () => void;
    }
  ) => {
    if (!synthesisRef.current) return;

    synthesisRef.current.cancel();

    const utterance = new SpeechSynthesisUtterance(text);
    utterance.rate = options?.rate ?? 1;
    utterance.pitch = options?.pitch ?? 1;
    utterance.volume = options?.volume ?? 1;
    utterance.lang = options?.lang ?? 'zh-CN';
    
    if (options?.voice) {
      utterance.voice = options.voice;
    }

    utterance.onstart = () => {
      setIsSpeaking(true);
      setIsPaused(false);
      options?.onStart?.();
    };

    utterance.onend = () => {
      setIsSpeaking(false);
      options?.onEnd?.();
    };

    utterance.onerror = () => {
      setIsSpeaking(false);
      options?.onError?.();
    };

    synthesisRef.current.speak(utterance);
  }, []);

  const stop = useCallback(() => {
    synthesisRef.current?.cancel();
    setIsSpeaking(false);
    setIsPaused(false);
  }, []);

  const pause = useCallback(() => {
    synthesisRef.current?.pause();
    setIsPaused(true);
  }, []);

  const resume = useCallback(() => {
    synthesisRef.current?.resume();
    setIsPaused(false);
  }, []);

  return {
    speak,
    stop,
    pause,
    resume,
    isSpeaking,
    isPaused,
    voices,
    isSupported: 'speechSynthesis' in window,
  };
};

// 语音识别 Hook
export const useSpeechRecognition = () => {
  const [isListening, setIsListening] = useState(false);
  const [transcript, setTranscript] = useState('');
  const [interimTranscript, setInterimTranscript] = useState('');
  const [error, setError] = useState<string | null>(null);
  const recognitionRef = useRef<SpeechRecognition | null>(null);

  const startListening = useCallback((options?: {
    continuous?: boolean;
    interimResults?: boolean;
    lang?: string;
    onResult?: (transcript: string) => void;
    onError?: (error: string) => void;
  }) => {
    if (!('webkitSpeechRecognition' in window) && !('SpeechRecognition' in window)) {
      setError('浏览器不支持语音识别');
      return;
    }

    const SpeechRecognition = window.SpeechRecognition || window.webkitSpeechRecognition;
    recognitionRef.current = new SpeechRecognition();

    recognitionRef.current.continuous = options?.continuous ?? true;
    recognitionRef.current.interimResults = options?.interimResults ?? true;
    recognitionRef.current.lang = options?.lang ?? 'zh-CN';

    recognitionRef.current.onstart = () => {
      setIsListening(true);
      setError(null);
    };

    recognitionRef.current.onresult = (event) => {
      let finalTranscript = '';
      let interim = '';

      for (let i = event.resultIndex; i < event.results.length; i++) {
        const transcript = event.results[i][0].transcript;
        if (event.results[i].isFinal) {
          finalTranscript += transcript;
        } else {
          interim += transcript;
        }
      }

      if (finalTranscript) {
        setTranscript(prev => prev + finalTranscript);
        options?.onResult?.(finalTranscript);
      }
      setInterimTranscript(interim);
    };

    recognitionRef.current.onerror = (event) => {
      const errorMessages: Record<string, string> = {
        'no-speech': '未检测到语音',
        'audio-capture': '无法访问麦克风',
        'not-allowed': '麦克风权限被拒绝',
        'network': '网络错误',
        'aborted': '语音识别已取消',
      };
      const errorMsg = errorMessages[event.error] || `语音识别错误: ${event.error}`;
      setError(errorMsg);
      setIsListening(false);
      options?.onError?.(errorMsg);
    };

    recognitionRef.current.onend = () => {
      setIsListening(false);
    };

    recognitionRef.current.start();
  }, []);

  const stopListening = useCallback(() => {
    recognitionRef.current?.stop();
    setIsListening(false);
  }, []);

  const resetTranscript = useCallback(() => {
    setTranscript('');
    setInterimTranscript('');
  }, []);

  return {
    startListening,
    stopListening,
    resetTranscript,
    isListening,
    transcript,
    interimTranscript,
    error,
    isSupported: 'webkitSpeechRecognition' in window || 'SpeechRecognition' in window,
  };
};

// 数学公式朗读 Hook
export const useMathReader = () => {
  const { speak, stop, isSpeaking } = useSpeechSynthesis();

  const convertMathToReadable = useCallback((text: string): string => {
    const conversions: Record<string, string> = {
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
      'α': '阿尔法',
      'β': '贝塔',
      'γ': '伽马',
      'δ': '德尔塔',
      'θ': '西塔',
      'λ': '拉姆达',
      'π': '派',
      'σ': '西格玛',
      'φ': '斐',
      'ω': '欧米伽',
      '∑': '求和',
      '∫': '积分',
      '√': '根号',
      '∞': '无穷大',
      '∈': '属于',
      '→': '趋向于',
      '∧': '且',
      '∨': '或',
      '¬': '非',
    };

    let readable = text;
    Object.entries(conversions).forEach(([symbol, word]) => {
      readable = readable.split(symbol).join(` ${word} `);
    });

    // 处理 LaTeX
    readable = readable
      .replace(/\\frac\{([^}]+)\}\{([^}]+)\}/g, '$1 分之 $2')
      .replace(/\^\{([^}]+)\}/g, '的 $1 次方')
      .replace(/\\sqrt\{([^}]+)\}/g, '根号 $1')
      .replace(/\\sin/g, '正弦')
      .replace(/\\cos/g, '余弦')
      .replace(/\\tan/g, '正切')
      .replace(/\\log/g, '对数')
      .replace(/\\ln/g, '自然对数')
      .replace(/\\lim/g, '极限');

    return readable;
  }, []);

  const readMath = useCallback((text: string, options?: Parameters<typeof speak>[1]) => {
    const readableText = convertMathToReadable(text);
    speak(readableText, options);
  }, [speak, convertMathToReadable]);

  return {
    readMath,
    stop,
    isSpeaking,
    convertMathToReadable,
  };
};

// AR 支持检测 Hook
export const useARSupport = () => {
  const [isSupported, setIsSupported] = useState<boolean | null>(null);
  const [isChecking, setIsChecking] = useState(true);

  useEffect(() => {
    const checkSupport = async () => {
      if (!navigator.xr) {
        setIsSupported(false);
        setIsChecking(false);
        return;
      }

      try {
        const supported = await navigator.xr.isSessionSupported('immersive-ar');
        setIsSupported(supported);
      } catch {
        setIsSupported(false);
      } finally {
        setIsChecking(false);
      }
    };

    checkSupport();
  }, []);

  return { isSupported, isChecking };
};

// 社交分享 Hook
export const useSocialShare = () => {
  const share = useCallback(async (data: {
    title: string;
    text: string;
    url: string;
  }) => {
    if (navigator.share) {
      try {
        await navigator.share(data);
        return { success: true, method: 'native' as const };
      } catch (err) {
        if ((err as Error).name !== 'AbortError') {
          console.error('Share failed:', err);
        }
        return { success: false, error: err };
      }
    }
    return { success: false, error: 'Native sharing not supported' };
  }, []);

  const copyToClipboard = useCallback(async (text: string) => {
    try {
      await navigator.clipboard.writeText(text);
      return { success: true };
    } catch (err) {
      return { success: false, error: err };
    }
  }, []);

  return { share, copyToClipboard };
};

export default useSpeechSynthesis;
