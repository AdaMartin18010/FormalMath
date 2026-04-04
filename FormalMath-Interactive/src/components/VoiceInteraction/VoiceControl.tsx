import React, { useState, useEffect, useCallback, useRef } from 'react';
import { Mic, Square, Play, Pause, SkipBack, SkipForward } from 'lucide-react';

interface VoiceControlProps {
  onTranscript: (text: string) => void;
  placeholder?: string;
  buttonSize?: 'sm' | 'md' | 'lg';
  showWaveform?: boolean;
  className?: string;
}

interface AudioLevel {
  level: number;
  timestamp: number;
}

export const VoiceControl: React.FC<VoiceControlProps> = ({
  onTranscript,
  placeholder = '点击麦克风开始语音输入...',
  buttonSize = 'md',
  showWaveform = true,
  className = '',
}) => {
  const [isRecording, setIsRecording] = useState(false);
  const [audioLevels, setAudioLevels] = useState<AudioLevel[]>([]);
  const [recordingTime, setRecordingTime] = useState(0);
  const [error, setError] = useState<string | null>(null);
  
  const recognitionRef = useRef<SpeechRecognition | null>(null);
  const audioContextRef = useRef<AudioContext | null>(null);
  const analyserRef = useRef<AnalyserNode | null>(null);
  const streamRef = useRef<MediaStream | null>(null);
  const timerRef = useRef<NodeJS.Timeout | null>(null);
  const animationFrameRef = useRef<number | null>(null);

  const sizeClasses = {
    sm: 'w-10 h-10',
    md: 'w-14 h-14',
    lg: 'w-20 h-20',
  };

  const iconSizes = {
    sm: 16,
    md: 24,
    lg: 32,
  };

  // 初始化语音识别
  useEffect(() => {
    if ('webkitSpeechRecognition' in window || 'SpeechRecognition' in window) {
      const SpeechRecognition = window.SpeechRecognition || window.webkitSpeechRecognition;
      recognitionRef.current = new SpeechRecognition();
      
      if (recognitionRef.current) {
        recognitionRef.current.lang = 'zh-CN';
        recognitionRef.current.continuous = false;
        recognitionRef.current.interimResults = true;

        recognitionRef.current.onresult = (event) => {
          const transcript = event.results[0][0].transcript;
          if (event.results[0].isFinal) {
            onTranscript(transcript);
            stopRecording();
          }
        };

        recognitionRef.current.onerror = (event) => {
          setError(`识别错误: ${event.error}`);
          stopRecording();
        };

        recognitionRef.current.onend = () => {
          setIsRecording(false);
        };
      }
    }

    return () => {
      stopRecording();
    };
  }, [onTranscript]);

  // 开始录音
  const startRecording = async () => {
    try {
      setError(null);
      
      // 请求麦克风权限
      streamRef.current = await navigator.mediaDevices.getUserMedia({ audio: true });
      
      // 设置音频分析
      audioContextRef.current = new AudioContext();
      analyserRef.current = audioContextRef.current.createAnalyser();
      const source = audioContextRef.current.createMediaStreamSource(streamRef.current);
      source.connect(analyserRef.current);
      analyserRef.current.fftSize = 256;

      // 开始语音识别
      recognitionRef.current?.start();
      setIsRecording(true);
      setRecordingTime(0);

      // 开始计时
      timerRef.current = setInterval(() => {
        setRecordingTime(prev => prev + 1);
      }, 1000);

      // 开始可视化
      if (showWaveform) {
        visualizeAudio();
      }
    } catch (err) {
      setError('无法访问麦克风，请检查权限设置');
    }
  };

  // 停止录音
  const stopRecording = useCallback(() => {
    recognitionRef.current?.stop();
    
    if (timerRef.current) {
      clearInterval(timerRef.current);
      timerRef.current = null;
    }

    if (animationFrameRef.current) {
      cancelAnimationFrame(animationFrameRef.current);
      animationFrameRef.current = null;
    }

    if (streamRef.current) {
      streamRef.current.getTracks().forEach(track => track.stop());
      streamRef.current = null;
    }

    if (audioContextRef.current) {
      audioContextRef.current.close();
      audioContextRef.current = null;
    }

    setIsRecording(false);
    setAudioLevels([]);
    setRecordingTime(0);
  }, []);

  // 音频可视化
  const visualizeAudio = () => {
    if (!analyserRef.current) return;

    const bufferLength = analyserRef.current.frequencyBinCount;
    const dataArray = new Uint8Array(bufferLength);

    const draw = () => {
      if (!isRecording) return;
      
      animationFrameRef.current = requestAnimationFrame(draw);
      analyserRef.current!.getByteFrequencyData(dataArray);

      // 计算平均音量
      const average = dataArray.reduce((a, b) => a + b) / bufferLength;
      const normalizedLevel = average / 255;

      setAudioLevels(prev => {
        const newLevels = [...prev, { level: normalizedLevel, timestamp: Date.now() }];
        // 只保留最近100个样本
        return newLevels.slice(-100);
      });
    };

    draw();
  };

  // 格式化时间
  const formatTime = (seconds: number): string => {
    const mins = Math.floor(seconds / 60);
    const secs = seconds % 60;
    return `${mins.toString().padStart(2, '0')}:${secs.toString().padStart(2, '0')}`;
  };

  return (
    <div className={`${className}`}>
      {/* 录音按钮 */}
      <div className="flex items-center gap-4">
        <button
          onClick={isRecording ? stopRecording : startRecording}
          className={`
            ${sizeClasses[buttonSize]} rounded-full flex items-center justify-center
            transition-all duration-300 transform
            ${isRecording 
              ? 'bg-red-500 hover:bg-red-600 animate-pulse' 
              : 'bg-blue-500 hover:bg-blue-600 hover:scale-110'
            }
            shadow-lg
          `}
        >
          {isRecording ? (
            <Square size={iconSizes[buttonSize]} className="text-white" />
          ) : (
            <Mic size={iconSizes[buttonSize]} className="text-white" />
          )}
        </button>

        {isRecording && (
          <div className="flex-1">
            <div className="flex items-center gap-2 mb-2">
              <span className="text-red-500 animate-pulse">●</span>
              <span className="text-sm text-gray-600">{placeholder}</span>
            </div>
            <span className="text-2xl font-mono text-gray-800">
              {formatTime(recordingTime)}
            </span>
          </div>
        )}
      </div>

      {/* 波形可视化 */}
      {isRecording && showWaveform && (
        <div className="mt-4 h-16 bg-gray-100 rounded-lg overflow-hidden">
          <div className="flex items-end justify-center h-full gap-1 px-4">
            {audioLevels.map((level, index) => (
              <div
                key={index}
                className="w-1 bg-blue-500 rounded-t transition-all duration-75"
                style={{
                  height: `${Math.max(level.level * 100, 4)}%`,
                  opacity: index / audioLevels.length,
                }}
              />
            ))}
          </div>
        </div>
      )}

      {/* 错误提示 */}
      {error && (
        <div className="mt-3 p-3 bg-red-50 text-red-600 text-sm rounded-lg">
          {error}
        </div>
      )}
    </div>
  );
};

// 语音播放器组件
interface VoicePlayerProps {
  text: string;
  autoPlay?: boolean;
  onComplete?: () => void;
  className?: string;
}

export const VoicePlayer: React.FC<VoicePlayerProps> = ({
  text,
  autoPlay = false,
  onComplete,
  className = '',
}) => {
  const [isPlaying, setIsPlaying] = useState(false);
  const [isPaused, setIsPaused] = useState(false);
  const [progress, setProgress] = useState(0);
  const synthesisRef = useRef<SpeechSynthesis | null>(null);
  const utteranceRef = useRef<SpeechSynthesisUtterance | null>(null);

  useEffect(() => {
    synthesisRef.current = window.speechSynthesis;
    
    if (autoPlay) {
      play();
    }

    return () => {
      synthesisRef.current?.cancel();
    };
  }, [text]);

  const play = () => {
    if (!synthesisRef.current) return;

    synthesisRef.current.cancel();

    utteranceRef.current = new SpeechSynthesisUtterance(text);
    utteranceRef.current.lang = 'zh-CN';
    utteranceRef.current.rate = 1;
    utteranceRef.current.pitch = 1;

    utteranceRef.current.onstart = () => {
      setIsPlaying(true);
      setIsPaused(false);
    };

    utteranceRef.current.onend = () => {
      setIsPlaying(false);
      setProgress(100);
      onComplete?.();
    };

    utteranceRef.current.onpause = () => {
      setIsPaused(true);
    };

    utteranceRef.current.onresume = () => {
      setIsPaused(false);
    };

    utteranceRef.current.onboundary = (event) => {
      const percent = (event.charIndex / text.length) * 100;
      setProgress(percent);
    };

    synthesisRef.current.speak(utteranceRef.current);
  };

  const pause = () => {
    synthesisRef.current?.pause();
  };

  const resume = () => {
    synthesisRef.current?.resume();
  };

  const stop = () => {
    synthesisRef.current?.cancel();
    setIsPlaying(false);
    setProgress(0);
  };

  return (
    <div className={`bg-white rounded-lg shadow p-4 ${className}`}>
      {/* 进度条 */}
      <div className="w-full h-2 bg-gray-200 rounded-full mb-4 overflow-hidden">
        <div
          className="h-full bg-blue-500 transition-all duration-300"
          style={{ width: `${progress}%` }}
        />
      </div>

      {/* 控制按钮 */}
      <div className="flex items-center justify-center gap-4">
        <button
          onClick={stop}
          className="p-2 text-gray-500 hover:text-gray-700 rounded-full hover:bg-gray-100"
        >
          <SkipBack size={20} />
        </button>

        {isPlaying && !isPaused ? (
          <button
            onClick={pause}
            className="w-12 h-12 bg-blue-500 hover:bg-blue-600 rounded-full flex items-center justify-center text-white"
          >
            <Pause size={24} />
          </button>
        ) : (
          <button
            onClick={isPaused ? resume : play}
            className="w-12 h-12 bg-blue-500 hover:bg-blue-600 rounded-full flex items-center justify-center text-white"
          >
            <Play size={24} />
          </button>
        )}

        <button
          onClick={stop}
          className="p-2 text-gray-500 hover:text-gray-700 rounded-full hover:bg-gray-100"
        >
          <SkipForward size={20} />
        </button>
      </div>
    </div>
  );
};

export default VoiceControl;
