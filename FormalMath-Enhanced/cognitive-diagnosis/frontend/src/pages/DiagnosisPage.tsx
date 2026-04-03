import React, { useState, useEffect, useCallback } from 'react';
import { useNavigate } from 'react-router-dom';
import { startDiagnosis, submitAnswer, StartDiagnosisRequest } from '../api/diagnosis';
import { Question, SubmitAnswerResponse } from '../types';
import QuestionCard from '../components/Diagnosis/QuestionCard';
import ProgressBar from '../components/Diagnosis/ProgressBar';
import AnswerFeedback from '../components/Diagnosis/AnswerFeedback';
import './DiagnosisPage.css';

const DiagnosisPage: React.FC = () => {
  const navigate = useNavigate();
  
  // 状态
  const [sessionId, setSessionId] = useState<string>('');
  const [currentQuestion, setCurrentQuestion] = useState<Question | null>(null);
  const [progress, setProgress] = useState({ current: 0, total: 0, percentage: 0 });
  const [isLoading, setIsLoading] = useState(false);
  const [error, setError] = useState<string>('');
  const [feedback, setFeedback] = useState<{ isCorrect: boolean; score: number } | null>(null);
  const [answerTime, setAnswerTime] = useState<number>(0);
  const [timer, setTimer] = useState<NodeJS.Timeout | null>(null);
  const [isStarted, setIsStarted] = useState(false);

  // 开始诊断
  const handleStartDiagnosis = async (config: { questionCount: number; targetLevels: number[] }) => {
    setIsLoading(true);
    setError('');
    
    try {
      const request: StartDiagnosisRequest = {
        user_id: 'user_demo', // 演示用固定用户
        question_count: config.questionCount,
        target_levels: config.targetLevels
      };
      
      const response = await startDiagnosis(request);
      
      if (response.success) {
        setSessionId(response.data.session_id);
        setCurrentQuestion(response.data.first_question);
        setProgress({
          current: 0,
          total: response.data.question_count,
          percentage: 0
        });
        setIsStarted(true);
        startTimer();
      } else {
        setError(response.message || '启动诊断失败');
      }
    } catch (err: any) {
      setError(err.message || '网络错误，请重试');
    } finally {
      setIsLoading(false);
    }
  };

  // 计时器
  const startTimer = useCallback(() => {
    const startTime = Date.now();
    const interval = setInterval(() => {
      setAnswerTime(Math.floor((Date.now() - startTime) / 1000));
    }, 1000);
    setTimer(interval);
  }, []);

  const stopTimer = useCallback(() => {
    if (timer) {
      clearInterval(timer);
      setTimer(null);
    }
  }, [timer]);

  // 提交答案
  const handleSubmitAnswer = async (answer: any) => {
    if (!currentQuestion || !sessionId) return;
    
    stopTimer();
    setIsLoading(true);
    setError('');
    
    try {
      const response = await submitAnswer({
        session_id: sessionId,
        question_id: currentQuestion.id,
        answer: answer,
        time_spent: answerTime,
        confidence: 0.8 // 默认置信度
      });
      
      if (response.success) {
        const data: SubmitAnswerResponse = response.data;
        
        // 显示反馈
        setFeedback({
          isCorrect: data.is_correct,
          score: data.score
        });
        
        // 更新进度
        setProgress(data.progress);
        
        // 延迟后显示下一题或完成
        setTimeout(() => {
          setFeedback(null);
          
          if (data.completed && data.report_id) {
            // 诊断完成，跳转到报告页
            navigate(`/reports/${data.report_id}`);
          } else if (data.next_question) {
            // 显示下一题
            setCurrentQuestion(data.next_question);
            setAnswerTime(0);
            startTimer();
          }
        }, 1500);
      } else {
        setError(response.message || '提交答案失败');
        startTimer();
      }
    } catch (err: any) {
      setError(err.message || '网络错误，请重试');
      startTimer();
    } finally {
      setIsLoading(false);
    }
  };

  // 清理
  useEffect(() => {
    return () => {
      if (timer) clearInterval(timer);
    };
  }, [timer]);

  // 未开始状态
  if (!isStarted) {
    return (
      <div className="diagnosis-page">
        <div className="diagnosis-intro card">
          <h2>开始认知诊断</h2>
          <p>
            诊断测试将评估您在数学概念四个层次（L0-L3）的掌握程度。
            测试包含约20道题目，预计用时15-30分钟。
          </p>
          <div className="config-section">
            <h4>诊断配置</h4>
            <div className="config-info">
              <p>📋 题目数量: 20道</p>
              <p>⏱️ 预计用时: 15-30分钟</p>
              <p>🎯 覆盖层次: L0-L3</p>
            </div>
          </div>
          <button
            className="btn btn-primary btn-large"
            onClick={() => handleStartDiagnosis({ questionCount: 20, targetLevels: [0, 1, 2, 3] })}
            disabled={isLoading}
          >
            {isLoading ? '启动中...' : '开始诊断'}
          </button>
          {error && <div className="error">{error}</div>}
        </div>
      </div>
    );
  }

  return (
    <div className="diagnosis-page">
      <ProgressBar 
        current={progress.current} 
        total={progress.total} 
        percentage={progress.percentage} 
      />
      
      {error && <div className="error">{error}</div>}
      
      {feedback && (
        <AnswerFeedback 
          isCorrect={feedback.isCorrect} 
          score={feedback.score} 
        />
      )}
      
      {currentQuestion && !feedback && (
        <QuestionCard
          question={currentQuestion}
          questionNumber={progress.current + 1}
          totalQuestions={progress.total}
          timeSpent={answerTime}
          onSubmit={handleSubmitAnswer}
          disabled={isLoading}
        />
      )}
      
      {isLoading && !feedback && <div className="loading">加载中...</div>}
    </div>
  );
};

export default DiagnosisPage;
