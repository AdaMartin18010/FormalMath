import React, { useState } from 'react';
import { Question, QuestionOption } from '../../types';
import './QuestionCard.css';

interface QuestionCardProps {
  question: Question;
  questionNumber: number;
  totalQuestions: number;
  timeSpent: number;
  onSubmit: (answer: any) => void;
  disabled?: boolean;
}

const QuestionCard: React.FC<QuestionCardProps> = ({
  question,
  questionNumber,
  totalQuestions,
  timeSpent,
  onSubmit,
  disabled = false
}) => {
  const [selectedAnswer, setSelectedAnswer] = useState<any>(null);
  const [textAnswer, setTextAnswer] = useState('');

  const formatTime = (seconds: number): string => {
    const mins = Math.floor(seconds / 60);
    const secs = seconds % 60;
    return `${mins.toString().padStart(2, '0')}:${secs.toString().padStart(2, '0')}`;
  };

  const handleSubmit = () => {
    if (disabled) return;
    
    let answer: any;
    
    switch (question.type) {
      case 'single_choice':
      case 'true_false':
        answer = selectedAnswer;
        break;
      case 'multiple_choice':
        answer = selectedAnswer || [];
        break;
      case 'fill_blank':
      case 'calculation':
      case 'proof':
        answer = textAnswer.trim();
        break;
      default:
        answer = selectedAnswer;
    }
    
    if (answer !== null && answer !== '' && answer !== undefined) {
      onSubmit(answer);
      setSelectedAnswer(null);
      setTextAnswer('');
    }
  };

  const renderQuestionContent = () => {
    switch (question.type) {
      case 'single_choice':
        return (
          <div className="options-list">
            {question.options?.map((option: QuestionOption) => (
              <label 
                key={option.id} 
                className={`option-item ${selectedAnswer === option.id ? 'selected' : ''}`}
              >
                <input
                  type="radio"
                  name={`question-${question.id}`}
                  value={option.id}
                  checked={selectedAnswer === option.id}
                  onChange={() => setSelectedAnswer(option.id)}
                  disabled={disabled}
                />
                <span className="option-label">{option.id}.</span>
                <span className="option-text">{option.text}</span>
              </label>
            ))}
          </div>
        );
      
      case 'true_false':
        return (
          <div className="options-list">
            {[
              { id: true, text: '正确' },
              { id: false, text: '错误' }
            ].map((option) => (
              <label 
                key={String(option.id)} 
                className={`option-item ${selectedAnswer === option.id ? 'selected' : ''}`}
              >
                <input
                  type="radio"
                  name={`question-${question.id}`}
                  value={String(option.id)}
                  checked={selectedAnswer === option.id}
                  onChange={() => setSelectedAnswer(option.id)}
                  disabled={disabled}
                />
                <span className="option-text">{option.text}</span>
              </label>
            ))}
          </div>
        );
      
      case 'fill_blank':
        return (
          <div className="text-answer">
            <input
              type="text"
              className="text-input"
              placeholder="请输入答案"
              value={textAnswer}
              onChange={(e) => setTextAnswer(e.target.value)}
              disabled={disabled}
            />
          </div>
        );
      
      default:
        return (
          <div className="text-answer">
            <textarea
              className="textarea-input"
              placeholder="请输入答案"
              rows={4}
              value={textAnswer}
              onChange={(e) => setTextAnswer(e.target.value)}
              disabled={disabled}
            />
          </div>
        );
    }
  };

  const levelNames = ['L0-基础', 'L1-中级', 'L2-高级', 'L3-研究'];

  return (
    <div className="question-card card">
      <div className="question-header">
        <span className="question-number">
          题目 {questionNumber}/{totalQuestions}
        </span>
        <div className="question-meta">
          <span className="knowledge-level">
            {levelNames[question.knowledge_level]}
          </span>
          <span className="timer">
            ⏱️ {formatTime(timeSpent)}
          </span>
        </div>
      </div>
      
      <div className="question-content">
        <h3 className="question-text">{question.content}</h3>
        
        <div className="answer-section">
          {renderQuestionContent()}
        </div>
      </div>
      
      <div className="question-actions">
        <button
          className="btn btn-primary"
          onClick={handleSubmit}
          disabled={disabled || (
            question.type === 'single_choice' || question.type === 'true_false'
              ? selectedAnswer === null
              : textAnswer.trim() === ''
          )}
        >
          {disabled ? '提交中...' : '提交答案'}
        </button>
      </div>
    </div>
  );
};

export default QuestionCard;
