import React from 'react';
import './AnswerFeedback.css';

interface AnswerFeedbackProps {
  isCorrect: boolean;
  score: number;
}

const AnswerFeedback: React.FC<AnswerFeedbackProps> = ({ isCorrect, score }) => {
  return (
    <div className={`answer-feedback ${isCorrect ? 'correct' : 'incorrect'}`}>
      <div className="feedback-icon">
        {isCorrect ? '✓' : '✗'}
      </div>
      <div className="feedback-content">
        <h3>{isCorrect ? '回答正确！' : '回答错误'}</h3>
        <p>得分: {score} 分</p>
      </div>
    </div>
  );
};

export default AnswerFeedback;
