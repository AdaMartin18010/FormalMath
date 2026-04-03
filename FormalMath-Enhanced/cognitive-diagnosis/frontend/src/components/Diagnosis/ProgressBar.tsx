import React from 'react';
import './ProgressBar.css';

interface ProgressBarProps {
  current: number;
  total: number;
  percentage: number;
}

const ProgressBar: React.FC<ProgressBarProps> = ({ current, total, percentage }) => {
  return (
    <div className="progress-bar-container card">
      <div className="progress-info">
        <span className="progress-text">
          进度: {current} / {total}
        </span>
        <span className="progress-percentage">
          {percentage.toFixed(0)}%
        </span>
      </div>
      <div className="progress-bar">
        <div 
          className="progress-fill"
          style={{ width: `${percentage}%` }}
        />
      </div>
    </div>
  );
};

export default ProgressBar;
