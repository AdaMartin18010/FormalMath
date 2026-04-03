import React from 'react';
import { DimensionInfo } from '../../types';

interface ScoreInputProps {
  dimension: DimensionInfo;
  value: number;
  onChange: (value: number) => void;
}

const ScoreInput: React.FC<ScoreInputProps> = ({ dimension, value, onChange }) => {
  const handleSliderChange = (e: React.ChangeEvent<HTMLInputElement>) => {
    onChange(Number(e.target.value));
  };

  const handleNumberChange = (e: React.ChangeEvent<HTMLInputElement>) => {
    let val = Number(e.target.value);
    if (val < 0) val = 0;
    if (val > 100) val = 100;
    onChange(val);
  };

  const getScoreColor = (score: number): string => {
    if (score >= 90) return '#48bb78';
    if (score >= 80) return '#68d391';
    if (score >= 70) return '#ecc94b';
    if (score >= 60) return '#ed8936';
    return '#fc8181';
  };

  const getScoreLevel = (score: number): string => {
    if (score >= 90) return '优秀';
    if (score >= 80) return '良好';
    if (score >= 70) return '中等';
    if (score >= 60) return '及格';
    return '需加强';
  };

  return (
    <div className="score-input-card">
      <div className="score-input-header">
        <div>
          <h4 className="dimension-title">{dimension.name}</h4>
          <p className="dimension-description">{dimension.description}</p>
        </div>
        <div className="score-badge" style={{ backgroundColor: getScoreColor(value) + '20', color: getScoreColor(value) }}>
          <span className="score-value-display">{value}</span>
          <span className="score-level">{getScoreLevel(value)}</span>
        </div>
      </div>

      <div className="score-input-body">
        <input
          type="range"
          min="0"
          max="100"
          value={value}
          onChange={handleSliderChange}
          className="score-slider"
          style={{ 
            background: `linear-gradient(to right, ${getScoreColor(value)} 0%, ${getScoreColor(value)} ${value}%, #e2e8f0 ${value}%, #e2e8f0 100%)` 
          }}
        />
        <div className="score-range-labels">
          <span>0</span>
          <span>25</span>
          <span>50</span>
          <span>75</span>
          <span>100</span>
        </div>
      </div>

      <div className="score-input-footer">
        <label className="score-number-label">
          精确分值:
          <input
            type="number"
            min="0"
            max="100"
            value={value}
            onChange={handleNumberChange}
            className="score-number-input"
          />
        </label>
        <span className="weight-badge">权重 {(dimension.weight * 100).toFixed(0)}%</span>
      </div>
    </div>
  );
};

export default ScoreInput;
