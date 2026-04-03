import React from 'react';
import { EvaluationReport } from '../../types';

interface ReportDisplayProps {
  report: EvaluationReport;
}

const ReportDisplay: React.FC<ReportDisplayProps> = ({ report }) => {
  const { executive_summary, detailed_scores, dimension_analysis, strengths_and_improvements } = report;

  const getGradeClass = (grade: string): string => {
    const gradeMap: Record<string, string> = {
      'A': 'grade-a',
      'B': 'grade-b',
      'C': 'grade-c',
      'D': 'grade-d',
      'F': 'grade-f',
    };
    return gradeMap[grade] || '';
  };

  const getStatusClass = (level: string): string => {
    const statusMap: Record<string, string> = {
      'excellent': 'status-excellent',
      'good': 'status-good',
      'satisfactory': 'status-average',
      'needs_improvement': 'status-needs-improvement',
      'critical': 'status-critical',
    };
    return statusMap[level] || '';
  };

  return (
    <div className="report-display">
      {/* Executive Summary */}
      <div className="card">
        <h3 className="card-title">执行摘要</h3>
        <div className="score-display">
          <div className="score-value">{executive_summary.overall_score.toFixed(1)}</div>
          <div className="score-label">综合得分</div>
          <span className={`score-grade ${getGradeClass(executive_summary.grade)}`}>
            等级 {executive_summary.grade}
          </span>
        </div>
        <p style={{ marginTop: '1rem', textAlign: 'center', color: '#4a5568' }}>
          {executive_summary.overall_assessment}
        </p>
        <div style={{ marginTop: '1rem', display: 'flex', justifyContent: 'center', gap: '1rem' }}>
          {executive_summary.key_highlights.map((highlight, index) => (
            <span key={index} className="status-badge status-good">
              {highlight}
            </span>
          ))}
        </div>
      </div>

      {/* Detailed Scores */}
      <div className="card">
        <h3 className="card-title">详细得分</h3>
        <div className="dimension-scores">
          {Object.entries(detailed_scores.dimension_scores).map(([key, dim]) => (
            <div key={key} className="dimension-card">
              <div className="dimension-name">{dim.name}</div>
              <div className="dimension-score">{dim.score.toFixed(1)}</div>
              <div className="dimension-weight">权重 {(dim.weight * 100).toFixed(0)}%</div>
            </div>
          ))}
        </div>
      </div>

      {/* Dimension Analysis */}
      <div className="card">
        <h3 className="card-title">维度分析</h3>
        <div className="analysis-list">
          {Object.entries(dimension_analysis).map(([key, analysis]) => (
            <div key={key} className="analysis-item">
              <div className="analysis-header">
                <h4>{analysis.name}</h4>
                <span className={`status-badge ${getStatusClass(analysis.level)}`}>
                  {analysis.level === 'excellent' && '优秀'}
                  {analysis.level === 'good' && '良好'}
                  {analysis.level === 'satisfactory' && '中等'}
                  {analysis.level === 'needs_improvement' && '需改进'}
                  {analysis.level === 'critical' && '需关注'}
                </span>
              </div>
              <p className="analysis-description">{analysis.description}</p>
              {analysis.recommendations.length > 0 && (
                <div className="recommendations">
                  <strong>建议:</strong>
                  <ul>
                    {analysis.recommendations.map((rec, idx) => (
                      <li key={idx}>{rec}</li>
                    ))}
                  </ul>
                </div>
              )}
            </div>
          ))}
        </div>
      </div>

      {/* Strengths and Improvements */}
      <div className="card">
        <h3 className="card-title">优势与提升空间</h3>
        <div className="strengths-weaknesses">
          <div className="strengths-section">
            <h4 className="section-title" style={{ color: '#38a169' }}>
              ✅ 优势领域
            </h4>
            {strengths_and_improvements.strengths.length > 0 ? (
              <ul className="strengths-list">
                {strengths_and_improvements.strengths.map((item, index) => (
                  <li key={index} className="strength-item">
                    <strong>{item.name}</strong> - {item.score}分
                  </li>
                ))}
              </ul>
            ) : (
              <p className="empty-message">暂无突出优势领域</p>
            )}
          </div>

          <div className="weaknesses-section" style={{ marginTop: '1.5rem' }}>
            <h4 className="section-title" style={{ color: '#e53e3e' }}>
              📈 提升空间
            </h4>
            {strengths_and_improvements.weaknesses.length > 0 ? (
              <ul className="weaknesses-list">
                {strengths_and_improvements.weaknesses.map((item, index) => (
                  <li key={index} className="weakness-item">
                    <strong>{item.name}</strong> - {item.score}分
                  </li>
                ))}
              </ul>
            ) : (
              <p className="empty-message">各维度表现均衡，继续保持!</p>
            )}
          </div>
        </div>
      </div>
    </div>
  );
};

export default ReportDisplay;
