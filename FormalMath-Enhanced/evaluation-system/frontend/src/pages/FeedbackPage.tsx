import React, { useState } from 'react';
import { evaluationApi } from '../api/evaluation';
import { FeedbackResponse } from '../types';

const FeedbackPage: React.FC = () => {
  const [userId, setUserId] = useState('');
  const [recordId, setRecordId] = useState('');
  const [feedback, setFeedback] = useState<FeedbackResponse | null>(null);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const handleSubmit = async (e: React.FormEvent) => {
    e.preventDefault();

    if (!userId.trim() || !recordId.trim()) {
      setError('请输入用户ID和记录ID');
      return;
    }

    setLoading(true);
    setError(null);

    try {
      const response = await evaluationApi.generateFeedback({
        user_id: userId,
        record_id: recordId,
      });
      setFeedback(response);
    } catch (err: any) {
      setError(err.error || '生成反馈失败');
    } finally {
      setLoading(false);
    }
  };

  const getPriorityColor = (priority: string): string => {
    const map: Record<string, string> = {
      high: '#e53e3e',
      medium: '#ed8936',
      low: '#48bb78',
    };
    return map[priority] || '#718096';
  };

  return (
    <div className="feedback-page">
      <h2>个性化反馈</h2>

      <div className="card">
        <h3 className="card-title">生成反馈</h3>
        <form onSubmit={handleSubmit}>
          <div className="form-row">
            <div className="form-group">
              <label>用户ID *</label>
              <input
                type="text"
                className="form-control"
                value={userId}
                onChange={(e) => setUserId(e.target.value)}
                placeholder="输入用户ID"
                required
              />
            </div>
            <div className="form-group">
              <label>评估记录ID *</label>
              <input
                type="text"
                className="form-control"
                value={recordId}
                onChange={(e) => setRecordId(e.target.value)}
                placeholder="输入评估记录ID"
                required
              />
            </div>
          </div>
          <button type="submit" className="btn btn-primary" disabled={loading}>
            {loading ? '生成中...' : '生成反馈'}
          </button>
        </form>
      </div>

      {error && <div className="error-message">{error}</div>}

      {loading && (
        <div className="loading">
          <div className="spinner"></div>
        </div>
      )}

      {feedback && !loading && (
        <div className="feedback-display">
          {/* Summary */}
          <div className="card">
            <h3 className="card-title">总体评价</h3>
            <p style={{ fontSize: '1.1rem', lineHeight: 1.8, color: '#2d3748' }}>
              {feedback.summary}
            </p>
          </div>

          {/* Strengths */}
          {feedback.strengths.length > 0 && (
            <div className="card">
              <h3 className="card-title" style={{ color: '#38a169' }}>
                ✅ 优势领域
              </h3>
              <div style={{ display: 'grid', gap: '1rem' }}>
                {feedback.strengths.map((item, index) => (
                  <div
                    key={index}
                    style={{
                      padding: '1rem',
                      background: '#f0fff4',
                      borderRadius: '8px',
                      borderLeft: '4px solid #38a169',
                    }}
                  >
                    <div style={{ fontWeight: 600, color: '#22543d' }}>
                      {item.name}
                    </div>
                    <div style={{ color: '#38a169', fontSize: '1.25rem' }}>
                      {item.score} 分
                    </div>
                  </div>
                ))}
              </div>
            </div>
          )}

          {/* Weaknesses */}
          {feedback.weaknesses.length > 0 && (
            <div className="card">
              <h3 className="card-title" style={{ color: '#e53e3e' }}>
                📈 提升空间
              </h3>
              <div style={{ display: 'grid', gap: '1rem' }}>
                {feedback.weaknesses.map((item, index) => (
                  <div
                    key={index}
                    style={{
                      padding: '1rem',
                      background: '#fff5f5',
                      borderRadius: '8px',
                      borderLeft: '4px solid #e53e3e',
                    }}
                  >
                    <div style={{ fontWeight: 600, color: '#742a2a' }}>
                      {item.name}
                    </div>
                    <div style={{ color: '#e53e3e', fontSize: '1.25rem' }}>
                      {item.score} 分
                    </div>
                  </div>
                ))}
              </div>
            </div>
          )}

          {/* Suggestions */}
          {feedback.suggestions.length > 0 && (
            <div className="card">
              <h3 className="card-title">💡 学习建议</h3>
              <div style={{ display: 'grid', gap: '1rem' }}>
                {feedback.suggestions.map((suggestion, index) => (
                  <div
                    key={index}
                    style={{
                      padding: '1.25rem',
                      background: '#ebf8ff',
                      borderRadius: '8px',
                      borderLeft: `4px solid ${getPriorityColor(suggestion.priority)}`,
                    }}
                  >
                    <div
                      style={{
                        display: 'flex',
                        justifyContent: 'space-between',
                        alignItems: 'center',
                        marginBottom: '0.5rem',
                      }}
                    >
                      <span style={{ fontWeight: 600, color: '#2b6cb0' }}>
                        {suggestion.dimension_name}
                      </span>
                      <span
                        style={{
                          padding: '0.25rem 0.75rem',
                          borderRadius: '50px',
                          fontSize: '0.75rem',
                          fontWeight: 500,
                          backgroundColor: getPriorityColor(suggestion.priority) + '20',
                          color: getPriorityColor(suggestion.priority),
                        }}
                      >
                        {suggestion.priority === 'high'
                          ? '高优先级'
                          : suggestion.priority === 'medium'
                          ? '中优先级'
                          : '低优先级'}
                      </span>
                    </div>
                    <div style={{ color: '#4a5568', marginBottom: '0.5rem' }}>
                      目标分数: {suggestion.target_score} 分
                    </div>
                    <ul
                      style={{
                        margin: 0,
                        paddingLeft: '1.25rem',
                        color: '#4a5568',
                      }}
                    >
                      {suggestion.actions.map((action, idx) => (
                        <li key={idx} style={{ marginBottom: '0.25rem' }}>
                          {action}
                        </li>
                      ))}
                    </ul>
                  </div>
                ))}
              </div>
            </div>
          )}

          {/* Learning Path */}
          {feedback.recommended_path && (
            <div className="card">
              <h3 className="card-title">🎯 推荐学习路径</h3>
              <div style={{ marginBottom: '1rem' }}>
                <span style={{ color: '#4a5568' }}>预计周期: </span>
                <span style={{ fontWeight: 600, color: '#1a365d' }}>
                  {feedback.recommended_path.total_duration}
                </span>
              </div>
              <div style={{ display: 'grid', gap: '1rem' }}>
                {feedback.recommended_path.phases.map((phase) => (
                  <div
                    key={phase.phase}
                    style={{
                      padding: '1.25rem',
                      background: '#faf5ff',
                      borderRadius: '8px',
                      borderLeft: '4px solid #805ad5',
                    }}
                  >
                    <div
                      style={{
                        display: 'flex',
                        justifyContent: 'space-between',
                        alignItems: 'center',
                        marginBottom: '0.5rem',
                      }}
                    >
                      <span style={{ fontWeight: 600, color: '#553c9a' }}>
                        阶段 {phase.phase}: {phase.name}
                      </span>
                      <span style={{ color: '#805ad5', fontSize: '0.875rem' }}>
                        {phase.duration}
                      </span>
                    </div>
                    <div style={{ color: '#4a5568', marginBottom: '0.5rem' }}>
                      重点: {phase.focus.join(', ')}
                    </div>
                    <ul
                      style={{
                        margin: 0,
                        paddingLeft: '1.25rem',
                        color: '#718096',
                        fontSize: '0.875rem',
                      }}
                    >
                      {phase.objectives.map((obj, idx) => (
                        <li key={idx}>{obj}</li>
                      ))}
                    </ul>
                  </div>
                ))}
              </div>
              <div
                style={{
                  marginTop: '1rem',
                  padding: '1rem',
                  background: '#f0fff4',
                  borderRadius: '8px',
                  color: '#22543d',
                }}
              >
                <strong>预期成果:</strong> {feedback.recommended_path.expected_outcome}
              </div>
            </div>
          )}

          {/* Resources */}
          {feedback.recommended_resources.length > 0 && (
            <div className="card">
              <h3 className="card-title">📚 推荐资源</h3>
              <div style={{ display: 'grid', gap: '0.75rem' }}>
                {feedback.recommended_resources.map((resource, index) => (
                  <div
                    key={index}
                    style={{
                      display: 'flex',
                      alignItems: 'center',
                      padding: '0.75rem 1rem',
                      background: '#f7fafc',
                      borderRadius: '6px',
                    }}
                  >
                    <span
                      style={{
                        padding: '0.25rem 0.5rem',
                        borderRadius: '4px',
                        fontSize: '0.75rem',
                        fontWeight: 500,
                        backgroundColor: '#4299e1',
                        color: 'white',
                        marginRight: '0.75rem',
                      }}
                    >
                      {resource.type}
                    </span>
                    <span style={{ flex: 1, color: '#2d3748' }}>
                      {resource.title}
                    </span>
                    <span
                      style={{
                        padding: '0.25rem 0.5rem',
                        borderRadius: '4px',
                        fontSize: '0.75rem',
                        backgroundColor:
                          resource.difficulty === '高级'
                            ? '#fed7d7'
                            : resource.difficulty === '进阶'
                            ? '#feebc8'
                            : '#c6f6d5',
                        color:
                          resource.difficulty === '高级'
                            ? '#742a2a'
                            : resource.difficulty === '进阶'
                            ? '#7c2d12'
                            : '#22543d',
                      }}
                    >
                      {resource.difficulty}
                    </span>
                  </div>
                ))}
              </div>
            </div>
          )}
        </div>
      )}
    </div>
  );
};

export default FeedbackPage;
