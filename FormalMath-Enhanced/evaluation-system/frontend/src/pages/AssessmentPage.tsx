import React, { useState, useEffect } from 'react';
import ScoreInput from '../components/Evaluation/ScoreInput';
import { evaluationApi } from '../api/evaluation';
import { DimensionInfo, AssessmentResponse } from '../types';

const AssessmentPage: React.FC = () => {
  const [dimensions, setDimensions] = useState<DimensionInfo[]>([]);
  const [scores, setScores] = useState<Record<string, number>>({
    knowledge_mastery: 75,
    problem_solving: 75,
    proof_ability: 75,
    application: 75,
    innovation: 75,
  });
  const [userId, setUserId] = useState('');
  const [period, setPeriod] = useState('');
  const [notes, setNotes] = useState('');
  const [loading, setLoading] = useState(false);
  const [result, setResult] = useState<AssessmentResponse | null>(null);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    loadDimensions();
  }, []);

  const loadDimensions = async () => {
    try {
      const response = await evaluationApi.getDimensions();
      setDimensions(response.dimensions);
    } catch (err: any) {
      setError('加载评估维度失败');
    }
  };

  const handleScoreChange = (dimension: string, value: number) => {
    setScores((prev) => ({ ...prev, [dimension]: value }));
  };

  const handleSubmit = async (e: React.FormEvent) => {
    e.preventDefault();
    
    if (!userId.trim()) {
      setError('请输入用户ID');
      return;
    }

    setLoading(true);
    setError(null);

    try {
      const response = await evaluationApi.assess({
        user_id: userId,
        scores: {
          knowledge_mastery: scores.knowledge_mastery,
          problem_solving: scores.problem_solving,
          proof_ability: scores.proof_ability,
          application: scores.application,
          innovation: scores.innovation,
        },
        period: period || undefined,
        notes: notes || undefined,
      });

      setResult(response);
    } catch (err: any) {
      setError(err.error || '评估提交失败');
    } finally {
      setLoading(false);
    }
  };

  const getGradeClass = (grade: string): string => {
    const map: Record<string, string> = {
      A: 'grade-a', B: 'grade-b', C: 'grade-c', D: 'grade-d', F: 'grade-f',
    };
    return map[grade] || '';
  };

  return (
    <div className="assessment-page">
      <h2>五维评估录入</h2>

      {error && <div className="error-message">{error}</div>}

      <form onSubmit={handleSubmit}>
        <div className="card">
          <h3 className="card-title">基本信息</h3>
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
              <label>评估周期</label>
              <input
                type="text"
                className="form-control"
                value={period}
                onChange={(e) => setPeriod(e.target.value)}
                placeholder="例如: 2024-Q1"
              />
            </div>
          </div>
        </div>

        <div className="card">
          <h3 className="card-title">维度评分 (0-100)</h3>
          {dimensions.map((dim) => (
            <ScoreInput
              key={dim.key}
              dimension={dim}
              value={scores[dim.key] || 0}
              onChange={(value) => handleScoreChange(dim.key, value)}
            />
          ))}
        </div>

        <div className="card">
          <h3 className="card-title">备注</h3>
          <div className="form-group">
            <textarea
              className="form-control"
              rows={3}
              value={notes}
              onChange={(e) => setNotes(e.target.value)}
              placeholder="输入备注信息（可选）"
            />
          </div>
        </div>

        <button type="submit" className="btn btn-primary" disabled={loading}>
          {loading ? '提交中...' : '提交评估'}
        </button>
      </form>

      {result && (
        <div className="card" style={{ marginTop: '2rem' }}>
          <h3 className="card-title">评估结果</h3>
          <div className="score-display">
            <div className="score-value">{result.scores.weighted_score.toFixed(1)}</div>
            <div className="score-label">综合得分</div>
            <span className={`score-grade ${getGradeClass(result.scores.grade)}`}>
              等级 {result.scores.grade}
            </span>
          </div>

          <div className="dimension-scores">
            {Object.entries(result.scores.dimension_scores).map(([key, dim]: [string, any]) => (
              <div key={key} className="dimension-card">
                <div className="dimension-name">{dim.name}</div>
                <div className="dimension-score">{dim.score}</div>
                <div className="dimension-weight">权重 {(dim.weight * 100).toFixed(0)}%</div>
              </div>
            ))}
          </div>

          <div className="success-message" style={{ marginTop: '1rem' }}>
            评估已保存！记录ID: {result.record_id}
          </div>
        </div>
      )}
    </div>
  );
};

export default AssessmentPage;
