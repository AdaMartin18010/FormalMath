import React, { useState } from 'react';
import GrowthCurve from '../components/Evaluation/GrowthCurve';
import { evaluationApi } from '../api/evaluation';
import { ProgressResponse, TrajectoryPoint } from '../types';

const ProgressPage: React.FC = () => {
  const [userId, setUserId] = useState('');
  const [periods, setPeriods] = useState(6);
  const [progress, setProgress] = useState<ProgressResponse | null>(null);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const handleSubmit = async (e: React.FormEvent) => {
    e.preventDefault();

    if (!userId.trim()) {
      setError('请输入用户ID');
      return;
    }

    setLoading(true);
    setError(null);

    try {
      const response = await evaluationApi.getProgress(userId, periods);
      setProgress(response);
    } catch (err: any) {
      setError(err.error || '获取学习轨迹失败');
    } finally {
      setLoading(false);
    }
  };

  const calculateStats = (trajectory: TrajectoryPoint[]) => {
    if (trajectory.length < 2) return null;

    const first = trajectory[0].scores;
    const last = trajectory[trajectory.length - 1].scores;

    const changes: Record<string, number> = {};
    Object.keys(first).forEach((key) => {
      changes[key] = (last as any)[key] - (first as any)[key];
    });

    const avgChange =
      Object.values(changes).reduce((a, b) => a + b, 0) /
      Object.values(changes).length;

    return {
      changes,
      avgChange,
      trend: avgChange > 0 ? '上升' : avgChange < 0 ? '下降' : '稳定',
    };
  };

  const getTrendColor = (value: number): string => {
    if (value > 0) return '#48bb78';
    if (value < 0) return '#e53e3e';
    return '#ed8936';
  };

  const dimensionNames: Record<string, string> = {
    knowledge_mastery: '知识掌握度',
    problem_solving: '问题解决',
    proof_ability: '证明能力',
    application: '应用能力',
    innovation: '创新思维',
  };

  return (
    <div className="progress-page">
      <h2>学习轨迹</h2>

      <div className="card">
        <h3 className="card-title">查询学习轨迹</h3>
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
              <label>周期数</label>
              <input
                type="number"
                className="form-control"
                value={periods}
                onChange={(e) => setPeriods(Number(e.target.value))}
                min={1}
                max={24}
              />
            </div>
          </div>
          <button type="submit" className="btn btn-primary" disabled={loading}>
            {loading ? '查询中...' : '查询轨迹'}
          </button>
        </form>
      </div>

      {error && <div className="error-message">{error}</div>}

      {loading && (
        <div className="loading">
          <div className="spinner"></div>
        </div>
      )}

      {progress && !loading && progress.data_points > 0 && (
        <>
          <div className="card">
            <GrowthCurve
              data={progress.trajectory}
              title="能力发展趋势"
              showAllDimensions={true}
            />
          </div>

          {calculateStats(progress.trajectory) && (
            <div className="card">
              <h3 className="card-title">变化统计</h3>
              <div
                style={{
                  display: 'grid',
                  gridTemplateColumns: 'repeat(auto-fit, minmax(150px, 1fr))',
                  gap: '1rem',
                }}
              >
                {Object.entries(calculateStats(progress.trajectory)!.changes).map(
                  ([key, value]) => (
                    <div
                      key={key}
                      style={{
                        padding: '1rem',
                        background: '#f7fafc',
                        borderRadius: '8px',
                        textAlign: 'center',
                      }}
                    >
                      <div style={{ fontSize: '0.875rem', color: '#718096' }}>
                        {dimensionNames[key]}
                      </div>
                      <div
                        style={{
                          fontSize: '1.5rem',
                          fontWeight: 700,
                          color: getTrendColor(value),
                        }}
                      >
                        {value > 0 ? '+' : ''}
                        {value.toFixed(1)}
                      </div>
                    </div>
                  )
                )}
              </div>
              <div
                style={{
                  marginTop: '1rem',
                  padding: '1rem',
                  background: '#edf2f7',
                  borderRadius: '8px',
                  textAlign: 'center',
                }}
              >
                <span style={{ color: '#4a5568' }}>整体趋势: </span>
                <span
                  style={{
                    fontWeight: 600,
                    color: getTrendColor(calculateStats(progress.trajectory)!.avgChange),
                  }}
                >
                  {calculateStats(progress.trajectory)!.trend}
                </span>
                <span style={{ marginLeft: '0.5rem', color: '#718096' }}>
                  (平均变化: {calculateStats(progress.trajectory)!.avgChange.toFixed(1)})
                </span>
              </div>
            </div>
          )}

          {progress.growth_analysis && (
            <div className="card">
              <h3 className="card-title">增长分析</h3>
              <div style={{ display: 'grid', gap: '1rem' }}>
                {progress.growth_analysis.period_growth.map((pg, index) => (
                  <div
                    key={index}
                    style={{
                      padding: '1rem',
                      background: '#f7fafc',
                      borderRadius: '8px',
                    }}
                  >
                    <div style={{ fontWeight: 600, color: '#1a365d' }}>
                      {pg.period}
                    </div>
                    <div style={{ marginTop: '0.5rem', color: '#4a5568' }}>
                      整体增长: {pg.growth.overall_growth > 0 ? '+' : ''}
                      {pg.growth.overall_growth.toFixed(1)} 分
                    </div>
                  </div>
                ))}
              </div>
            </div>
          )}
        </>
      )}

      {progress && !loading && progress.data_points === 0 && (
        <div className="card">
          <p style={{ textAlign: 'center', color: '#718096' }}>
            暂无该用户的学习轨迹数据
          </p>
        </div>
      )}
    </div>
  );
};

export default ProgressPage;
