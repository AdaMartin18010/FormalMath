import React, { useState } from 'react';
import ReportDisplay from '../components/Evaluation/ReportDisplay';
import RadarChart from '../components/Evaluation/RadarChart';
import { evaluationApi } from '../api/evaluation';
import { EvaluationReport } from '../types';

const ReportPage: React.FC = () => {
  const [userId, setUserId] = useState('');
  const [recordId, setRecordId] = useState('');
  const [report, setReport] = useState<EvaluationReport | null>(null);
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
      const response = await evaluationApi.getReport(
        userId,
        recordId.trim() || undefined
      );
      setReport(response);
    } catch (err: any) {
      setError(err.error || '获取报告失败');
    } finally {
      setLoading(false);
    }
  };

  const prepareRadarData = (report: EvaluationReport) => {
    return Object.entries(report.detailed_scores.dimension_scores).map(
      ([key, dim]: [string, any]) => ({
        dimension: dim.name,
        score: dim.score,
        fullMark: 100,
      })
    );
  };

  return (
    <div className="report-page">
      <h2>评估报告</h2>

      <div className="card">
        <h3 className="card-title">查询评估报告</h3>
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
              <label>记录ID (可选)</label>
              <input
                type="text"
                className="form-control"
                value={recordId}
                onChange={(e) => setRecordId(e.target.value)}
                placeholder="输入特定记录ID"
              />
            </div>
          </div>
          <button type="submit" className="btn btn-primary" disabled={loading}>
            {loading ? '查询中...' : '查询报告'}
          </button>
        </form>
      </div>

      {error && <div className="error-message">{error}</div>}

      {loading && (
        <div className="loading">
          <div className="spinner"></div>
        </div>
      )}

      {report && !loading && (
        <>
          <div className="card">
            <RadarChart
              data={prepareRadarData(report)}
              title="五维能力雷达图"
            />
          </div>
          <ReportDisplay report={report} />
        </>
      )}
    </div>
  );
};

export default ReportPage;
