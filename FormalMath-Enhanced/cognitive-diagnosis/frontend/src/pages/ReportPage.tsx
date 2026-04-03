import React, { useState, useEffect } from 'react';
import { useParams, useNavigate } from 'react-router-dom';
import { getReportById, getUserReports } from '../api/reports';
import { DiagnosisReport } from '../types';
import AbilityRadarChart from '../components/Diagnosis/AbilityRadarChart';
import KnowledgePieChart from '../components/Diagnosis/KnowledgePieChart';
import SuggestionsList from '../components/Diagnosis/SuggestionsList';
import './ReportPage.css';

const ReportPage: React.FC = () => {
  const { reportId } = useParams<{ reportId?: string }>();
  const navigate = useNavigate();
  
  const [report, setReport] = useState<DiagnosisReport | null>(null);
  const [reports, setReports] = useState<DiagnosisReport[]>([]);
  const [isLoading, setIsLoading] = useState(true);
  const [error, setError] = useState<string>('');
  const [activeTab, setActiveTab] = useState<'overview' | 'details' | 'suggestions'>('overview');

  useEffect(() => {
    if (reportId) {
      loadReport(reportId);
    } else {
      loadReportList();
    }
  }, [reportId]);

  const loadReport = async (id: string) => {
    setIsLoading(true);
    try {
      const response = await getReportById(id);
      if (response.success) {
        setReport(response.data);
      } else {
        setError('加载报告失败');
      }
    } catch (err: any) {
      setError(err.message || '网络错误');
    } finally {
      setIsLoading(false);
    }
  };

  const loadReportList = async () => {
    setIsLoading(true);
    try {
      const response = await getUserReports('user_demo', 10, 0);
      if (response.success) {
        setReports(response.data);
        if (response.data.length > 0) {
          setReport(response.data[0]);
        }
      } else {
        setError('加载报告列表失败');
      }
    } catch (err: any) {
      setError(err.message || '网络错误');
    } finally {
      setIsLoading(false);
    }
  };

  // 报告列表视图
  if (!reportId && !isLoading && reports.length === 0) {
    return (
      <div className="report-page">
        <div className="no-reports card">
          <h2>暂无诊断报告</h2>
          <p>您还没有完成任何诊断测试</p>
          <button 
            className="btn btn-primary"
            onClick={() => navigate('/diagnosis')}
          >
            开始诊断
          </button>
        </div>
      </div>
    );
  }

  if (isLoading) {
    return <div className="loading">加载中...</div>;
  }

  if (error) {
    return <div className="error">{error}</div>;
  }

  if (!report) {
    return <div className="error">报告不存在</div>;
  }

  // 能力水平描述
  const getAbilityDescription = (score: number): { level: string; color: string } => {
    if (score >= 0.8) return { level: '优秀', color: '#4caf50' };
    if (score >= 0.6) return { level: '良好', color: '#2196f3' };
    if (score >= 0.4) return { level: '一般', color: '#ff9800' };
    return { level: '待提高', color: '#f44336' };
  };

  return (
    <div className="report-page">
      <header className="report-header">
        <h1>诊断报告</h1>
        <p className="report-meta">
          报告ID: {report.id} | 
          生成时间: {new Date(report.created_at).toLocaleString('zh-CN')}
        </p>
      </header>

      {/* 统计概览 */}
      <div className="stats-grid">
        <div className="stat-card">
          <div className="stat-value">{report.total_questions}</div>
          <div className="stat-label">总题数</div>
        </div>
        <div className="stat-card">
          <div className="stat-value">{report.correct_count}</div>
          <div className="stat-label">正确数</div>
        </div>
        <div className="stat-card">
          <div className="stat-value">{(report.accuracy * 100).toFixed(1)}%</div>
          <div className="stat-label">正确率</div>
        </div>
        <div className="stat-card">
          <div className="stat-value">{Math.round(report.avg_time_per_question)}s</div>
          <div className="stat-label">平均用时</div>
        </div>
      </div>

      {/* 标签页 */}
      <div className="report-tabs">
        <button 
          className={`tab-btn ${activeTab === 'overview' ? 'active' : ''}`}
          onClick={() => setActiveTab('overview')}
        >
          能力概览
        </button>
        <button 
          className={`tab-btn ${activeTab === 'details' ? 'active' : ''}`}
          onClick={() => setActiveTab('details')}
        >
          层次详情
        </button>
        <button 
          className={`tab-btn ${activeTab === 'suggestions' ? 'active' : ''}`}
          onClick={() => setActiveTab('suggestions')}
        >
          学习建议
        </button>
      </div>

      {/* 标签内容 */}
      <div className="tab-content">
        {activeTab === 'overview' && (
          <div className="overview-section">
            <div className="charts-grid">
              <div className="chart-card">
                <h3>能力水平雷达图</h3>
                <AbilityRadarChart data={report.visualization_data.radar} />
              </div>
              <div className="chart-card">
                <h3>知识掌握分布</h3>
                <KnowledgePieChart data={report.visualization_data.pie} />
              </div>
            </div>
            
            <div className="ability-summary">
              <h3>各层次能力评估</h3>
              <div className="ability-bars">
                {[0, 1, 2, 3].map(level => {
                  const score = report.ability_level[level] || 0;
                  const desc = getAbilityDescription(score);
                  const levelNames = ['L0-基础层', 'L1-中级层', 'L2-高级层', 'L3-研究层'];
                  
                  return (
                    <div key={level} className="ability-bar-item">
                      <div className="ability-bar-header">
                        <span className="ability-name">{levelNames[level]}</span>
                        <span className="ability-score" style={{ color: desc.color }}>
                          {(score * 100).toFixed(1)}% - {desc.level}
                        </span>
                      </div>
                      <div className="ability-bar">
                        <div 
                          className="ability-bar-fill"
                          style={{ 
                            width: `${score * 100}%`,
                            backgroundColor: desc.color 
                          }}
                        />
                      </div>
                    </div>
                  );
                })}
              </div>
            </div>
          </div>
        )}

        {activeTab === 'details' && (
          <div className="details-section">
            {report.ability_assessments.map(assessment => (
              <div key={assessment.level} className="level-detail-card">
                <div className="level-header">
                  <h3>L{assessment.level} 层次评估</h3>
                  <span className="level-score">
                    {(assessment.score * 100).toFixed(1)}%
                  </span>
                </div>
                <p className="level-description">{assessment.description}</p>
                
                {assessment.mastered_concepts.length > 0 && (
                  <div className="concept-section">
                    <h4>已掌握概念</h4>
                    <div className="concept-tags">
                      {assessment.mastered_concepts.map((concept, idx) => (
                        <span key={idx} className="concept-tag mastered">
                          {concept}
                        </span>
                      ))}
                    </div>
                  </div>
                )}
                
                {assessment.weak_concepts.length > 0 && (
                  <div className="concept-section">
                    <h4>薄弱概念</h4>
                    <div className="concept-tags">
                      {assessment.weak_concepts.map((concept, idx) => (
                        <span key={idx} className="concept-tag weak">
                          {concept}
                        </span>
                      ))}
                    </div>
                  </div>
                )}
              </div>
            ))}
          </div>
        )}

        {activeTab === 'suggestions' && (
          <div className="suggestions-section">
            <SuggestionsList suggestions={report.suggestions} />
          </div>
        )}
      </div>

      {/* 报告列表（当查看单个报告时显示） */}
      {reportId && reports.length > 1 && (
        <div className="report-history">
          <h3>历史报告</h3>
          <div className="history-list">
            {reports.map(r => (
              <div 
                key={r.id}
                className={`history-item ${r.id === reportId ? 'active' : ''}`}
                onClick={() => navigate(`/reports/${r.id}`)}
              >
                <span className="history-date">
                  {new Date(r.created_at).toLocaleDateString('zh-CN')}
                </span>
                <span className="history-accuracy">
                  {(r.accuracy * 100).toFixed(0)}%
                </span>
              </div>
            ))}
          </div>
        </div>
      )}
    </div>
  );
};

export default ReportPage;
