import React, { useState, useEffect } from 'react';
import './PathGenerator.css';

function PathGenerator({ apiBase, learnerId, onPathGenerated }) {
  const [concepts, setConcepts] = useState([]);
  const [selectedGoals, setSelectedGoals] = useState([]);
  const [constraints, setConstraints] = useState({
    max_time_hours: 100,
    difficulty_range_min: 0.5,
    difficulty_range_max: 1.5,
    diversity_weight: 0.2
  });
  const [generatedPaths, setGeneratedPaths] = useState([]);
  const [loading, setLoading] = useState(false);
  const [message, setMessage] = useState('');

  useEffect(() => {
    fetchConcepts();
  }, []);

  const fetchConcepts = async () => {
    try {
      const response = await fetch(`${apiBase}/knowledge-graph/concepts`);
      if (response.ok) {
        const data = await response.json();
        setConcepts(data);
      }
    } catch (error) {
      console.error('Error fetching concepts:', error);
    }
  };

  const generatePath = async () => {
    if (!learnerId) {
      setMessage('❌ 请先创建学习者档案');
      return;
    }
    if (selectedGoals.length === 0) {
      setMessage('❌ 请至少选择一个目标概念');
      return;
    }

    setLoading(true);
    setMessage('');
    
    try {
      const response = await fetch(`${apiBase}/learning-path/generate`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          learner_id: learnerId,
          goal_concepts: selectedGoals,
          max_time_hours: constraints.max_time_hours,
          difficulty_range_min: constraints.difficulty_range_min,
          difficulty_range_max: constraints.difficulty_range_max,
          diversity_weight: constraints.diversity_weight
        })
      });
      
      if (response.ok) {
        const data = await response.json();
        setGeneratedPaths(data.paths);
        setMessage('✅ 学习路径生成成功！');
      } else {
        const error = await response.json();
        setMessage('❌ 生成失败：' + error.detail);
      }
    } catch (error) {
      setMessage('❌ 网络错误：' + error.message);
    }
    setLoading(false);
  };

  const startPath = async (pathId) => {
    try {
      const response = await fetch(`${apiBase}/learning-path/${pathId}/start`, {
        method: 'POST'
      });
      if (response.ok) {
        onPathGenerated(pathId);
        setMessage('✅ 学习路径已开始！');
      }
    } catch (error) {
      setMessage('❌ 启动失败：' + error.message);
    }
  };

  const toggleGoal = (conceptName) => {
    if (selectedGoals.includes(conceptName)) {
      setSelectedGoals(selectedGoals.filter(g => g !== conceptName));
    } else {
      setSelectedGoals([...selectedGoals, conceptName]);
    }
  };

  const getDifficultyLabel = (level) => {
    const labels = { 1: '初级', 2: '中级', 3: '高级', 4: '研究级' };
    return labels[level] || '未知';
  };

  return (
    <div className="path-generator">
      <h2>🗺️ 生成学习路径</h2>
      
      {message && <div className="message">{message}</div>}
      
      <div className="section">
        <h3>🎯 选择学习目标</h3>
        <p className="hint">选择一个或多个您想要学习的概念：</p>
        <div className="concepts-grid">
          {concepts.map(concept => (
            <div
              key={concept.concept_id}
              className={`concept-card ${selectedGoals.includes(concept.name) ? 'selected' : ''}`}
              onClick={() => toggleGoal(concept.name)}
            >
              <h4>{concept.name}</h4>
              <span className={`difficulty difficulty-${concept.difficulty}`}>
                {getDifficultyLabel(concept.difficulty)}
              </span>
              <p>{concept.description.substring(0, 50)}...</p>
              <small>预计时间: {concept.estimated_time}分钟</small>
            </div>
          ))}
        </div>
      </div>

      <div className="section">
        <h3>⚙️ 路径约束设置</h3>
        <div className="constraints-form">
          <div className="form-group">
            <label>最大总时长（小时）：</label>
            <input
              type="number"
              min="10"
              max="500"
              value={constraints.max_time_hours}
              onChange={(e) => setConstraints({...constraints, max_time_hours: parseFloat(e.target.value)})}
            />
          </div>
          <div className="form-group">
            <label>难度偏好范围：</label>
            <div className="range-inputs">
              <input
                type="number"
                min="0"
                max="2"
                step="0.1"
                value={constraints.difficulty_range_min}
                onChange={(e) => setConstraints({...constraints, difficulty_range_min: parseFloat(e.target.value)})}
              />
              <span>至</span>
              <input
                type="number"
                min="0"
                max="2"
                step="0.1"
                value={constraints.difficulty_range_max}
                onChange={(e) => setConstraints({...constraints, difficulty_range_max: parseFloat(e.target.value)})}
              />
            </div>
          </div>
          <div className="form-group">
            <label>多样性权重：</label>
            <input
              type="range"
              min="0"
              max="1"
              step="0.1"
              value={constraints.diversity_weight}
              onChange={(e) => setConstraints({...constraints, diversity_weight: parseFloat(e.target.value)})}
            />
            <span>{constraints.diversity_weight}</span>
          </div>
        </div>
      </div>

      <button 
        className="generate-btn"
        onClick={generatePath}
        disabled={loading || selectedGoals.length === 0}
      >
        {loading ? '生成中...' : '🚀 生成个性化学习路径'}
      </button>

      {generatedPaths.length > 0 && (
        <div className="section generated-paths">
          <h3>📋 生成的学习路径</h3>
          {generatedPaths.map((path, idx) => (
            <div key={path.path_id} className="path-card">
              <div className="path-header">
                <h4>路径 {idx + 1} {idx === 0 && <span className="best-tag">最佳推荐</span>}</h4>
                <span className="match-score">匹配度: {(path.match_score * 100).toFixed(1)}%</span>
              </div>
              <p className="path-description">{path.description}</p>
              <div className="path-stats">
                <span>📚 {path.total_nodes} 个概念</span>
                <span>⏱️ {path.estimated_hours.toFixed(1)} 小时</span>
              </div>
              <p className="path-reason"><strong>推荐理由：</strong>{path.reason || '综合推荐'}</p>
              <button 
                className="start-btn"
                onClick={() => startPath(path.path_id)}
              >
                开始学习
              </button>
            </div>
          ))}
        </div>
      )}
    </div>
  );
}

export default PathGenerator;
