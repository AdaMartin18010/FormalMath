import React, { useState, useEffect } from 'react';
import './ResourcePanel.css';

function ResourcePanel({ apiBase, learnerId }) {
  const [concepts, setConcepts] = useState([]);
  const [selectedConcept, setSelectedConcept] = useState('');
  const [resources, setResources] = useState([]);
  const [searchQuery, setSearchQuery] = useState('');
  const [searchResults, setSearchResults] = useState([]);
  const [loading, setLoading] = useState(false);

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

  const fetchResources = async (conceptId) => {
    if (!learnerId || !conceptId) return;
    
    setLoading(true);
    try {
      const response = await fetch(
        `${apiBase}/resources/recommend?learner_id=${learnerId}&concept_id=${conceptId}&count=10`
      );
      if (response.ok) {
        const data = await response.json();
        setResources(data);
      }
    } catch (error) {
      console.error('Error fetching resources:', error);
    }
    setLoading(false);
  };

  const searchResources = async () => {
    if (!searchQuery) return;
    
    setLoading(true);
    try {
      const response = await fetch(
        `${apiBase}/resources/search?query=${encodeURIComponent(searchQuery)}`
      );
      if (response.ok) {
        const data = await response.json();
        setSearchResults(data);
      }
    } catch (error) {
      console.error('Error searching resources:', error);
    }
    setLoading(false);
  };

  const getResourceIcon = (type) => {
    const icons = {
      'text': '📄',
      'video': '🎬',
      'audio': '🎧',
      'interactive': '🔧',
      'exercise': '✏️',
      'project': '📁'
    };
    return icons[type] || '📎';
  };

  const getDifficultyLabel = (difficulty) => {
    const labels = { 1: '初级', 2: '中级', 3: '高级', 4: '研究级' };
    return labels[difficulty] || '未知';
  };

  return (
    <div className="resource-panel">
      <h2>📖 学习资源</h2>

      <div className="resource-search">
        <input
          type="text"
          placeholder="搜索资源..."
          value={searchQuery}
          onChange={(e) => setSearchQuery(e.target.value)}
          onKeyPress={(e) => e.key === 'Enter' && searchResources()}
        />
        <button onClick={searchResources} disabled={loading}>
          {loading ? '搜索中...' : '搜索'}
        </button>
      </div>

      {searchResults.length > 0 && (
        <div className="search-results">
          <h3>搜索结果</h3>
          {searchResults.map(r => (
            <div key={r.resource_id} className="resource-card">
              <span className="resource-icon">{getResourceIcon(r.type)}</span>
              <div className="resource-info">
                <h4>{r.title}</h4>
                <p>{r.description}</p>
                <div className="resource-meta">
                  <span className={`difficulty-${r.difficulty}`}>
                    {getDifficultyLabel(r.difficulty)}
                  </span>
                  <span>⭐ {r.rating.toFixed(1)}</span>
                </div>
              </div>
            </div>
          ))}
        </div>
      )}

      <div className="concept-selector">
        <h3>按概念浏览资源</h3>
        <select 
          value={selectedConcept} 
          onChange={(e) => {
            setSelectedConcept(e.target.value);
            fetchResources(e.target.value);
          }}
        >
          <option value="">选择概念...</option>
          {concepts.map(c => (
            <option key={c.concept_id} value={c.concept_id}>
              {c.name}
            </option>
          ))}
        </select>
      </div>

      {selectedConcept && (
        <div className="recommended-resources">
          <h3>为您推荐的资源</h3>
          {loading ? (
            <p>加载中...</p>
          ) : resources.length > 0 ? (
            resources.map(r => (
              <div key={r.resource_id} className="resource-card recommended">
                <span className="resource-icon">{getResourceIcon(r.type)}</span>
                <div className="resource-info">
                  <h4>{r.title}</h4>
                  <p>{r.description}</p>
                  <div className="resource-meta">
                    <span className={`difficulty-${r.difficulty}`}>
                      {getDifficultyLabel(r.difficulty)}
                    </span>
                    <span>⏱️ {r.estimated_time}分钟</span>
                    <span className="match-score">
                      匹配度: {(r.score * 100).toFixed(0)}%
                    </span>
                  </div>
                </div>
                <a 
                  href={r.url} 
                  target="_blank" 
                  rel="noopener noreferrer"
                  className="resource-link"
                >
                  开始学习
                </a>
              </div>
            ))
          ) : (
            <p>暂无推荐资源</p>
          )}
        </div>
      )}

      <div className="resource-types">
        <h3>资源类型说明</h3>
        <div className="type-grid">
          <div className="type-item">
            <span className="type-icon">📄</span>
            <span className="type-name">文本</span>
            <span className="type-desc">适合阅读型学习者</span>
          </div>
          <div className="type-item">
            <span className="type-icon">🎬</span>
            <span className="type-name">视频</span>
            <span className="type-desc">适合视觉型学习者</span>
          </div>
          <div className="type-item">
            <span className="type-icon">🎧</span>
            <span className="type-name">音频</span>
            <span className="type-desc">适合听觉型学习者</span>
          </div>
          <div className="type-item">
            <span className="type-icon">🔧</span>
            <span className="type-name">交互式</span>
            <span className="type-desc">适合动手型学习者</span>
          </div>
        </div>
      </div>
    </div>
  );
}

export default ResourcePanel;
