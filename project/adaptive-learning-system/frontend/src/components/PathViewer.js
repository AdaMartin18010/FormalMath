import React, { useState, useEffect } from 'react';
import './PathViewer.css';

function PathViewer({ apiBase, pathId, learnerId }) {
  const [path, setPath] = useState(null);
  const [pathList, setPathList] = useState([]);
  const [loading, setLoading] = useState(false);
  const [selectedNode, setSelectedNode] = useState(null);
  const [resources, setResources] = useState([]);
  const [adjustment, setAdjustment] = useState(null);
  const [message, setMessage] = useState('');

  useEffect(() => {
    if (learnerId) {
      fetchPathList();
    }
  }, [learnerId]);

  useEffect(() => {
    if (pathId) {
      fetchPathDetail(pathId);
    }
  }, [pathId]);

  const fetchPathList = async () => {
    try {
      const response = await fetch(`${apiBase}/learning-paths?learner_id=${learnerId}`);
      if (response.ok) {
        const data = await response.json();
        setPathList(data);
      }
    } catch (error) {
      console.error('Error fetching paths:', error);
    }
  };

  const fetchPathDetail = async (pid) => {
    setLoading(true);
    try {
      const response = await fetch(`${apiBase}/learning-path/${pid}`);
      if (response.ok) {
        const data = await response.json();
        setPath(data);
      }
    } catch (error) {
      console.error('Error fetching path:', error);
    }
    setLoading(false);
  };

  const updateProgress = async (nodeId, progress, mastery) => {
    try {
      const response = await fetch(`${apiBase}/learning-path/${pathId}/progress`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ node_id: nodeId, progress, mastery })
      });
      if (response.ok) {
        fetchPathDetail(pathId);
        setMessage('✅ 进度更新成功');
        setTimeout(() => setMessage(''), 2000);
      }
    } catch (error) {
      setMessage('❌ 更新失败');
    }
  };

  const getAdjustment = async () => {
    try {
      const response = await fetch(`${apiBase}/learning-path/${pathId}/adjust`);
      if (response.ok) {
        const data = await response.json();
        setAdjustment(data);
      }
    } catch (error) {
      console.error('Error getting adjustment:', error);
    }
  };

  const fetchResources = async (conceptId) => {
    try {
      const response = await fetch(`${apiBase}/resources/recommend?learner_id=${learnerId}&concept_id=${conceptId}`);
      if (response.ok) {
        const data = await response.json();
        setResources(data);
      }
    } catch (error) {
      console.error('Error fetching resources:', error);
    }
  };

  const getNodeStatusClass = (status) => {
    const statusMap = {
      'completed': 'status-completed',
      'in_progress': 'status-in-progress',
      'available': 'status-available',
      'locked': 'status-locked'
    };
    return statusMap[status] || 'status-locked';
  };

  const getNodeStatusIcon = (status) => {
    const iconMap = {
      'completed': '✅',
      'in_progress': '📖',
      'available': '🔓',
      'locked': '🔒'
    };
    return iconMap[status] || '🔒';
  };

  if (!learnerId) {
    return <div className="path-viewer"><p>请先创建学习者档案</p></div>;
  }

  if (!pathId && pathList.length === 0) {
    return (
      <div className="path-viewer">
        <h2>📚 学习路径</h2>
        <p>您还没有学习路径，请先生成一条学习路径。</p>
      </div>
    );
  }

  return (
    <div className="path-viewer">
      <h2>📚 学习路径</h2>
      
      {message && <div className="message">{message}</div>}
      
      {!pathId && (
        <div className="path-list">
          <h3>我的学习路径</h3>
          {pathList.map(p => (
            <div key={p.path_id} className="path-item" onClick={() => fetchPathDetail(p.path_id)}>
              <h4>{p.name}</h4>
              <p>{p.description}</p>
              <div className="path-meta">
                <span>进度: {(p.progress * 100).toFixed(0)}%</span>
                <span>状态: {p.status}</span>
                <span>节点: {p.completed_nodes}/{p.total_nodes}</span>
              </div>
            </div>
          ))}
        </div>
      )}
      
      {path && (
        <>
          <div className="path-overview">
            <h3>{path.name}</h3>
            <p>{path.description}</p>
            <div className="progress-bar">
              <div className="progress-fill" style={{width: `${path.progress * 100}%`}}></div>
              <span>{(path.progress * 100).toFixed(0)}%</span>
            </div>
            <div className="path-stats">
              <span>📚 {path.total_nodes} 个概念</span>
              <span>✅ {path.completed_nodes} 已完成</span>
              <span>⏱️ {path.remaining_hours.toFixed(1)} 小时剩余</span>
              <span>📊 状态: {path.status}</span>
            </div>
            <button className="adjust-btn" onClick={getAdjustment}>
              获取调整建议
            </button>
          </div>

          {adjustment && adjustment.adjustments && (
            <div className="adjustment-panel">
              <h4>🔄 路径调整建议</h4>
              <p><strong>原因：</strong>{adjustment.reason}</p>
              {adjustment.nodes_added > 0 && <p>新增 {adjustment.nodes_added} 个节点</p>}
              {adjustment.nodes_removed > 0 && <p>移除 {adjustment.nodes_removed} 个节点</p>}
            </div>
          )}

          <div className="nodes-container">
            <h3>学习节点</h3>
            {path.nodes.map((node, idx) => (
              <div 
                key={node.node_id} 
                className={`node-card ${getNodeStatusClass(node.status)}`}
                onClick={() => {
                  setSelectedNode(node);
                  fetchResources(node.concept_id);
                }}
              >
                <div className="node-header">
                  <span className="node-icon">{getNodeStatusIcon(node.status)}</span>
                  <span className="node-sequence">#{node.sequence + 1}</span>
                  <h4>{node.concept_id}</h4>
                </div>
                <div className="node-info">
                  <span>难度: {'⭐'.repeat(node.difficulty)}</span>
                  <span>⏱️ {node.estimated_duration}分钟</span>
                </div>
                <div className="node-progress">
                  <div className="mini-progress">
                    <div className="mini-fill" style={{width: `${node.completion * 100}%`}}></div>
                  </div>
                  <span>{(node.completion * 100).toFixed(0)}%</span>
                </div>
                <div className="node-mastery">
                  <span>掌握度: {(node.mastery * 100).toFixed(0)}%</span>
                </div>
                
                {node.status !== 'locked' && node.status !== 'completed' && (
                  <div className="progress-controls">
                    <input
                      type="range"
                      min="0"
                      max="100"
                      value={node.completion * 100}
                      onChange={(e) => {
                        const val = parseFloat(e.target.value) / 100;
                        updateProgress(node.node_id, val, node.mastery);
                      }}
                      onClick={(e) => e.stopPropagation()}
                    />
                    <button 
                      onClick={(e) => {
                        e.stopPropagation();
                        updateProgress(node.node_id, 1.0, Math.max(0.7, node.mastery + 0.1));
                      }}
                    >
                      标记完成
                    </button>
                  </div>
                )}
              </div>
            ))}
          </div>

          {selectedNode && (
            <div className="node-detail-modal" onClick={() => setSelectedNode(null)}>
              <div className="modal-content" onClick={(e) => e.stopPropagation()}>
                <h3>{selectedNode.concept_id}</h3>
                <p>难度: {'⭐'.repeat(selectedNode.difficulty)}</p>
                <p>预计时间: {selectedNode.estimated_duration}分钟</p>
                <p>当前进度: {(selectedNode.completion * 100).toFixed(0)}%</p>
                <p>掌握度: {(selectedNode.mastery * 100).toFixed(0)}%</p>
                
                <h4>推荐资源</h4>
                <div className="resources-list">
                  {resources.length > 0 ? (
                    resources.map(r => (
                      <div key={r.resource_id} className="resource-item">
                        <h5>{r.title}</h5>
                        <p>{r.description}</p>
                        <span className="resource-type">{r.type}</span>
                        <span className="resource-score">匹配度: {(r.score * 100).toFixed(0)}%</span>
                      </div>
                    ))
                  ) : (
                    <p>加载资源中...</p>
                  )}
                </div>
                
                <button onClick={() => setSelectedNode(null)}>关闭</button>
              </div>
            </div>
          )}
        </>
      )}
    </div>
  );
}

export default PathViewer;
