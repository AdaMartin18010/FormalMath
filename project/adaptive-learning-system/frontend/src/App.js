import React, { useState } from 'react';
import './App.css';
import LearnerProfile from './components/LearnerProfile';
import PathGenerator from './components/PathGenerator';
import PathViewer from './components/PathViewer';
import ResourcePanel from './components/ResourcePanel';
import AchievementPanel from './components/AchievementPanel';

function App() {
  const [activeTab, setActiveTab] = useState('profile');
  const [learnerId, setLearnerId] = useState(localStorage.getItem('learnerId') || '');
  const [currentPathId, setCurrentPathId] = useState('');

  const API_BASE = process.env.REACT_APP_API_URL || 'http://localhost:8000/api/v1';

  const handleLearnerCreated = (id) => {
    setLearnerId(id);
    localStorage.setItem('learnerId', id);
  };

  const handlePathGenerated = (pathId) => {
    setCurrentPathId(pathId);
    setActiveTab('path');
  };

  return (
    <div className="App">
      <header className="App-header">
        <h1>🎓 FormalMath 自适应学习路径系统</h1>
        <p>基于知识图谱和认知诊断的个性化学习平台</p>
      </header>

      <nav className="App-nav">
        <button 
          className={activeTab === 'profile' ? 'active' : ''}
          onClick={() => setActiveTab('profile')}
        >
          👤 学习者画像
        </button>
        <button 
          className={activeTab === 'generator' ? 'active' : ''}
          onClick={() => setActiveTab('generator')}
        >
          🗺️ 路径生成
        </button>
        <button 
          className={activeTab === 'path' ? 'active' : ''}
          onClick={() => setActiveTab('path')}
        >
          📚 学习路径
        </button>
        <button 
          className={activeTab === 'resources' ? 'active' : ''}
          onClick={() => setActiveTab('resources')}
        >
          📖 学习资源
        </button>
        <button 
          className={activeTab === 'achievements' ? 'active' : ''}
          onClick={() => setActiveTab('achievements')}
        >
          🏆 成就系统
        </button>
      </nav>

      <main className="App-main">
        {activeTab === 'profile' && (
          <LearnerProfile 
            apiBase={API_BASE}
            learnerId={learnerId}
            onLearnerCreated={handleLearnerCreated}
          />
        )}
        
        {activeTab === 'generator' && (
          <PathGenerator 
            apiBase={API_BASE}
            learnerId={learnerId}
            onPathGenerated={handlePathGenerated}
          />
        )}
        
        {activeTab === 'path' && (
          <PathViewer 
            apiBase={API_BASE}
            pathId={currentPathId}
            learnerId={learnerId}
          />
        )}
        
        {activeTab === 'resources' && (
          <ResourcePanel 
            apiBase={API_BASE}
            learnerId={learnerId}
          />
        )}
        
        {activeTab === 'achievements' && (
          <AchievementPanel 
            apiBase={API_BASE}
            learnerId={learnerId}
          />
        )}
      </main>

      <footer className="App-footer">
        <p>FormalMath 自适应学习路径系统 v1.0 | 任务 T3.1</p>
      </footer>
    </div>
  );
}

export default App;
