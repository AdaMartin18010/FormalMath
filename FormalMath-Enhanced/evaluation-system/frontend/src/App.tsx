import React, { useState, useEffect } from 'react';
import { BrowserRouter as Router, Routes, Route, Link } from 'react-router-dom';
import AssessmentPage from './pages/AssessmentPage';
import ReportPage from './pages/ReportPage';
import ProgressPage from './pages/ProgressPage';
import FeedbackPage from './pages/FeedbackPage';
import './App.css';

const App: React.FC = () => {
  const [isMobileMenuOpen, setIsMobileMenuOpen] = useState(false);
  const [isOnline, setIsOnline] = useState(navigator.onLine);

  useEffect(() => {
    const handleOnline = () => setIsOnline(true);
    const handleOffline = () => setIsOnline(false);

    window.addEventListener('online', handleOnline);
    window.addEventListener('offline', handleOffline);

    return () => {
      window.removeEventListener('online', handleOnline);
      window.removeEventListener('offline', handleOffline);
    };
  }, []);

  const toggleMobileMenu = () => {
    setIsMobileMenuOpen(!isMobileMenuOpen);
  };

  const closeMobileMenu = () => {
    setIsMobileMenuOpen(false);
  };

  return (
    <Router>
      <div className="app">
        {/* 离线指示器 */}
        {!isOnline && (
          <div className="offline-indicator">
            <span>⚠️ 离线模式 - 部分功能可能受限</span>
          </div>
        )}
        
        <nav className="navbar">
          <div className="nav-brand">
            <Link to="/" onClick={closeMobileMenu}>
              <h1>FormalMath 评估系统</h1>
            </Link>
          </div>
          
          {/* 移动端汉堡菜单按钮 */}
          <button 
            className={`nav-toggle ${isMobileMenuOpen ? 'active' : ''}`}
            onClick={toggleMobileMenu}
            aria-label="切换导航菜单"
            aria-expanded={isMobileMenuOpen}
          >
            <span></span>
            <span></span>
            <span></span>
          </button>
          
          <ul className={`nav-links ${isMobileMenuOpen ? 'active' : ''}`}>
            <li><Link to="/" onClick={closeMobileMenu}>评估录入</Link></li>
            <li><Link to="/report" onClick={closeMobileMenu}>评估报告</Link></li>
            <li><Link to="/progress" onClick={closeMobileMenu}>学习轨迹</Link></li>
            <li><Link to="/feedback" onClick={closeMobileMenu}>反馈建议</Link></li>
          </ul>
        </nav>
        
        <main className="main-content">
          <Routes>
            <Route path="/" element={<AssessmentPage />} />
            <Route path="/report" element={<ReportPage />} />
            <Route path="/progress" element={<ProgressPage />} />
            <Route path="/feedback" element={<FeedbackPage />} />
          </Routes>
        </main>
        
        <footer className="footer">
          <p>© 2024 FormalMath 项目 | 五维数学能力评估系统</p>
          {!isOnline && <small> | 离线模式</small>}
        </footer>
      </div>
    </Router>
  );
};

export default App;
