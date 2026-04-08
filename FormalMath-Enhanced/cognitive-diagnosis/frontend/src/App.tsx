import React, { useState, useEffect } from 'react';
import { BrowserRouter as Router, Routes, Route, Link } from 'react-router-dom';
import DiagnosisPage from './pages/DiagnosisPage';
import ReportPage from './pages/ReportPage';
import HomePage from './pages/HomePage';
import './App.css';
import './styles/responsive.css';

const App: React.FC = () => {
  const [isMobileMenuOpen, setIsMobileMenuOpen] = useState(false);
  const [isOnline, setIsOnline] = useState(navigator.onLine);

  useEffect(() => {
    // 监听网络状态
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
            <span>⚠️ 当前处于离线模式，部分功能可能受限</span>
          </div>
        )}
        
        <nav className="navbar">
          <div className="nav-brand">
            <Link to="/" onClick={closeMobileMenu}>认知诊断系统</Link>
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
            <li><Link to="/" onClick={closeMobileMenu}>首页</Link></li>
            <li><Link to="/diagnosis" onClick={closeMobileMenu}>开始诊断</Link></li>
            <li><Link to="/reports" onClick={closeMobileMenu}>诊断报告</Link></li>
          </ul>
        </nav>
        
        <main className="main-content">
          <Routes>
            <Route path="/" element={<HomePage />} />
            <Route path="/diagnosis" element={<DiagnosisPage />} />
            <Route path="/reports" element={<ReportPage />} />
            <Route path="/reports/:reportId" element={<ReportPage />} />
          </Routes>
        </main>
        
        <footer className="footer">
          <p>© 2026 FormalMath项目 - 认知诊断系统</p>
          {!isOnline && <small> | 离线模式</small>}
        </footer>
      </div>
    </Router>
  );
};

export default App;
