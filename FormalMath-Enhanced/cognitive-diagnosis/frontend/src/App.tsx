import React from 'react';
import { BrowserRouter as Router, Routes, Route, Link } from 'react-router-dom';
import DiagnosisPage from './pages/DiagnosisPage';
import ReportPage from './pages/ReportPage';
import HomePage from './pages/HomePage';
import './App.css';

const App: React.FC = () => {
  return (
    <Router>
      <div className="app">
        <nav className="navbar">
          <div className="nav-brand">
            <Link to="/">认知诊断系统</Link>
          </div>
          <ul className="nav-links">
            <li><Link to="/">首页</Link></li>
            <li><Link to="/diagnosis">开始诊断</Link></li>
            <li><Link to="/reports">诊断报告</Link></li>
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
        </footer>
      </div>
    </Router>
  );
};

export default App;
