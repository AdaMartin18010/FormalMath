import React from 'react';
import { BrowserRouter as Router, Routes, Route, Link } from 'react-router-dom';
import AssessmentPage from './pages/AssessmentPage';
import ReportPage from './pages/ReportPage';
import ProgressPage from './pages/ProgressPage';
import FeedbackPage from './pages/FeedbackPage';
import './App.css';

const App: React.FC = () => {
  return (
    <Router>
      <div className="app">
        <nav className="navbar">
          <div className="nav-brand">
            <h1>FormalMath 评估系统</h1>
          </div>
          <ul className="nav-links">
            <li><Link to="/">评估录入</Link></li>
            <li><Link to="/report">评估报告</Link></li>
            <li><Link to="/progress">学习轨迹</Link></li>
            <li><Link to="/feedback">反馈建议</Link></li>
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
        </footer>
      </div>
    </Router>
  );
};

export default App;
