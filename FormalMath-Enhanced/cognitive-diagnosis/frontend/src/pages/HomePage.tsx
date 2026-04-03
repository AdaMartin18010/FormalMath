import React from 'react';
import { useNavigate } from 'react-router-dom';
import './HomePage.css';

const HomePage: React.FC = () => {
  const navigate = useNavigate();

  return (
    <div className="home-page">
      <section className="hero">
        <h1>认知诊断系统</h1>
        <p className="subtitle">
          基于HCD（层级认知诊断）框架的智能诊断系统<br />
          精准评估数学概念掌握程度，生成个性化学习建议
        </p>
        <div className="hero-actions">
          <button 
            className="btn btn-primary btn-large"
            onClick={() => navigate('/diagnosis')}
          >
            开始诊断
          </button>
          <button 
            className="btn btn-secondary btn-large"
            onClick={() => navigate('/reports')}
          >
            查看报告
          </button>
        </div>
      </section>

      <section className="features">
        <h2>系统特点</h2>
        <div className="feature-grid">
          <div className="feature-card">
            <div className="feature-icon">📊</div>
            <h3>层次化评估</h3>
            <p>基于L0-L3知识层次结构，全面评估从基础到研究各层次能力</p>
          </div>
          <div className="feature-card">
            <div className="feature-icon">🧠</div>
            <h3>HCD算法</h3>
            <p>采用层次约束感知认知诊断算法，提高诊断准确性</p>
          </div>
          <div className="feature-card">
            <div className="feature-icon">📝</div>
            <h3>个性化建议</h3>
            <p>根据诊断结果生成针对性学习路径和方法建议</p>
          </div>
          <div className="feature-card">
            <div className="feature-icon">📈</div>
            <h3>可视化报告</h3>
            <p>雷达图、饼图等多种可视化方式展示诊断结果</p>
          </div>
        </div>
      </section>

      <section className="knowledge-levels">
        <h2>知识层次说明</h2>
        <div className="level-list">
          <div className="level-item">
            <div className="level-badge l0">L0</div>
            <div className="level-content">
              <h4>基础层</h4>
              <p>直观理解、基本定义、简单例子</p>
            </div>
          </div>
          <div className="level-item">
            <div className="level-badge l1">L1</div>
            <div className="level-content">
              <h4>中级层</h4>
              <p>严格定义、基本定理、证明思路</p>
            </div>
          </div>
          <div className="level-item">
            <div className="level-badge l2">L2</div>
            <div className="level-content">
              <h4>高级层</h4>
              <p>深入定理、应用、前沿内容</p>
            </div>
          </div>
          <div className="level-item">
            <div className="level-badge l3">L3</div>
            <div className="level-content">
              <h4>研究层</h4>
              <p>开放问题、研究方向、前沿研究</p>
            </div>
          </div>
        </div>
      </section>
    </div>
  );
};

export default HomePage;
