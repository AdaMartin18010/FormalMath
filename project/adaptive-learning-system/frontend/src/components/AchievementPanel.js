import React, { useState, useEffect } from 'react';
import './AchievementPanel.css';

function AchievementPanel({ apiBase, learnerId }) {
  const [achievements, setAchievements] = useState(null);
  const [leaderboard, setLeaderboard] = useState([]);
  const [newAchievements, setNewAchievements] = useState([]);
  const [loading, setLoading] = useState(false);
  const [message, setMessage] = useState('');

  useEffect(() => {
    if (learnerId) {
      fetchAchievements();
      fetchLeaderboard();
    }
  }, [learnerId]);

  const fetchAchievements = async () => {
    try {
      const response = await fetch(`${apiBase}/achievements?learner_id=${learnerId}`);
      if (response.ok) {
        const data = await response.json();
        setAchievements(data);
      }
    } catch (error) {
      console.error('Error fetching achievements:', error);
    }
  };

  const fetchLeaderboard = async () => {
    try {
      const response = await fetch(`${apiBase}/achievements/leaderboard?top_n=10`);
      if (response.ok) {
        const data = await response.json();
        setLeaderboard(data);
      }
    } catch (error) {
      console.error('Error fetching leaderboard:', error);
    }
  };

  const checkNewAchievements = async () => {
    if (!achievements) return;
    
    setLoading(true);
    try {
      // 模拟统计数据
      const stats = {
        concepts_completed: achievements.total_achievements * 2 + 5,
        current_streak: 3,
        total_hours: achievements.total_points / 10,
        high_mastery_count: achievements.total_achievements,
        paths_started: 1,
        paths_completed: achievements.total_achievements > 5 ? 1 : 0,
        peer_interactions: 0
      };

      const response = await fetch(`${apiBase}/achievements/check?learner_id=${learnerId}`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(stats)
      });

      if (response.ok) {
        const data = await response.json();
        setNewAchievements(data.new_achievements);
        if (data.unlocked_count > 0) {
          setMessage(`🎉 恭喜！解锁了 ${data.unlocked_count} 个新成就！`);
          fetchAchievements();
        } else {
          setMessage('继续学习，解锁更多成就！');
        }
      }
    } catch (error) {
      console.error('Error checking achievements:', error);
    }
    setLoading(false);
  };

  if (!learnerId) {
    return (
      <div className="achievement-panel">
        <h2>🏆 成就系统</h2>
        <p>请先创建学习者档案</p>
      </div>
    );
  }

  return (
    <div className="achievement-panel">
      <h2>🏆 成就系统</h2>

      {message && <div className="achievement-message">{message}</div>}

      {achievements && (
        <div className="achievement-summary">
          <div className="stat-card">
            <span className="stat-value">{achievements.total_achievements}</span>
            <span className="stat-label">已解锁成就</span>
          </div>
          <div className="stat-card">
            <span className="stat-value">{achievements.total_points}</span>
            <span className="stat-label">总积分</span>
          </div>
          <div className="stat-card">
            <span className="stat-value">{achievements.available_achievements}</span>
            <span className="stat-label">待解锁成就</span>
          </div>
        </div>
      )}

      <button 
        className="check-achievements-btn"
        onClick={checkNewAchievements}
        disabled={loading}
      >
        {loading ? '检查中...' : '🔍 检查新成就'}
      </button>

      {newAchievements.length > 0 && (
        <div className="new-achievements">
          <h3>🎊 新解锁的成就</h3>
          {newAchievements.map(a => (
            <div key={a.id} className="achievement-card new">
              <span className="achievement-icon">{a.icon}</span>
              <div className="achievement-info">
                <h4>{a.name}</h4>
                <p>{a.description}</p>
                <span className="points">+{a.points} 积分</span>
              </div>
            </div>
          ))}
        </div>
      )}

      {achievements && achievements.achievements.length > 0 && (
        <div className="my-achievements">
          <h3>我的成就</h3>
          <div className="achievements-grid">
            {achievements.achievements.map(a => (
              <div key={a.id} className="achievement-card">
                <span className="achievement-icon">{a.icon}</span>
                <div className="achievement-info">
                  <h4>{a.name}</h4>
                  <p>{a.description}</p>
                  <span className="category">{a.category}</span>
                  <span className="points">{a.points} 积分</span>
                </div>
              </div>
            ))}
          </div>
        </div>
      )}

      <div className="leaderboard">
        <h3>🏅 成就排行榜</h3>
        <table>
          <thead>
            <tr>
              <th>排名</th>
              <th>学习者</th>
              <th>成就数</th>
              <th>总积分</th>
            </tr>
          </thead>
          <tbody>
            {leaderboard.map((entry, idx) => (
              <tr key={entry.learner_id} className={idx < 3 ? 'top-rank' : ''}>
                <td>
                  {idx === 0 ? '🥇' : idx === 1 ? '🥈' : idx === 2 ? '🥉' : idx + 1}
                </td>
                <td>{entry.learner_id.substring(0, 8)}...</td>
                <td>{entry.achievement_count}</td>
                <td>{entry.total_points}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>

      <div className="achievement-categories">
        <h3>成就类别</h3>
        <div className="category-list">
          <div className="category-item">
            <span className="category-icon">📚</span>
            <span className="category-name">学习成就</span>
            <span className="category-desc">完成概念学习</span>
          </div>
          <div className="category-item">
            <span className="category-icon">📅</span>
            <span className="category-name">坚持成就</span>
            <span className="category-desc">保持学习连续性</span>
          </div>
          <div className="category-item">
            <span className="category-icon">⭐</span>
            <span className="category-name">掌握成就</span>
            <span className="category-desc">达到高掌握度</span>
          </div>
          <div className="category-item">
            <span className="category-icon">🤝</span>
            <span className="category-name">社交成就</span>
            <span className="category-desc">与学习伙伴互动</span>
          </div>
        </div>
      </div>
    </div>
  );
}

export default AchievementPanel;
