import React, { useState, useEffect } from 'react';
import './LearnerProfile.css';

function LearnerProfile({ apiBase, learnerId, onLearnerCreated }) {
  const [profile, setProfile] = useState(null);
  const [loading, setLoading] = useState(false);
  const [newLearnerForm, setNewLearnerForm] = useState({ name: '', email: '' });
  const [styleAnswers, setStyleAnswers] = useState({});
  const [styleQuestions, setStyleQuestions] = useState([]);
  const [timeAvailability, setTimeAvailability] = useState({
    daily_hours: 2,
    weekly_days: 5,
    preferred_time: 'evening',
    max_session: 60
  });
  const [message, setMessage] = useState('');

  useEffect(() => {
    if (learnerId) {
      fetchProfile();
      fetchStyleQuestions();
    }
  }, [learnerId]);

  const fetchProfile = async () => {
    try {
      const response = await fetch(`${apiBase}/learners/${learnerId}`);
      if (response.ok) {
        const data = await response.json();
        setProfile(data);
      }
    } catch (error) {
      console.error('Error fetching profile:', error);
    }
  };

  const fetchStyleQuestions = async () => {
    try {
      const response = await fetch(`${apiBase}/learning-style/questions`);
      if (response.ok) {
        const data = await response.json();
        setStyleQuestions(data);
      }
    } catch (error) {
      console.error('Error fetching questions:', error);
    }
  };

  const createLearner = async () => {
    setLoading(true);
    try {
      const response = await fetch(`${apiBase}/learners`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(newLearnerForm)
      });
      if (response.ok) {
        const data = await response.json();
        onLearnerCreated(data.learner_id);
        setMessage('✅ 学习者创建成功！');
        fetchProfile();
      }
    } catch (error) {
      setMessage('❌ 创建失败：' + error.message);
    }
    setLoading(false);
  };

  const submitStyleAssessment = async () => {
    setLoading(true);
    try {
      const response = await fetch(`${apiBase}/learners/${learnerId}/learning-style`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ answers: styleAnswers })
      });
      if (response.ok) {
        const data = await response.json();
        setMessage(`✅ 学习风格评估完成：您的主要风格是 ${data.dominant_style}`);
        fetchProfile();
      }
    } catch (error) {
      setMessage('❌ 评估失败：' + error.message);
    }
    setLoading(false);
  };

  const updateTimeAvailability = async () => {
    setLoading(true);
    try {
      const response = await fetch(`${apiBase}/learners/${learnerId}/time-availability`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(timeAvailability)
      });
      if (response.ok) {
        const data = await response.json();
        setMessage(`✅ 时间可用性已更新：每周 ${data.weekly_available_hours} 小时`);
        fetchProfile();
      }
    } catch (error) {
      setMessage('❌ 更新失败：' + error.message);
    }
    setLoading(false);
  };

  if (!learnerId) {
    return (
      <div className="learner-profile">
        <h2>👤 创建学习者档案</h2>
        <div className="form-section">
          <input
            type="text"
            placeholder="您的姓名"
            value={newLearnerForm.name}
            onChange={(e) => setNewLearnerForm({...newLearnerForm, name: e.target.value})}
          />
          <input
            type="email"
            placeholder="您的邮箱"
            value={newLearnerForm.email}
            onChange={(e) => setNewLearnerForm({...newLearnerForm, email: e.target.value})}
          />
          <button onClick={createLearner} disabled={loading}>
            {loading ? '创建中...' : '创建档案'}
          </button>
        </div>
      </div>
    );
  }

  return (
    <div className="learner-profile">
      <h2>👤 学习者画像</h2>
      
      {message && <div className="message">{message}</div>}
      
      {profile && (
        <div className="profile-summary">
          <h3>基本信息</h3>
          <p><strong>姓名：</strong>{profile.name}</p>
          <p><strong>整体能力水平：</strong>{(profile.overall_ability * 100).toFixed(1)}%</p>
          <p><strong>学习风格：</strong>{profile.learning_style}</p>
          <p><strong>每周学习时间：</strong>{profile.weekly_study_hours} 小时</p>
          <p><strong>已掌握概念：</strong>{profile.concepts_mastered} / {profile.total_concepts_attempted}</p>
        </div>
      )}

      <div className="assessment-section">
        <h3>📝 学习风格评估</h3>
        {styleQuestions.length > 0 ? (
          <>
            {styleQuestions.map((q, idx) => (
              <div key={q.id} className="question">
                <p>{idx + 1}. {q.question}</p>
                <div className="options">
                  {q.options.map((opt) => (
                    <label key={opt.text} className="option">
                      <input
                        type="radio"
                        name={q.id}
                        value={opt.style}
                        checked={styleAnswers[q.id] === opt.style}
                        onChange={(e) => setStyleAnswers({...styleAnswers, [q.id]: e.target.value})}
                      />
                      {opt.text}
                    </label>
                  ))}
                </div>
              </div>
            ))}
            <button onClick={submitStyleAssessment} disabled={loading}>
              {loading ? '提交中...' : '提交评估'}
            </button>
          </>
        ) : (
          <p>加载问题中...</p>
        )}
      </div>

      <div className="availability-section">
        <h3>⏰ 学习时间设置</h3>
        <div className="form-group">
          <label>每日可用时间（小时）：</label>
          <input
            type="number"
            min="0.5"
            max="12"
            step="0.5"
            value={timeAvailability.daily_hours}
            onChange={(e) => setTimeAvailability({...timeAvailability, daily_hours: parseFloat(e.target.value)})}
          />
        </div>
        <div className="form-group">
          <label>每周可用天数：</label>
          <input
            type="number"
            min="1"
            max="7"
            value={timeAvailability.weekly_days}
            onChange={(e) => setTimeAvailability({...timeAvailability, weekly_days: parseInt(e.target.value)})}
          />
        </div>
        <div className="form-group">
          <label>偏好学习时间：</label>
          <select
            value={timeAvailability.preferred_time}
            onChange={(e) => setTimeAvailability({...timeAvailability, preferred_time: e.target.value})}
          >
            <option value="morning">早晨</option>
            <option value="afternoon">下午</option>
            <option value="evening">晚上</option>
          </select>
        </div>
        <div className="form-group">
          <label>单次最大学习时长（分钟）：</label>
          <input
            type="number"
            min="15"
            max="240"
            step="15"
            value={timeAvailability.max_session}
            onChange={(e) => setTimeAvailability({...timeAvailability, max_session: parseInt(e.target.value)})}
          />
        </div>
        <button onClick={updateTimeAvailability} disabled={loading}>
          {loading ? '更新中...' : '更新时间设置'}
        </button>
      </div>
    </div>
  );
}

export default LearnerProfile;
