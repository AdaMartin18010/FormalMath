import React, { useEffect, useState } from 'react';
import { useParams } from 'react-router-dom';
import { Card, Descriptions, Tag, Timeline, Statistic, Row, Col, Button, message } from 'antd';
import {
  RadarChart, Radar, PolarGrid, PolarAngleAxis, PolarRadiusAxis,
  LineChart, Line, XAxis, YAxis, CartesianGrid, Tooltip, Legend
} from 'recharts';
import { learnerAPI, evaluationAPI } from '../services/api';

const LearnerDetail: React.FC = () => {
  const { id } = useParams<{ id: string }>();
  const [learner, setLearner] = useState<any>(null);
  const [evaluationHistory, setEvaluationHistory] = useState<any[]>([]);
  const [loading, setLoading] = useState(false);
  
  useEffect(() => {
    if (id) {
      loadLearnerData();
    }
  }, [id]);
  
  const loadLearnerData = async () => {
    setLoading(true);
    try {
      // 模拟数据
      setLearner({
        id,
        name: '张三',
        email: 'zhangsan@example.com',
        created_at: '2026-03-01',
        ability_profile: {
          '知识掌握度': 85,
          '技能熟练度': 78,
          '问题解决能力': 82,
          '创新思维能力': 75
        },
        knowledge_state: {
          '集合论基础': 90,
          '函数与映射': 85,
          '数理逻辑': 70,
          '证明方法': 75,
          '抽象代数入门': 60
        }
      });
      
      setEvaluationHistory([
        { date: '2026-03-01', score: 65 },
        { date: '2026-03-15', score: 72 },
        { date: '2026-04-01', score: 80 },
      ]);
    } catch (error) {
      message.error('加载学习者数据失败');
    } finally {
      setLoading(false);
    }
  };
  
  const abilityData = learner ? Object.entries(learner.ability_profile).map(([key, value]) => ({
    dimension: key,
    score: value
  })) : [];
  
  if (!learner) {
    return <div>加载中...</div>;
  }
  
  return (
    <div>
      <h1>{learner.name} - 学习者详情</h1>
      
      <Row gutter={16} style={{ marginTop: 24 }}>
        <Col span={16}>
          <Card title="能力雷达图" loading={loading}>
            <RadarChart cx={300} cy={200} outerRadius={150} width={600} height={400} data={abilityData}>
              <PolarGrid />
              <PolarAngleAxis dataKey="dimension" />
              <PolarRadiusAxis angle={30} domain={[0, 100]} />
              <Radar
                name="能力得分"
                dataKey="score"
                stroke="#8884d8"
                fill="#8884d8"
                fillOpacity={0.6}
              />
              <Tooltip />
            </RadarChart>
          </Card>
        </Col>
        
        <Col span={8}>
          <Card title="基本信息" loading={loading}>
            <Descriptions column={1}>
              <Descriptions.Item label="姓名">{learner.name}</Descriptions.Item>
              <Descriptions.Item label="邮箱">{learner.email}</Descriptions.Item>
              <Descriptions.Item label="注册时间">{learner.created_at}</Descriptions.Item>
            </Descriptions>
          </Card>
          
          <Card title="学习统计" style={{ marginTop: 16 }}>
            <Row>
              <Col span={12}>
                <Statistic title="评价次数" value={12} />
              </Col>
              <Col span={12}>
                <Statistic title="学习时长" value="48小时" />
              </Col>
            </Row>
          </Card>
        </Col>
      </Row>
      
      <Row gutter={16} style={{ marginTop: 16 }}>
        <Col span={12}>
          <Card title="学习趋势">
            <LineChart width={500} height={300} data={evaluationHistory}>
              <CartesianGrid strokeDasharray="3 3" />
              <XAxis dataKey="date" />
              <YAxis domain={[0, 100]} />
              <Tooltip />
              <Legend />
              <Line type="monotone" dataKey="score" stroke="#8884d8" name="综合得分" />
            </LineChart>
          </Card>
        </Col>
        
        <Col span={12}>
          <Card title="知识掌握情况">
            {Object.entries(learner.knowledge_state).map(([concept, mastery]: [string, any]) => (
              <div key={concept} style={{ marginBottom: 12 }}>
                <div style={{ display: 'flex', justifyContent: 'space-between' }}>
                  <span>{concept}</span>
                  <Tag color={mastery >= 80 ? 'success' : mastery >= 60 ? 'warning' : 'error'}>
                    {mastery}%
                  </Tag>
                </div>
                <div style={{ 
                  width: '100%', 
                  height: 8, 
                  background: '#f0f0f0', 
                  borderRadius: 4,
                  marginTop: 4
                }}>
                  <div style={{
                    width: `${mastery}%`,
                    height: '100%',
                    background: mastery >= 80 ? '#52c41a' : mastery >= 60 ? '#faad14' : '#f5222d',
                    borderRadius: 4
                  }} />
                </div>
              </div>
            ))}
          </Card>
        </Col>
      </Row>
    </div>
  );
};

export default LearnerDetail;
