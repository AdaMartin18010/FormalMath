import React, { useEffect, useState } from 'react';
import { Card, Row, Col, Statistic, List, Tag } from 'antd';
import {
  UserOutlined,
  FileTextOutlined,
  MessageOutlined,
  RiseOutlined
} from '@ant-design/icons';
import { assessmentAPI } from '../services/api';

const Dashboard: React.FC = () => {
  const [stats, setStats] = useState({
    totalLearners: 0,
    totalEvaluations: 0,
    totalReports: 0,
    pendingFeedback: 0
  });
  
  const [recentActivities, setRecentActivities] = useState<any[]>([]);
  
  useEffect(() => {
    // 加载统计数据
    loadStats();
  }, []);
  
  const loadStats = async () => {
    try {
      // 这里应该调用实际API
      // const response = await assessmentAPI.getSystemStats();
      // setStats(response.data);
      
      // 模拟数据
      setStats({
        totalLearners: 156,
        totalEvaluations: 1248,
        totalReports: 320,
        pendingFeedback: 45
      });
      
      setRecentActivities([
        { id: 1, type: 'evaluation', content: '张三完成了能力评估', time: '10分钟前' },
        { id: 2, type: 'report', content: '生成了班级月度报告', time: '1小时前' },
        { id: 3, type: 'feedback', content: '李四收到了改进建议', time: '2小时前' },
        { id: 4, type: 'evaluation', content: '王五进行了过程性评价', time: '3小时前' },
      ]);
    } catch (error) {
      console.error('加载统计数据失败:', error);
    }
  };
  
  const getActivityTag = (type: string) => {
    switch (type) {
      case 'evaluation':
        return <Tag color="blue">评估</Tag>;
      case 'report':
        return <Tag color="green">报告</Tag>;
      case 'feedback':
        return <Tag color="orange">反馈</Tag>;
      default:
        return <Tag>其他</Tag>;
    }
  };
  
  return (
    <div>
      <h1>系统总览</h1>
      
      <Row gutter={16} style={{ marginTop: 24 }}>
        <Col span={6}>
          <Card>
            <Statistic
              title="学习者总数"
              value={stats.totalLearners}
              prefix={<UserOutlined />}
            />
          </Card>
        </Col>
        <Col span={6}>
          <Card>
            <Statistic
              title="评价次数"
              value={stats.totalEvaluations}
              prefix={<RiseOutlined />}
            />
          </Card>
        </Col>
        <Col span={6}>
          <Card>
            <Statistic
              title="生成报告"
              value={stats.totalReports}
              prefix={<FileTextOutlined />}
            />
          </Card>
        </Col>
        <Col span={6}>
          <Card>
            <Statistic
              title="待处理反馈"
              value={stats.pendingFeedback}
              prefix={<MessageOutlined />}
            />
          </Card>
        </Col>
      </Row>
      
      <Row gutter={16} style={{ marginTop: 24 }}>
        <Col span={12}>
          <Card title="最近活动">
            <List
              dataSource={recentActivities}
              renderItem={item => (
                <List.Item>
                  <List.Item.Meta
                    title={
                      <span>
                        {getActivityTag(item.type)}
                        <span style={{ marginLeft: 8 }}>{item.content}</span>
                      </span>
                    }
                    description={item.time}
                  />
                </List.Item>
              )}
            />
          </Card>
        </Col>
        <Col span={12}>
          <Card title="系统状态">
            <p>✅ 评估服务: 正常运行</p>
            <p>✅ 数据库: 连接正常</p>
            <p>✅ 报告生成: 正常运行</p>
            <p>✅ 反馈系统: 正常运行</p>
            <p style={{ marginTop: 16, color: '#666' }}>
              系统版本: v1.0.0 | 最后更新: 2026-04-03
            </p>
          </Card>
        </Col>
      </Row>
    </div>
  );
};

export default Dashboard;
