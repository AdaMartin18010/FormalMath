import React, { useState, useEffect } from 'react';
import { Card, List, Tag, Button, Badge, message, Empty } from 'antd';
import { CheckOutlined, BellOutlined } from '@ant-design/icons';
import { feedbackAPI } from '../services/api';

interface FeedbackItem {
  id: string;
  type: string;
  priority: string;
  title: string;
  content: string;
  suggestions: string[];
  is_read: boolean;
  created_at: string;
}

const Feedback: React.FC = () => {
  const [feedback, setFeedback] = useState<FeedbackItem[]>([]);
  const [loading, setLoading] = useState(false);
  
  useEffect(() => {
    loadFeedback();
  }, []);
  
  const loadFeedback = async () => {
    setLoading(true);
    try {
      // 模拟数据
      setFeedback([
        {
          id: '1',
          type: 'improvement',
          priority: 'high',
          title: '改进建议 - 知识掌握度',
          content: '你的知识掌握度有提升空间，建议加强基础概念的学习。',
          suggestions: ['重新阅读教材', '做概念辨析练习', '寻求帮助'],
          is_read: false,
          created_at: '2026-04-03 10:00'
        },
        {
          id: '2',
          type: 'overall',
          priority: 'low',
          title: '综合评价',
          content: '你的综合得分为78.5分，处于熟练水平。',
          suggestions: ['查看各维度详细分析', '制定针对性学习计划'],
          is_read: true,
          created_at: '2026-04-02 15:30'
        },
        {
          id: '3',
          type: 'encouragement',
          priority: 'low',
          title: '加油！',
          content: '你的进步很明显，相信通过努力会取得更大突破！',
          suggestions: [],
          is_read: false,
          created_at: '2026-04-01 09:00'
        }
      ]);
    } catch (error) {
      message.error('加载反馈失败');
    } finally {
      setLoading(false);
    }
  };
  
  const handleMarkRead = async (id: string) => {
    try {
      // await feedbackAPI.markRead(id);
      setFeedback(prev => 
        prev.map(item => 
          item.id === id ? { ...item, is_read: true } : item
        )
      );
      message.success('已标记为已读');
    } catch (error) {
      message.error('操作失败');
    }
  };
  
  const getPriorityColor = (priority: string) => {
    const colors: Record<string, string> = {
      high: 'red',
      medium: 'orange',
      low: 'green'
    };
    return colors[priority] || 'default';
  };
  
  const getPriorityText = (priority: string) => {
    const texts: Record<string, string> = {
      high: '高',
      medium: '中',
      low: '低'
    };
    return texts[priority] || priority;
  };
  
  const getTypeTag = (type: string) => {
    const types: Record<string, { text: string; color: string }> = {
      overall: { text: '综合评价', color: 'blue' },
      dimension: { text: '维度分析', color: 'cyan' },
      improvement: { text: '改进建议', color: 'orange' },
      encouragement: { text: '鼓励', color: 'green' },
      error_feedback: { text: '错误分析', color: 'red' },
      process: { text: '过程反馈', color: 'purple' },
      real_time: { text: '实时反馈', color: 'geekblue' }
    };
    const config = types[type] || { text: type, color: 'default' };
    return <Tag color={config.color}>{config.text}</Tag>;
  };
  
  const unreadCount = feedback.filter(f => !f.is_read).length;
  
  return (
    <div>
      <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center' }}>
        <h1>反馈管理</h1>
        <Badge count={unreadCount}>
          <BellOutlined style={{ fontSize: 24 }} />
        </Badge>
      </div>
      
      <Card style={{ marginTop: 16 }}>
        {feedback.length === 0 ? (
          <Empty description="暂无反馈" />
        ) : (
          <List
            loading={loading}
            itemLayout="vertical"
            dataSource={feedback}
            renderItem={item => (
              <List.Item
                style={{ 
                  background: item.is_read ? 'transparent' : '#f6ffed',
                  padding: 16,
                  marginBottom: 8,
                  borderRadius: 8
                }}
                actions={[
                  !item.is_read && (
                    <Button 
                      key="read" 
                      type="link" 
                      icon={<CheckOutlined />}
                      onClick={() => handleMarkRead(item.id)}
                    >
                      标记已读
                    </Button>
                  )
                ]}
              >
                <List.Item.Meta
                  title={
                    <div style={{ display: 'flex', alignItems: 'center', gap: 8 }}>
                      {getTypeTag(item.type)}
                      <span>{item.title}</span>
                      <Tag color={getPriorityColor(item.priority)}>
                        {getPriorityText(item.priority)}优先级
                      </Tag>
                      {!item.is_read && <Badge status="processing" />}
                    </div>
                  }
                  description={item.created_at}
                />
                <div style={{ marginTop: 8 }}>
                  <p>{item.content}</p>
                  {item.suggestions.length > 0 && (
                    <div style={{ marginTop: 8 }}>
                      <strong>建议：</strong>
                      <ul>
                        {item.suggestions.map((suggestion, index) => (
                          <li key={index}>{suggestion}</li>
                        ))}
                      </ul>
                    </div>
                  )}
                </div>
              </List.Item>
            )}
          />
        )}
      </Card>
    </div>
  );
};

export default Feedback;
