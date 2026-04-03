import React from 'react';
import { Card, Progress, Timeline, Tag, Space, Statistic, Row, Col } from 'antd';
import { 
  CheckCircleOutlined, 
  ClockCircleOutlined, 
  BookOutlined,
  TrophyOutlined
} from '@ant-design/icons';
import type { LearningPath, PathNode, PathStatus } from '../../types';
import './ProgressTracker.css';

interface ProgressTrackerProps {
  path: LearningPath;
}

const statusIcons: Record<PathStatus, React.ReactNode> = {
  pending: <ClockCircleOutlined />,
  in_progress: <BookOutlined style={{ color: '#1890ff' }} />,
  completed: <CheckCircleOutlined style={{ color: '#52c41a' }} />,
  adjusted: <ClockCircleOutlined style={{ color: '#faad14' }} />,
  abandoned: <ClockCircleOutlined style={{ color: '#ff4d4f' }} />
};

const statusColors: Record<PathStatus, string> = {
  pending: 'gray',
  in_progress: 'blue',
  completed: 'green',
  adjusted: 'orange',
  abandoned: 'red'
};

const ProgressTracker: React.FC<ProgressTrackerProps> = ({ path }) => {
  // 计算统计数据
  const completedCount = path.nodes.filter(n => n.status === 'completed').length;
  const inProgressCount = path.nodes.filter(n => n.status === 'in_progress').length;
  const pendingCount = path.nodes.filter(n => n.status === 'pending').length;
  
  const completedTime = path.nodes
    .filter(n => n.status === 'completed')
    .reduce((sum, n) => sum + n.estimated_time, 0);
  
  const totalTime = path.total_estimated_time;
  const timeProgress = totalTime > 0 ? Math.round((completedTime / totalTime) * 100) : 0;

  return (
    <div className="progress-tracker">
      {/* 总体进度统计 */}
      <Row gutter={[16, 16]} className="progress-stats">
        <Col xs={24} sm={12} md={6}>
          <Card>
            <Statistic
              title="总体进度"
              value={path.progress_percentage}
              suffix="%"
              precision={1}
              valueStyle={{ color: '#1890ff' }}
              prefix={<TrophyOutlined />}
            />
            <Progress 
              percent={path.progress_percentage} 
              status="active"
              strokeColor={{ from: '#108ee9', to: '#87d068' }}
            />
          </Card>
        </Col>
        <Col xs={24} sm={12} md={6}>
          <Card>
            <Statistic
              title="已完成概念"
              value={completedCount}
              suffix={`/ ${path.total_concepts}`}
              valueStyle={{ color: '#52c41a' }}
              prefix={<CheckCircleOutlined />}
            />
          </Card>
        </Col>
        <Col xs={24} sm={12} md={6}>
          <Card>
            <Statistic
              title="学习中"
              value={inProgressCount}
              valueStyle={{ color: '#faad14' }}
              prefix={<BookOutlined />}
            />
          </Card>
        </Col>
        <Col xs={24} sm={12} md={6}>
          <Card>
            <Statistic
              title="预计剩余时间"
              value={Math.round((totalTime - completedTime) / 60)}
              suffix="小时"
              valueStyle={{ color: '#666' }}
              prefix={<ClockCircleOutlined />}
            />
          </Card>
        </Col>
      </Row>

      {/* 时间进度 */}
      <Card className="time-progress-card" title="时间投入">
        <Progress 
          percent={timeProgress}
          format={() => `${Math.round(completedTime / 60)} / ${Math.round(totalTime / 60)} 小时`}
          strokeColor="#52c41a"
        />
      </Card>

      {/* 学习进度时间线 */}
      <Card className="timeline-card" title="学习进度">
        <Timeline mode="left">
          {path.nodes.map((node, index) => (
            <Timeline.Item
              key={node.node_id}
              dot={statusIcons[node.status]}
              color={statusColors[node.status]}
              label={
                <Space direction="vertical" size={0} style={{ textAlign: 'right' }}>
                  <Tag color={statusColors[node.status]}>
                    {node.status === 'completed' ? '已完成' :
                     node.status === 'in_progress' ? '进行中' : '待开始'}
                  </Tag>
                  <span className="time-label">{node.estimated_time}分钟</span>
                </Space>
              }
            >
              <div className="timeline-content">
                <h4>{node.concept.name}</h4>
                <Space wrap>
                  <Tag>{node.concept.branch}</Tag>
                  <Tag color="blue">{node.concept.difficulty}</Tag>
                  {node.status === 'completed' && (
                    <Tag color="success">已掌握</Tag>
                  )}
                </Space>
                {node.recommended_resources.length > 0 && (
                  <div className="resources-preview">
                    <span>推荐资源: </span>
                    {node.recommended_resources.slice(0, 2).map((res, i) => (
                      <Tag key={i} size="small">{res.title}</Tag>
                    ))}
                    {node.recommended_resources.length > 2 && (
                      <Tag size="small">+{node.recommended_resources.length - 2}</Tag>
                    )}
                  </div>
                )}
              </div>
            </Timeline.Item>
          ))}
        </Timeline>
      </Card>
    </div>
  );
};

export default ProgressTracker;
