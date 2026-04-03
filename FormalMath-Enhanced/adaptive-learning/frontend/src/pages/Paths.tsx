import React, { useState, useEffect } from 'react';
import { Layout, Typography, Card, List, Tag, Button, Space, Empty, Spin, Tabs, message } from 'antd';
import { 
  PlayCircleOutlined, 
  CheckCircleOutlined,
  ClockCircleOutlined,
  EyeOutlined,
  PlusOutlined
} from '@ant-design/icons';
import { useNavigate } from 'react-router-dom';
import { adaptiveApi } from '../api/adaptiveApi';
import { PathVisualization, ProgressTracker } from '../components/Adaptive';
import type { LearningPath, PathStatus } from '../types';
import './Paths.css';

const { Content } = Layout;
const { Title } = Typography;
const { TabPane } = Tabs;

const Paths: React.FC = () => {
  const navigate = useNavigate();
  const [paths, setPaths] = useState<LearningPath[]>([]);
  const [loading, setLoading] = useState(true);
  const [selectedPath, setSelectedPath] = useState<LearningPath | null>(null);
  const userId = 'user_001'; // 模拟用户ID

  useEffect(() => {
    fetchPaths();
  }, []);

  const fetchPaths = async () => {
    try {
      setLoading(true);
      const data = await adaptiveApi.getUserPaths(userId);
      setPaths(data);
      if (data.length > 0 && !selectedPath) {
        setSelectedPath(data[0]);
      }
    } catch (error) {
      message.error('获取学习路径失败');
    } finally {
      setLoading(false);
    }
  };

  const handleNodeStatusChange = async (nodeId: string, status: PathStatus) => {
    if (!selectedPath) return;
    
    try {
      await adaptiveApi.updateProgress({
        user_id: userId,
        path_id: selectedPath.path_id,
        node_id: nodeId,
        status
      });
      message.success('进度已更新');
      fetchPaths();
    } catch (error) {
      message.error('更新进度失败');
    }
  };

  const getStatusIcon = (status: PathStatus) => {
    switch (status) {
      case 'completed':
        return <CheckCircleOutlined style={{ color: '#52c41a' }} />;
      case 'in_progress':
        return <PlayCircleOutlined style={{ color: '#1890ff' }} />;
      default:
        return <ClockCircleOutlined style={{ color: '#999' }} />;
    }
  };

  const getStatusColor = (status: PathStatus) => {
    switch (status) {
      case 'completed':
        return 'success';
      case 'in_progress':
        return 'processing';
      case 'adjusted':
        return 'warning';
      default:
        return 'default';
    }
  };

  const getStatusText = (status: PathStatus) => {
    switch (status) {
      case 'completed':
        return '已完成';
      case 'in_progress':
        return '进行中';
      case 'adjusted':
        return '已调整';
      default:
        return '待开始';
    }
  };

  if (loading) {
    return (
      <Content className="paths-content">
        <div className="loading-container">
          <Spin size="large" />
        </div>
      </Content>
    );
  }

  return (
    <Content className="paths-content">
      <div className="paths-header">
        <Title level={2}>我的学习路径</Title>
        <Button 
          type="primary" 
          icon={<PlusOutlined />}
          onClick={() => navigate('/paths/create')}
        >
          新建路径
        </Button>
      </div>

      {paths.length === 0 ? (
        <Empty
          description="还没有学习路径"
          image={Empty.PRESENTED_IMAGE_SIMPLE}
        >
          <Button 
            type="primary" 
            onClick={() => navigate('/paths/create')}
          >
            创建第一条路径
          </Button>
        </Empty>
      ) : (
        <Tabs defaultActiveKey="visual">
          <TabPane tab="路径可视化" key="visual">
            <Row gutter={[24, 24]}>
              <Col xs={24} lg={8}>
                <Card title="路径列表">
                  <List
                    dataSource={paths}
                    renderItem={(path) => (
                      <List.Item
                        className={selectedPath?.path_id === path.path_id ? 'selected-path' : ''}
                        onClick={() => setSelectedPath(path)}
                        style={{ cursor: 'pointer' }}
                      >
                        <List.Item.Meta
                          avatar={getStatusIcon(path.status)}
                          title={path.name}
                          description={
                            <Space>
                              <Tag color={getStatusColor(path.status)}>
                                {getStatusText(path.status)}
                              </Tag>
                              <span>{path.progress_percentage.toFixed(1)}%</span>
                            </Space>
                          }
                        />
                      </List.Item>
                    )}
                  />
                </Card>
              </Col>
              <Col xs={24} lg={16}>
                {selectedPath && (
                  <PathVisualization
                    path={selectedPath}
                    onNodeStatusChange={handleNodeStatusChange}
                  />
                )}
              </Col>
            </Row>
          </TabPane>
          
          <TabPane tab="进度追踪" key="progress">
            {selectedPath ? (
              <ProgressTracker path={selectedPath} />
            ) : (
              <Empty description="请选择一条路径" />
            )}
          </TabPane>
        </Tabs>
      )}
    </Content>
  );
};

export default Paths;
