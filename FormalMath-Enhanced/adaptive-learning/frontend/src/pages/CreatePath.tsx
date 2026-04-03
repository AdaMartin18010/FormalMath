import React, { useState, useEffect } from 'react';
import { Layout, Typography, message, Spin, Modal } from 'antd';
import { CheckCircleOutlined } from '@ant-design/icons';
import { useNavigate } from 'react-router-dom';
import { adaptiveApi } from '../api/adaptiveApi';
import { PathGenerator, PathVisualization } from '../components/Adaptive';
import type { ConceptNode, LearningPath } from '../types';
import './CreatePath.css';

const { Content } = Layout;
const { Title } = Typography;

const CreatePath: React.FC = () => {
  const navigate = useNavigate();
  const [concepts, setConcepts] = useState<ConceptNode[]>([]);
  const [loading, setLoading] = useState(true);
  const [generating, setGenerating] = useState(false);
  const [generatedPath, setGeneratedPath] = useState<LearningPath | null>(null);
  const userId = 'user_001';

  useEffect(() => {
    fetchConcepts();
  }, []);

  const fetchConcepts = async () => {
    try {
      setLoading(true);
      const result = await adaptiveApi.searchConcepts('', { limit: 100 });
      setConcepts(result.concepts);
    } catch (error) {
      message.error('获取概念列表失败');
    } finally {
      setLoading(false);
    }
  };

  const handleGenerate = async (request: {
    user_id: string;
    target_concepts: string[];
    algorithm: string;
    preferences: Record<string, any>;
  }) => {
    try {
      setGenerating(true);
      const response = await adaptiveApi.generatePath({
        user_id: request.user_id,
        target_concepts: request.target_concepts,
        algorithm: request.algorithm,
        preferences: request.preferences
      });

      if (response.success && response.path) {
        setGeneratedPath(response.path);
        Modal.success({
          title: '路径生成成功',
          content: `已为您生成包含 ${response.path.total_concepts} 个概念的学习路径，预计学习时间 ${Math.round(response.path.total_estimated_time / 60)} 小时`,
          icon: <CheckCircleOutlined />,
          okText: '查看路径',
          onOk: () => {
            navigate('/paths');
          }
        });
      } else {
        message.error(response.message || '路径生成失败');
      }
    } catch (error) {
      message.error('生成路径时出错');
    } finally {
      setGenerating(false);
    }
  };

  if (loading) {
    return (
      <Content className="create-path-content">
        <div className="loading-container">
          <Spin size="large" tip="加载概念数据..." />
        </div>
      </Content>
    );
  }

  return (
    <Content className="create-path-content">
      <Title level={2}>创建学习路径</Title>
      
      {!generatedPath ? (
        <PathGenerator
          availableConcepts={concepts}
          userId={userId}
          onGenerate={handleGenerate}
          loading={generating}
        />
      ) : (
        <div className="generated-path-preview">
          <PathVisualization 
            path={generatedPath}
            onNodeClick={(node) => console.log('Clicked:', node)}
          />
        </div>
      )}
    </Content>
  );
};

export default CreatePath;
