import React from 'react';
import { Card, Tag, Space, Progress, Button, Tooltip } from 'antd';
import { 
  BookOutlined, 
  CheckCircleOutlined, 
  ClockCircleOutlined,
  ArrowRightOutlined,
  StarOutlined
} from '@ant-design/icons';
import type { ConceptNode } from '../../types';
import './ConceptCard.css';

interface ConceptCardProps {
  concept: ConceptNode;
  masteryScore?: number;
  isMastered?: boolean;
  isInProgress?: boolean;
  isRecommended?: boolean;
  onClick?: (concept: ConceptNode) => void;
  onStartLearning?: (concept: ConceptNode) => void;
  showActions?: boolean;
}

const difficultyColors: Record<string, string> = {
  beginner: 'success',
  intermediate: 'warning',
  advanced: 'error',
  expert: 'purple'
};

const difficultyLabels: Record<string, string> = {
  beginner: '初级',
  intermediate: '中级',
  advanced: '高级',
  expert: '专家'
};

const ConceptCard: React.FC<ConceptCardProps> = ({
  concept,
  masteryScore,
  isMastered = false,
  isInProgress = false,
  isRecommended = false,
  onClick,
  onStartLearning,
  showActions = true
}) => {
  return (
    <Card 
      className={`concept-card ${isMastered ? 'mastered' : ''} ${isInProgress ? 'in-progress' : ''} ${isRecommended ? 'recommended' : ''}`}
      hoverable
      onClick={() => onClick?.(concept)}
    >
      <div className="concept-header">
        <h3 className="concept-name">
          {isMastered && <CheckCircleOutlined className="status-icon mastered-icon" />}
          {isInProgress && <ClockCircleOutlined className="status-icon progress-icon" />}
          {isRecommended && <StarOutlined className="status-icon recommend-icon" />}
          {concept.name}
        </h3>
        <Space>
          <Tag color="blue">{concept.branch}</Tag>
          <Tag color={difficultyColors[concept.difficulty]}>
            {difficultyLabels[concept.difficulty]}
          </Tag>
        </Space>
      </div>

      <p className="concept-description">
        {concept.description || '暂无描述'}
      </p>

      <div className="concept-meta">
        <Space wrap>
          <Tag icon={<BookOutlined />}>
            {concept.prerequisites.length} 个先修
          </Tag>
          <Tag icon={<ArrowRightOutlined />}>
            {concept.successors.length} 个后继
          </Tag>
          <Tag>
            约 {concept.estimated_time} 分钟
          </Tag>
        </Space>
      </div>

      {masteryScore !== undefined && (
        <div className="mastery-section">
          <span>掌握度: {Math.round(masteryScore * 100)}%</span>
          <Progress 
            percent={Math.round(masteryScore * 100)} 
            size="small"
            status={masteryScore >= 0.8 ? 'success' : 'active'}
          />
        </div>
      )}

      {showActions && (
        <div className="concept-actions">
          {isMastered ? (
            <Button type="default" block size="small">
              复习巩固
            </Button>
          ) : isInProgress ? (
            <Button type="primary" block size="small">
              继续学习
            </Button>
          ) : (
            <Button 
              type="primary" 
              block 
              size="small"
              onClick={(e) => {
                e.stopPropagation();
                onStartLearning?.(concept);
              }}
            >
              开始学习
            </Button>
          )}
        </div>
      )}
    </Card>
  );
};

export default ConceptCard;
