import React from 'react';
import { Card, List, Tag, Space, Button, Tooltip, Badge } from 'antd';
import { 
  BookOutlined, 
  PlayCircleOutlined, 
  ExperimentOutlined,
  EditOutlined,
  FileTextOutlined,
  SolutionOutlined,
  StarFilled
} from '@ant-design/icons';
import type { Resource, ResourceType } from '../../types';
import './ResourceList.css';

interface ResourceListProps {
  resources: Resource[];
  onResourceClick?: (resource: Resource) => void;
  title?: string;
}

const resourceIcons: Record<ResourceType, React.ReactNode> = {
  text: <BookOutlined />,
  video: <PlayCircleOutlined />,
  interactive: <ExperimentOutlined />,
  exercise: <EditOutlined />,
  proof: <FileTextOutlined />,
  example: <SolutionOutlined />
};

const resourceColors: Record<ResourceType, string> = {
  text: 'blue',
  video: 'red',
  interactive: 'purple',
  exercise: 'green',
  proof: 'orange',
  example: 'cyan'
};

const resourceLabels: Record<ResourceType, string> = {
  text: '文本',
  video: '视频',
  interactive: '交互',
  exercise: '练习',
  proof: '证明',
  example: '示例'
};

const difficultyColors: Record<string, string> = {
  beginner: 'success',
  intermediate: 'warning',
  advanced: 'error',
  expert: 'purple'
};

const ResourceList: React.FC<ResourceListProps> = ({
  resources,
  onResourceClick,
  title = '推荐资源'
}) => {
  return (
    <Card 
      title={title}
      className="resource-list-card"
    >
      <List
        itemLayout="horizontal"
        dataSource={resources}
        renderItem={(resource) => (
          <List.Item
            actions={[
              <Button 
                type="primary" 
                size="small"
                onClick={() => onResourceClick?.(resource)}
              >
                开始学习
              </Button>
            ]}
          >
            <List.Item.Meta
              avatar={
                <div className="resource-icon-wrapper">
                  {resourceIcons[resource.type]}
                </div>
              }
              title={
                <Space>
                  <span>{resource.title}</span>
                  <Tag color={resourceColors[resource.type]}>
                    {resourceLabels[resource.type]}
                  </Tag>
                  <Tag color={difficultyColors[resource.difficulty]}>
                    {resource.difficulty === 'beginner' ? '初级' :
                     resource.difficulty === 'intermediate' ? '中级' :
                     resource.difficulty === 'advanced' ? '高级' : '专家'}
                  </Tag>
                </Space>
              }
              description={
                <div className="resource-description">
                  <p>{resource.description}</p>
                  <Space wrap className="resource-meta">
                    <Tooltip title="相关度">
                      <Badge 
                        count={`${Math.round(resource.relevance_score * 100)}%`}
                        style={{ backgroundColor: '#52c41a' }}
                      />
                    </Tooltip>
                    <Tag icon={<StarFilled />} color="gold">
                      {resource.match_reason}
                    </Tag>
                    <Tag>{resource.estimated_time} 分钟</Tag>
                  </Space>
                </div>
              }
            />
          </List.Item>
        )}
      />
    </Card>
  );
};

export default ResourceList;
