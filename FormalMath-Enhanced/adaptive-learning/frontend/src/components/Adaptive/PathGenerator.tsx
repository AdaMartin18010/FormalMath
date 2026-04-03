import React, { useState } from 'react';
import { 
  Card, 
  Form, 
  Select, 
  Button, 
  Space, 
  Tag, 
  Alert,
  Steps,
  Checkbox,
  Radio
} from 'antd';
import { 
  RocketOutlined, 
  SettingOutlined,
  BulbOutlined
} from '@ant-design/icons';
import type { ConceptNode } from '../../types';
import './PathGenerator.css';

const { Step } = Steps;
const { Option } = Select;

interface PathGeneratorProps {
  availableConcepts: ConceptNode[];
  userId: string;
  onGenerate: (request: {
    user_id: string;
    target_concepts: string[];
    algorithm: string;
    preferences: Record<string, any>;
  }) => void;
  loading?: boolean;
}

const branches = [
  { value: '代数', label: '代数' },
  { value: '分析', label: '分析' },
  { value: '几何', label: '几何' },
  { value: '拓扑', label: '拓扑' },
  { value: '数论', label: '数论' },
  { value: '概率论', label: '概率论' },
  { value: '组合数学', label: '组合数学' },
  { value: '逻辑', label: '逻辑' }
];

const algorithms = [
  { value: 'astar', label: 'A* 算法', description: '最短路径优先' },
  { value: 'dp', label: '动态规划', description: '多目标优化' },
  { value: 'rl', label: '强化学习', description: '智能探索' }
];

const PathGenerator: React.FC<PathGeneratorProps> = ({
  availableConcepts,
  userId,
  onGenerate,
  loading = false
}) => {
  const [currentStep, setCurrentStep] = useState(0);
  const [selectedTargets, setSelectedTargets] = useState<string[]>([]);
  const [algorithm, setAlgorithm] = useState('astar');
  const [interestAreas, setInterestAreas] = useState<string[]>([]);
  const [learningPreference, setLearningPreference] = useState('balanced');

  const steps = [
    {
      title: '选择目标',
      icon: <BulbOutlined />
    },
    {
      title: '配置偏好',
      icon: <SettingOutlined />
    },
    {
      title: '生成路径',
      icon: <RocketOutlined />
    }
  ];

  const handleGenerate = () => {
    onGenerate({
      user_id: userId,
      target_concepts: selectedTargets,
      algorithm,
      preferences: {
        interest_areas: interestAreas,
        learning_preference: learningPreference
      }
    });
  };

  const nextStep = () => {
    setCurrentStep(currentStep + 1);
  };

  const prevStep = () => {
    setCurrentStep(currentStep - 1);
  };

  const renderStepContent = () => {
    switch (currentStep) {
      case 0:
        return (
          <div className="step-content">
            <Alert
              message="选择学习目标"
              description="请选择您想要学习的数学概念。系统将自动分析先修知识并生成最优学习路径。"
              type="info"
              showIcon
              style={{ marginBottom: 16 }}
            />
            <Form.Item label="目标概念">
              <Select
                mode="multiple"
                placeholder="选择要学习的概念"
                value={selectedTargets}
                onChange={setSelectedTargets}
                style={{ width: '100%' }}
                showSearch
                optionFilterProp="children"
              >
                {availableConcepts.map(concept => (
                  <Option key={concept.id} value={concept.id}>
                    <Space>
                      <span>{concept.name}</span>
                      <Tag size="small">{concept.branch}</Tag>
                      <Tag size="small" color={
                        concept.difficulty === 'beginner' ? 'success' :
                        concept.difficulty === 'intermediate' ? 'warning' :
                        concept.difficulty === 'advanced' ? 'error' : 'purple'
                      }>
                        {concept.difficulty}
                      </Tag>
                    </Space>
                  </Option>
                ))}
              </Select>
            </Form.Item>
            <div className="selected-preview">
              <span>已选择: </span>
              <Space wrap>
                {selectedTargets.map(targetId => {
                  const concept = availableConcepts.find(c => c.id === targetId);
                  return concept ? (
                    <Tag key={targetId} closable onClose={() => {
                      setSelectedTargets(selectedTargets.filter(id => id !== targetId));
                    }}>
                      {concept.name}
                    </Tag>
                  ) : null;
                })}
              </Space>
            </div>
          </div>
        );

      case 1:
        return (
          <div className="step-content">
            <Alert
              message="配置学习偏好"
              description="这些设置将帮助系统为您生成更个性化的学习路径。"
              type="info"
              showIcon
              style={{ marginBottom: 16 }}
            />
            
            <Form.Item label="学习算法">
              <Radio.Group value={algorithm} onChange={e => setAlgorithm(e.target.value)}>
                <Space direction="vertical">
                  {algorithms.map(alg => (
                    <Radio key={alg.value} value={alg.value}>
                      <Space>
                        <span>{alg.label}</span>
                        <Tag size="small" color="blue">{alg.description}</Tag>
                      </Space>
                    </Radio>
                  ))}
                </Space>
              </Radio.Group>
            </Form.Item>

            <Form.Item label="感兴趣的数学分支">
              <Checkbox.Group
                options={branches}
                value={interestAreas}
                onChange={(values) => setInterestAreas(values as string[])}
              />
            </Form.Item>

            <Form.Item label="学习偏好">
              <Radio.Group value={learningPreference} onChange={e => setLearningPreference(e.target.value)}>
                <Radio.Button value="theory_first">理论优先</Radio.Button>
                <Radio.Button value="example_first">例子优先</Radio.Button>
                <Radio.Button value="practice_first">练习优先</Radio.Button>
                <Radio.Button value="balanced">平衡模式</Radio.Button>
              </Radio.Group>
            </Form.Item>
          </div>
        );

      case 2:
        return (
          <div className="step-content">
            <Alert
              message="准备生成路径"
              description="请确认以下配置信息，然后点击生成按钮。"
              type="success"
              showIcon
              style={{ marginBottom: 16 }}
            />
            
            <Card size="small" title="配置摘要">
              <p><strong>目标概念:</strong></p>
              <Space wrap style={{ marginBottom: 16 }}>
                {selectedTargets.map(targetId => {
                  const concept = availableConcepts.find(c => c.id === targetId);
                  return concept ? (
                    <Tag key={targetId} color="blue">{concept.name}</Tag>
                  ) : null;
                })}
              </Space>
              
              <p><strong>算法:</strong> {algorithms.find(a => a.value === algorithm)?.label}</p>
              <p><strong>兴趣领域:</strong> {interestAreas.join(', ') || '未指定'}</p>
              <p><strong>学习偏好:</strong> {
                learningPreference === 'theory_first' ? '理论优先' :
                learningPreference === 'example_first' ? '例子优先' :
                learningPreference === 'practice_first' ? '练习优先' : '平衡模式'
              }</p>
            </Card>

            <Button
              type="primary"
              size="large"
              icon={<RocketOutlined />}
              onClick={handleGenerate}
              loading={loading}
              disabled={selectedTargets.length === 0}
              block
              style={{ marginTop: 16 }}
            >
              生成学习路径
            </Button>
          </div>
        );

      default:
        return null;
    }
  };

  return (
    <Card className="path-generator">
      <Steps current={currentStep} style={{ marginBottom: 24 }}>
        {steps.map(step => (
          <Step key={step.title} title={step.title} icon={step.icon} />
        ))}
      </Steps>

      {renderStepContent()}

      <div className="step-actions">
        {currentStep > 0 && (
          <Button onClick={prevStep} style={{ marginRight: 8 }}>
            上一步
          </Button>
        )}
        {currentStep < steps.length - 1 && (
          <Button 
            type="primary" 
            onClick={nextStep}
            disabled={currentStep === 0 && selectedTargets.length === 0}
          >
            下一步
          </Button>
        )}
      </div>
    </Card>
  );
};

export default PathGenerator;
