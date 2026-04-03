import React, { useState } from 'react';
import { Card, Form, Input, Select, Button, Slider, message, Tabs, Radio } from 'antd';
import { evaluationAPI } from '../services/api';

const { TabPane } = Tabs;
const { Option } = Select;

const Evaluation: React.FC = () => {
  const [form] = Form.useForm();
  const [loading, setLoading] = useState(false);
  const [result, setResult] = useState<any>(null);
  
  const handleComprehensiveEval = async (values: any) => {
    setLoading(true);
    try {
      const data = {
        learner_id: values.learner_id,
        assessment_type: 'comprehensive',
        scores: {
          knowledge: {
            concept_understanding: values.concept_understanding || 0,
            theorem_mastery: values.theorem_mastery || 0,
            method_proficiency: values.method_proficiency || 0
          },
          skill: {
            calculation: values.calculation || 0,
            proof: values.proof || 0,
            modeling: values.modeling || 0
          },
          problem_solving: {
            problem_analysis: values.problem_analysis || 0,
            strategy_selection: values.strategy_selection || 0,
            execution_verification: values.execution_verification || 0
          },
          creative: {
            divergent_thinking: values.divergent_thinking || 0,
            creativity: values.creativity || 0,
            critical_thinking: values.critical_thinking || 0
          }
        }
      };
      
      // const response = await evaluationAPI.comprehensive(data);
      // setResult(response.data);
      
      // 模拟结果
      setResult({
        overall_score: 78.5,
        level: 'proficient',
        dimension_scores: {
          knowledge_mastery: { score: 80 },
          skill_proficiency: { score: 75 },
          problem_solving: { score: 82 },
          creative_thinking: { score: 77 }
        },
        feedback: [
          { title: '综合评价', content: '整体表现良好', priority: 'low' }
        ]
      });
      
      message.success('评估完成');
    } catch (error) {
      message.error('评估失败');
    } finally {
      setLoading(false);
    }
  };
  
  const getLevelText = (level: string) => {
    const levels: Record<string, string> = {
      expert: '专家',
      advanced: '高级',
      proficient: '熟练',
      developing: '发展中',
      beginner: '初级'
    };
    return levels[level] || level;
  };
  
  return (
    <div>
      <h1>评估中心</h1>
      
      <Tabs defaultActiveKey="comprehensive">
        <TabPane tab="综合评价" key="comprehensive">
          <Card title="四维能力评价">
            <Form form={form} onFinish={handleComprehensiveEval} layout="vertical">
              <Form.Item
                name="learner_id"
                label="学习者ID"
                rules={[{ required: true }]}
              >
                <Input placeholder="输入学习者ID" />
              </Form.Item>
              
              <h3>知识掌握度</h3>
              <Form.Item name="concept_understanding" label="概念理解">
                <Slider min={0} max={100} marks={{ 0: '0', 50: '50', 100: '100' }} />
              </Form.Item>
              <Form.Item name="theorem_mastery" label="定理掌握">
                <Slider min={0} max={100} marks={{ 0: '0', 50: '50', 100: '100' }} />
              </Form.Item>
              <Form.Item name="method_proficiency" label="方法熟练">
                <Slider min={0} max={100} marks={{ 0: '0', 50: '50', 100: '100' }} />
              </Form.Item>
              
              <h3>技能熟练度</h3>
              <Form.Item name="calculation" label="计算能力">
                <Slider min={0} max={100} marks={{ 0: '0', 50: '50', 100: '100' }} />
              </Form.Item>
              <Form.Item name="proof" label="证明能力">
                <Slider min={0} max={100} marks={{ 0: '0', 50: '50', 100: '100' }} />
              </Form.Item>
              
              <h3>问题解决能力</h3>
              <Form.Item name="problem_analysis" label="问题分析">
                <Slider min={0} max={100} marks={{ 0: '0', 50: '50', 100: '100' }} />
              </Form.Item>
              <Form.Item name="strategy_selection" label="策略选择">
                <Slider min={0} max={100} marks={{ 0: '0', 50: '50', 100: '100' }} />
              </Form.Item>
              
              <Form.Item>
                <Button type="primary" htmlType="submit" loading={loading}>
                  提交评估
                </Button>
              </Form.Item>
            </Form>
          </Card>
          
          {result && (
            <Card title="评估结果" style={{ marginTop: 16 }}>
              <h2>综合得分: {result.overall_score} 分</h2>
              <p>等级: {getLevelText(result.level)}</p>
              
              <h4>各维度得分:</h4>
              <ul>
                {Object.entries(result.dimension_scores).map(([key, value]: [string, any]) => (
                  <li key={key}>{key}: {value.score} 分</li>
                ))}
              </ul>
            </Card>
          )}
        </TabPane>
        
        <TabPane tab="过程性评价" key="process">
          <Card title="过程性评价">
            <Form layout="vertical">
              <Form.Item label="学习者ID" required>
                <Input placeholder="输入学习者ID" />
              </Form.Item>
              <Form.Item label="评价周期">
                <Radio.Group defaultValue={7}>
                  <Radio.Button value={7}>最近7天</Radio.Button>
                  <Radio.Button value={30}>最近30天</Radio.Button>
                </Radio.Group>
              </Form.Item>
              <Form.Item>
                <Button type="primary">开始评价</Button>
              </Form.Item>
            </Form>
          </Card>
        </TabPane>
        
        <TabPane tab="增值评价" key="value-added">
          <Card title="增值评价">
            <p>对比期初和期末数据，计算学习增值</p>
            <Form layout="vertical">
              <Form.Item label="学习者ID" required>
                <Input placeholder="输入学习者ID" />
              </Form.Item>
              <Form.Item label="评价周期">
                <Radio.Group defaultValue={30}>
                  <Radio.Button value={30}>最近30天</Radio.Button>
                  <Radio.Button value={90}>最近90天</Radio.Button>
                </Radio.Group>
              </Form.Item>
              <Form.Item>
                <Button type="primary">计算增值</Button>
              </Form.Item>
            </Form>
          </Card>
        </TabPane>
      </Tabs>
    </div>
  );
};

export default Evaluation;
