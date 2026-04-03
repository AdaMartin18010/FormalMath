import { useParams } from 'react-router-dom'
import { Card, Row, Col, Progress, Tag, Button, Timeline, Alert, List } from 'antd'
import { 
  DownloadOutlined, 
  ShareAltOutlined,
  CheckCircleOutlined,
  ExclamationCircleOutlined,
  BookOutlined,
  TrophyOutlined
} from '@ant-design/icons'
import AbilityRadarChart from '../components/charts/AbilityRadarChart'

// 模拟诊断结果数据
const mockReport = {
  testId: 'DIAG-20260401-001',
  date: '2026年4月1日',
  overallConfidence: 0.85,
  abilityLevel: {
    L0: { score: 0.92, level: 'advanced', description: '高级' },
    L1: { score: 0.78, level: 'intermediate', description: '中级' },
    L2: { score: 0.62, level: 'developing', description: '发展中' },
    L3: { score: 0.35, level: 'beginner', description: '初学者' }
  },
  weakAreas: [
    { concept_id: 'galois_theory', concept_name: 'Galois理论', current_level: 0.25, improvement_needed: 0.45 },
    { concept_id: 'compactness', concept_name: '紧致性理论', current_level: 0.30, improvement_needed: 0.40 },
    { concept_id: 'uniform_conv', concept_name: '一致收敛', current_level: 0.35, improvement_needed: 0.35 },
    { concept_id: 'sylow', concept_name: 'Sylow定理', current_level: 0.40, improvement_needed: 0.30 },
    { concept_id: 'measure', concept_name: '测度论基础', current_level: 0.42, improvement_needed: 0.28 }
  ],
  strongAreas: [
    { concept_id: 'group_basic', concept_name: '群的基本概念', current_level: 0.95 },
    { concept_id: 'limit_theory', concept_name: '极限理论', current_level: 0.90 },
    { concept_id: 'set_theory', concept_name: '集合论基础', current_level: 0.88 }
  ],
  suggestions: [
    { 
      type: 'foundation', 
      priority: 1, 
      title: '加强基础概念学习', 
      description: '您的L0基础概念掌握度较低，建议先巩固基础知识。',
      estimated_time: '2-3周'
    },
    { 
      type: 'concept', 
      priority: 2, 
      title: '强化：Galois理论', 
      description: '该知识点掌握度为25%，需要重点提升。',
      action: '复习相关概念，完成针对性练习'
    },
    { 
      type: 'level_up', 
      priority: 5, 
      title: '向L3层次进阶', 
      description: '建议在当前层次巩固后，尝试L3层次的内容。',
      prerequisite: 'L2掌握度达到70%'
    }
  ],
  branchScores: {
    '代数': 0.75,
    '分析': 0.60,
    '拓扑': 0.55,
    '基础': 0.90
  }
}

function Report() {
  const { testId } = useParams()

  const getLevelColor = (score: number) => {
    if (score >= 0.8) return 'success'
    if (score >= 0.6) return 'processing'
    if (score >= 0.4) return 'warning'
    return 'exception'
  }

  return (
    <div className="max-w-6xl mx-auto">
      {/* 报告头部 */}
      <Card className="mb-6">
        <div className="flex justify-between items-start">
          <div>
            <h1 className="text-2xl font-bold mb-2">📊 认知诊断报告</h1>
            <p className="text-gray-600">
              诊断ID: {mockReport.testId} | 诊断日期: {mockReport.date}
            </p>
          </div>
          <div className="flex gap-2">
            <Button icon={<DownloadOutlined />}>下载PDF</Button>
            <Button icon={<ShareAltOutlined />}>分享</Button>
          </div>
        </div>
        
        <Alert
          message={`整体水平: L2 (定理应用层) | 置信度: ${(mockReport.overallConfidence * 100).toFixed(0)}%`}
          type="info"
          showIcon
          className="mt-4"
        />
      </Card>

      {/* L0-L3能力分析 */}
      <Row gutter={[16, 16]} className="mb-6">
        <Col xs={24} lg={12}>
          <Card title="能力雷达图" className="h-full">
            <AbilityRadarChart data={{
              L0: mockReport.abilityLevel.L0.score,
              L1: mockReport.abilityLevel.L1.score,
              L2: mockReport.abilityLevel.L2.score,
              L3: mockReport.abilityLevel.L3.score
            }} />
          </Card>
        </Col>
        <Col xs={24} lg={12}>
          <Card title="L0-L3 能力分析" className="h-full">
            {Object.entries(mockReport.abilityLevel).map(([level, info]) => (
              <div key={level} className="mb-4">
                <div className="flex justify-between mb-1">
                  <span className="font-medium">
                    {level} {level === 'L0' ? '基础概念' : level === 'L1' ? '定义理解' : level === 'L2' ? '定理应用' : '综合证明'}
                  </span>
                  <span className={`text-${getLevelColor(info.score)}-600`}>
                    {(info.score * 100).toFixed(0)}% ({info.description})
                  </span>
                </div>
                <Progress 
                  percent={info.score * 100} 
                  status={getLevelColor(info.score) as any}
                  showInfo={false}
                />
              </div>
            ))}
          </Card>
        </Col>
      </Row>

      {/* 知识领域分布 & 薄弱环节 */}
      <Row gutter={[16, 16]} className="mb-6">
        <Col xs={24} lg={12}>
          <Card title="知识领域分布">
            {Object.entries(mockReport.branchScores).map(([branch, score]) => (
              <div key={branch} className="mb-3">
                <div className="flex justify-between mb-1">
                  <span>{branch}</span>
                  <span>{(score * 100).toFixed(0)}%</span>
                </div>
                <Progress percent={score * 100} size="small" />
              </div>
            ))}
          </Card>
        </Col>
        <Col xs={24} lg={12}>
          <Card title="⚠️ 薄弱环节 (Top 5)">
            <Timeline>
              {mockReport.weakAreas.map((area, index) => (
                <Timeline.Item 
                  key={area.concept_id}
                  dot={<ExclamationCircleOutlined className="text-red-500" />}
                >
                  <div className="flex justify-between">
                    <span>{index + 1}. {area.concept_name}</span>
                    <Tag color="red">{(area.current_level * 100).toFixed(0)}%</Tag>
                  </div>
                </Timeline.Item>
              ))}
            </Timeline>
          </Card>
        </Col>
      </Row>

      {/* 优势领域 & 学习建议 */}
      <Row gutter={[16, 16]}>
        <Col xs={24} lg={12}>
          <Card title="✅ 优势领域">
            <List
              dataSource={mockReport.strongAreas}
              renderItem={(area) => (
                <List.Item>
                  <div className="flex justify-between w-full">
                    <span><TrophyOutlined className="text-yellow-500 mr-2" />{area.concept_name}</span>
                    <Tag color="green">{(area.current_level * 100).toFixed(0)}%</Tag>
                  </div>
                </List.Item>
              )}
            />
          </Card>
        </Col>
        <Col xs={24} lg={12}>
          <Card title="💡 个性化学习建议">
            {mockReport.suggestions.map((suggestion) => (
              <div key={suggestion.title} className="mb-4 p-3 bg-gray-50 rounded">
                <div className="flex items-center gap-2 mb-1">
                  <Tag color={suggestion.priority === 1 ? 'red' : suggestion.priority === 2 ? 'orange' : 'blue'}>
                    优先级{suggestion.priority}
                  </Tag>
                  <span className="font-medium">{suggestion.title}</span>
                </div>
                <p className="text-gray-600 text-sm">{suggestion.description}</p>
                {suggestion.estimated_time && (
                  <p className="text-gray-500 text-xs mt-1">预计用时: {suggestion.estimated_time}</p>
                )}
              </div>
            ))}
            <Button type="primary" icon={<BookOutlined />} block>
              查看完整学习路径
            </Button>
          </Card>
        </Col>
      </Row>
    </div>
  )
}

export default Report
