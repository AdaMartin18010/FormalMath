import { useState, useEffect } from 'react'
import { Row, Col, Card, Statistic, Button, Progress, List, Tag } from 'antd'
import { 
  ArrowUpOutlined, 
  BookOutlined, 
  TrophyOutlined,
  FireOutlined,
  RightOutlined
} from '@ant-design/icons'
import { Link } from 'react-router-dom'
import AbilityRadarChart from '../components/charts/AbilityRadarChart'

// 模拟数据
const mockStats = {
  totalTests: 12,
  currentLevel: 'L2',
  masteryRate: 0.68,
  streak: 7
}

const mockAbility = {
  L0: 0.92,
  L1: 0.78,
  L2: 0.62,
  L3: 0.35
}

const mockRecommendations = [
  {
    title: '复习群同态理论',
    type: '概念强化',
    priority: 'high',
    description: '您的群同态掌握度为45%，建议重点复习'
  },
  {
    title: 'Lagrange定理应用练习',
    type: '习题训练',
    priority: 'medium',
    description: '完成5道相关练习题'
  },
  {
    title: '阅读《代数学引论》第三章',
    type: '阅读',
    priority: 'low',
    description: '建议配合视频学习'
  }
]

function Dashboard() {
  const [loading, setLoading] = useState(false)

  return (
    <div className="max-w-7xl mx-auto">
      {/* 欢迎区域 */}
      <div className="mb-6">
        <h1 className="text-2xl font-bold text-gray-800">欢迎回来! 👋</h1>
        <p className="text-gray-600 mt-1">继续您的数学学习之旅</p>
      </div>

      {/* 统计卡片 */}
      <Row gutter={[16, 16]} className="mb-6">
        <Col xs={24} sm={12} lg={6}>
          <Card className="card-hover">
            <Statistic
              title="已完成诊断"
              value={mockStats.totalTests}
              prefix={<TrophyOutlined className="text-yellow-500" />}
              suffix="次"
            />
          </Card>
        </Col>
        <Col xs={24} sm={12} lg={6}>
          <Card className="card-hover">
            <Statistic
              title="当前层次"
              value={mockStats.currentLevel}
              valueStyle={{ color: '#1890ff' }}
            />
            <div className="text-xs text-gray-500 mt-1">中级应用层</div>
          </Card>
        </Col>
        <Col xs={24} sm={12} lg={6}>
          <Card className="card-hover">
            <Statistic
              title="整体掌握度"
              value={mockStats.masteryRate * 100}
              precision={1}
              suffix="%"
              prefix={<ArrowUpOutlined className="text-green-500" />}
            />
            <Progress percent={68} size="small" className="mt-2" />
          </Card>
        </Col>
        <Col xs={24} sm={12} lg={6}>
          <Card className="card-hover">
            <Statistic
              title="学习连续"
              value={mockStats.streak}
              suffix="天"
              prefix={<FireOutlined className="text-red-500" />}
            />
            <div className="text-xs text-green-600 mt-1">继续保持!</div>
          </Card>
        </Col>
      </Row>

      {/* 主内容区 */}
      <Row gutter={[16, 16]}>
        {/* 能力雷达图 */}
        <Col xs={24} lg={12}>
          <Card title="能力分析" className="h-full">
            <AbilityRadarChart data={mockAbility} />
            <div className="mt-4 grid grid-cols-4 gap-2 text-center">
              {Object.entries(mockAbility).map(([level, score]) => (
                <div key={level} className="p-2 bg-gray-50 rounded">
                  <div className="text-xs text-gray-500">{level}</div>
                  <div className={`font-bold ${score >= 0.8 ? 'text-green-600' : score >= 0.6 ? 'text-blue-600' : 'text-orange-600'}`}>
                    {(score * 100).toFixed(0)}%
                  </div>
                </div>
              ))}
            </div>
          </Card>
        </Col>

        {/* 今日推荐 */}
        <Col xs={24} lg={12}>
          <Card 
            title="今日学习推荐" 
            className="h-full"
            extra={<Link to="/learning-path">查看全部 <RightOutlined /></Link>}
          >
            <List
              dataSource={mockRecommendations}
              renderItem={(item) => (
                <List.Item>
                  <List.Item.Meta
                    title={
                      <div className="flex items-center gap-2">
                        <span>{item.title}</span>
                        <Tag color={
                          item.priority === 'high' ? 'red' : 
                          item.priority === 'medium' ? 'orange' : 'blue'
                        }>
                          {item.type}
                        </Tag>
                      </div>
                    }
                    description={item.description}
                  />
                </List.Item>
              )}
            />
            <Button type="primary" block icon={<BookOutlined />} className="mt-4">
              开始学习
            </Button>
          </Card>
        </Col>
      </Row>

      {/* 快速操作 */}
      <Card className="mt-6" title="快速操作">
        <div className="flex gap-4 flex-wrap">
          <Link to="/diagnosis">
            <Button type="primary" size="large" icon={<CheckCircleOutlined />}>
              开始诊断测试
            </Button>
          </Link>
          <Link to="/report">
            <Button size="large" icon={<FileTextOutlined />}>
              查看最近报告
            </Button>
          </Link>
        </div>
      </Card>
    </div>
  )
}

export default Dashboard
