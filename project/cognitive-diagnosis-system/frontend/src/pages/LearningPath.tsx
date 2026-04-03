import { Card, Steps, Button, Tag, Progress, Timeline } from 'antd'
import { 
  CheckCircleOutlined, 
  ClockCircleOutlined,
  PlayCircleOutlined,
  BookOutlined
} from '@ant-design/icons'

const { Step } = Steps

// 模拟学习路径数据
const mockPath = {
  currentNode: 'node-2',
  progress: 0.35,
  nodes: [
    {
      id: 'node-1',
      title: '子群理论',
      concept: 'subgroup',
      estimatedTime: '2小时',
      prerequisites: [],
      status: 'completed',
      resources: ['视频讲解', '阅读材料', '练习题']
    },
    {
      id: 'node-2',
      title: 'Lagrange定理',
      concept: 'lagrange',
      estimatedTime: '3小时',
      prerequisites: ['node-1'],
      status: 'in_progress',
      resources: ['视频讲解', '证明详解', '应用例题']
    },
    {
      id: 'node-3',
      title: '正规子群与商群',
      concept: 'normal_subgroup',
      estimatedTime: '3小时',
      prerequisites: ['node-2'],
      status: 'pending',
      resources: ['视频讲解', '阅读材料']
    },
    {
      id: 'node-4',
      title: '同态基本定理',
      concept: 'homomorphism_theorem',
      estimatedTime: '4小时',
      prerequisites: ['node-3'],
      status: 'pending',
      resources: ['视频讲解', '证明详解']
    },
    {
      id: 'node-5',
      title: '群作用理论',
      concept: 'group_action',
      estimatedTime: '4小时',
      prerequisites: ['node-2'],
      status: 'pending',
      resources: ['视频讲解', '应用案例']
    }
  ]
}

function LearningPath() {
  return (
    <div className="max-w-6xl mx-auto">
      <Card className="mb-6">
        <h1 className="text-2xl font-bold mb-4">🎯 个性化学习路径</h1>
        <p className="text-gray-600 mb-4">
          基于您的诊断结果，我们为您规划了以下学习路径。
        </p>
        <div className="flex items-center gap-4">
          <Progress percent={mockPath.progress * 100} className="flex-1" />
          <span className="text-gray-600">{(mockPath.progress * 100).toFixed(0)}% 完成</span>
        </div>
      </Card>

      <div className="grid grid-cols-1 lg:grid-cols-3 gap-6">
        {/* 学习路径可视化 */}
        <Card className="lg:col-span-2" title="学习路径">
          <Timeline mode="left">
            {mockPath.nodes.map((node) => (
              <Timeline.Item
                key={node.id}
                dot={
                  node.status === 'completed' ? (
                    <CheckCircleOutlined className="text-green-500 text-lg" />
                  ) : node.status === 'in_progress' ? (
                    <PlayCircleOutlined className="text-blue-500 text-lg" />
                  ) : (
                    <ClockCircleOutlined className="text-gray-400 text-lg" />
                  )
                }
                label={
                  <Tag color={
                    node.status === 'completed' ? 'success' : 
                    node.status === 'in_progress' ? 'processing' : 'default'
                  }>
                    {node.status === 'completed' ? '已完成' : 
                     node.status === 'in_progress' ? '进行中' : '待开始'}
                  </Tag>
                }
              >
                <div className={`p-3 rounded ${node.status === 'in_progress' ? 'bg-blue-50 border border-blue-200' : 'bg-gray-50'}`}>
                  <h3 className="font-medium mb-2">{node.title}</h3>
                  <div className="flex items-center gap-2 text-sm text-gray-500 mb-2">
                    <ClockCircleOutlined />
                    <span>预计用时: {node.estimatedTime}</span>
                  </div>
                  <div className="flex flex-wrap gap-1">
                    {node.resources.map((resource) => (
                      <Tag key={resource} size="small">{resource}</Tag>
                    ))}
                  </div>
                  {node.status === 'in_progress' && (
                    <Button type="primary" size="small" className="mt-2" icon={<BookOutlined />}>
                      继续学习
                    </Button>
                  )}
                  {node.status === 'pending' && (
                    <Button size="small" className="mt-2" disabled>
                      等待解锁
                    </Button>
                  )}
                </div>
              </Timeline.Item>
            ))}
          </Timeline>
        </Card>

        {/* 学习统计 */}
        <Card title="学习统计">
          <div className="space-y-4">
            <div className="p-3 bg-green-50 rounded">
              <div className="text-2xl font-bold text-green-600">1</div>
              <div className="text-sm text-gray-600">已完成节点</div>
            </div>
            <div className="p-3 bg-blue-50 rounded">
              <div className="text-2xl font-bold text-blue-600">1</div>
              <div className="text-sm text-gray-600">进行中节点</div>
            </div>
            <div className="p-3 bg-gray-50 rounded">
              <div className="text-2xl font-bold text-gray-600">3</div>
              <div className="text-sm text-gray-600">待开始节点</div>
            </div>
            <div className="p-3 bg-purple-50 rounded">
              <div className="text-2xl font-bold text-purple-600">16小时</div>
              <div className="text-sm text-gray-600">预计总用时</div>
            </div>
          </div>
        </Card>
      </div>
    </div>
  )
}

export default LearningPath
