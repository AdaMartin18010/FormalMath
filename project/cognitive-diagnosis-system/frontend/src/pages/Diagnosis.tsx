import { useState } from 'react'
import { Card, Button, Progress, Radio, Input, Space, Tag, Typography, Result } from 'antd'
import { 
  ClockCircleOutlined, 
  CheckCircleOutlined,
  LeftOutlined,
  RightOutlined,
  FlagOutlined,
  FireOutlined
} from '@ant-design/icons'
import { Link } from 'react-router-dom'

const { Title, Text } = Typography
const { TextArea } = Input

// 模拟题目数据
const mockQuestions = [
  {
    id: 'Q001',
    content: '下列哪个集合与运算构成群？',
    type: 'SC',
    level: 0,
    difficulty: 1,
    branch: '代数学',
    options: {
      A: '自然数集 ℕ 与加法运算',
      B: '整数集 ℤ 与加法运算',
      C: '整数集 ℤ 与乘法运算',
      D: '偶数集 2ℤ 与乘法运算'
    },
    time_estimate: 60
  },
  {
    id: 'Q002',
    content: '数列极限 lim(n→∞) aₙ = a 的直观含义是什么？',
    type: 'SC',
    level: 0,
    difficulty: 1,
    branch: '分析学',
    options: {
      A: '数列的项最终会等于a',
      B: '数列的项会无限接近a',
      C: '数列的每一项都小于a',
      D: '数列单调递减趋向a'
    },
    time_estimate: 60
  },
  {
    id: 'Q003',
    content: '用自己的话解释什么是群同态(group homomorphism)。',
    type: 'SA',
    level: 0,
    difficulty: 2,
    branch: '代数学',
    time_estimate: 120
  }
]

function Diagnosis() {
  const [started, setStarted] = useState(false)
  const [currentIndex, setCurrentIndex] = useState(0)
  const [answers, setAnswers] = useState<Record<string, string>>({})
  const [completed, setCompleted] = useState(false)

  const currentQuestion = mockQuestions[currentIndex]
  const progress = ((currentIndex + 1) / mockQuestions.length) * 100

  const handleAnswer = (value: string) => {
    setAnswers({ ...answers, [currentQuestion.id]: value })
  }

  const handleNext = () => {
    if (currentIndex < mockQuestions.length - 1) {
      setCurrentIndex(currentIndex + 1)
    } else {
      setCompleted(true)
    }
  }

  const handlePrev = () => {
    if (currentIndex > 0) {
      setCurrentIndex(currentIndex - 1)
    }
  }

  // 开始页面
  if (!started) {
    return (
      <div className="max-w-3xl mx-auto py-12">
        <Card className="text-center">
          <FireOutlined className="text-6xl text-orange-500 mb-6" />
          <Title level={2}>认知诊断测试</Title>
          <Text className="text-gray-600 block mb-8">
            通过本次测试，我们将评估您在L0-L3四个层次的能力水平，<br />
            并为您生成个性化的学习建议。
          </Text>
          
          <div className="grid grid-cols-3 gap-4 mb-8 text-left">
            <Card size="small" className="bg-blue-50">
              <div className="text-2xl font-bold text-blue-600">{mockQuestions.length}</div>
              <div className="text-sm text-gray-600">题目数量</div>
            </Card>
            <Card size="small" className="bg-green-50">
              <div className="text-2xl font-bold text-green-600">15</div>
              <div className="text-sm text-gray-600">预估用时(分钟)</div>
            </Card>
            <Card size="small" className="bg-purple-50">
              <div className="text-2xl font-bold text-purple-600">L0-L3</div>
              <div className="text-sm text-gray-600">测试层次</div>
            </Card>
          </div>

          <Button type="primary" size="large" onClick={() => setStarted(true)}>
            开始测试
          </Button>
        </Card>
      </div>
    )
  }

  // 完成页面
  if (completed) {
    return (
      <div className="max-w-2xl mx-auto py-12">
        <Result
          status="success"
          title="测试完成!"
          subTitle="您的答案已提交，正在生成诊断报告..."
          extra={[
            <Link to="/report/test-001" key="report">
              <Button type="primary">查看诊断报告</Button>
            </Link>,
            <Link to="/" key="home">
              <Button>返回首页</Button>
            </Link>
          ]}
        />
      </div>
    )
  }

  // 测试页面
  return (
    <div className="max-w-4xl mx-auto">
      {/* 进度条 */}
      <Card className="mb-4">
        <div className="flex items-center justify-between mb-2">
          <span className="text-gray-600">
            题目 {currentIndex + 1} / {mockQuestions.length}
          </span>
          <span className="text-gray-600 flex items-center gap-2">
            <ClockCircleOutlined />
            15:32
          </span>
        </div>
        <Progress percent={progress} showInfo={false} strokeColor="#1890ff" />
      </Card>

      {/* 题目卡片 */}
      <Card>
        {/* 题目信息 */}
        <div className="flex items-center gap-2 mb-4">
          <Tag color="blue">L{currentQuestion.level}</Tag>
          <Tag color="cyan">{currentQuestion.branch}</Tag>
          <Tag>难度: {'★'.repeat(currentQuestion.difficulty)}{'☆'.repeat(5 - currentQuestion.difficulty)}</Tag>
        </div>

        {/* 题目内容 */}
        <Title level={4} className="mb-6">
          {currentQuestion.content}
        </Title>

        {/* 答题区 */}
        <div className="mb-6">
          {currentQuestion.type === 'SC' && currentQuestion.options && (
            <Radio.Group 
              onChange={(e) => handleAnswer(e.target.value)}
              value={answers[currentQuestion.id]}
              className="w-full"
            >
              <Space direction="vertical" className="w-full">
                {Object.entries(currentQuestion.options).map(([key, value]) => (
                  <Radio key={key} value={key} className="p-3 border rounded hover:bg-gray-50 w-full">
                    {key}. {value}
                  </Radio>
                ))}
              </Space>
            </Radio.Group>
          )}

          {currentQuestion.type === 'SA' && (
            <TextArea
              rows={6}
              placeholder="请输入您的答案..."
              value={answers[currentQuestion.id] || ''}
              onChange={(e) => handleAnswer(e.target.value)}
            />
          )}
        </div>

        {/* 操作按钮 */}
        <div className="flex justify-between">
          <Button 
            icon={<LeftOutlined />}
            disabled={currentIndex === 0}
            onClick={handlePrev}
          >
            上一题
          </Button>
          
          <Space>
            <Button icon={<FlagOutlined />}>标记</Button>
            <Button 
              type="primary"
              icon={currentIndex === mockQuestions.length - 1 ? <CheckCircleOutlined /> : <RightOutlined />}
              onClick={handleNext}
            >
              {currentIndex === mockQuestions.length - 1 ? '提交' : '下一题'}
            </Button>
          </Space>
        </div>
      </Card>
    </div>
  )
}

export default Diagnosis
