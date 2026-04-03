import { Card, Avatar, Descriptions, Tag, Timeline, Button } from 'antd'
import { 
  UserOutlined, 
  TrophyOutlined,
  FireOutlined,
  BookOutlined,
  CalendarOutlined
} from '@ant-design/icons'

// 模拟用户数据
const mockUser = {
  username: '张三',
  email: 'zhangsan@example.com',
  currentLevel: 2,
  joinDate: '2026-01-15',
  totalTests: 12,
  streak: 7,
  achievements: [
    { name: '初出茅庐', description: '完成第一次诊断', date: '2026-01-15' },
    { name: '坚持学习', description: '连续学习7天', date: '2026-03-28' },
    { name: 'L2进阶', description: '达到L2层次', date: '2026-04-01' }
  ],
  recentActivity: [
    { action: '完成诊断测试', detail: 'L2层次诊断', date: '2026-04-01' },
    { action: '完成练习', detail: '群论练习 - 10题', date: '2026-03-31' },
    { action: '学习视频', detail: 'Lagrange定理讲解', date: '2026-03-30' },
    { action: '完成诊断测试', detail: 'L1层次诊断', date: '2026-03-15' }
  ]
}

function Profile() {
  return (
    <div className="max-w-4xl mx-auto">
      {/* 用户基本信息 */}
      <Card className="mb-6">
        <div className="flex items-start gap-6">
          <Avatar size={80} icon={<UserOutlined />} className="bg-blue-500" />
          <div className="flex-1">
            <h1 className="text-2xl font-bold mb-2">{mockUser.username}</h1>
            <p className="text-gray-600 mb-4">{mockUser.email}</p>
            <div className="flex flex-wrap gap-2">
              <Tag color="blue">L{mockUser.currentLevel} 学习者</Tag>
              <Tag icon={<FireOutlined />} color="orange">连续学习 {mockUser.streak} 天</Tag>
              <Tag icon={<TrophyOutlined />} color="gold">完成 {mockUser.totalTests} 次诊断</Tag>
            </div>
          </div>
        </div>
      </Card>

      <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
        {/* 详细信息 */}
        <Card title="详细信息">
          <Descriptions column={1}>
            <Descriptions.Item label="用户名">{mockUser.username}</Descriptions.Item>
            <Descriptions.Item label="邮箱">{mockUser.email}</Descriptions.Item>
            <Descriptions.Item label="当前层次">L{mockUser.currentLevel} (定理应用层)</Descriptions.Item>
            <Descriptions.Item label="加入时间">{mockUser.joinDate}</Descriptions.Item>
            <Descriptions.Item label="诊断次数">{mockUser.totalTests} 次</Descriptions.Item>
          </Descriptions>
          <Button type="primary" className="mt-4">编辑资料</Button>
        </Card>

        {/* 成就 */}
        <Card title="成就徽章">
          <div className="grid grid-cols-3 gap-4">
            {mockUser.achievements.map((achievement) => (
              <div key={achievement.name} className="text-center p-4 bg-gray-50 rounded">
                <TrophyOutlined className="text-3xl text-yellow-500 mb-2" />
                <div className="font-medium text-sm">{achievement.name}</div>
                <div className="text-xs text-gray-500">{achievement.description}</div>
              </div>
            ))}
          </div>
        </Card>

        {/* 最近活动 */}
        <Card title="最近活动" className="lg:col-span-2">
          <Timeline>
            {mockUser.recentActivity.map((activity, index) => (
              <Timeline.Item 
                key={index}
                dot={<CalendarOutlined className="text-blue-500" />}
              >
                <div className="flex justify-between">
                  <div>
                    <span className="font-medium">{activity.action}</span>
                    <span className="text-gray-600 ml-2">- {activity.detail}</span>
                  </div>
                  <span className="text-gray-500 text-sm">{activity.date}</span>
                </div>
              </Timeline.Item>
            ))}
          </Timeline>
        </Card>
      </div>
    </div>
  )
}

export default Profile
