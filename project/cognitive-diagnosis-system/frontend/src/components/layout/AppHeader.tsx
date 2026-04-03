import { Link, useLocation } from 'react-router-dom'
import { Layout, Menu, Avatar, Badge } from 'antd'
import { 
  DashboardOutlined, 
  CheckCircleOutlined, 
  FileTextOutlined, 
  PartitionOutlined,
  UserOutlined 
} from '@ant-design/icons'

const { Header } = Layout

const menuItems = [
  { key: '/', icon: <DashboardOutlined />, label: <Link to="/">仪表盘</Link> },
  { key: '/diagnosis', icon: <CheckCircleOutlined />, label: <Link to="/diagnosis">诊断测试</Link> },
  { key: '/report', icon: <FileTextOutlined />, label: <Link to="/report">诊断报告</Link> },
  { key: '/learning-path', icon: <PartitionOutlined />, label: <Link to="/learning-path">学习路径</Link> },
  { key: '/profile', icon: <UserOutlined />, label: <Link to="/profile">个人中心</Link> },
]

function AppHeader() {
  const location = useLocation()

  return (
    <Header className="bg-white shadow-sm flex items-center justify-between px-6 sticky top-0 z-50">
      <div className="flex items-center">
        <div className="text-xl font-bold mr-8 text-blue-600">
          FormalMath CDS
        </div>
        <Menu
          mode="horizontal"
          selectedKeys={[location.pathname]}
          items={menuItems}
          className="border-b-0 min-w-[400px]"
        />
      </div>
      <div className="flex items-center gap-4">
        <Badge count={5} size="small">
          <span className="cursor-pointer text-gray-600">通知</span>
        </Badge>
        <Avatar icon={<UserOutlined />} className="bg-blue-500" />
      </div>
    </Header>
  )
}

export default AppHeader
