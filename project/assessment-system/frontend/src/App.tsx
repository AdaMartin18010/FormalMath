import React from 'react';
import { BrowserRouter as Router, Routes, Route, Link } from 'react-router-dom';
import { Layout, Menu, Typography } from 'antd';
import {
  DashboardOutlined,
  UserOutlined,
  BarChartOutlined,
  FileTextOutlined,
  MessageOutlined
} from '@ant-design/icons';

// 页面组件
import Dashboard from './pages/Dashboard';
import LearnerList from './pages/LearnerList';
import LearnerDetail from './pages/LearnerDetail';
import Evaluation from './pages/Evaluation';
import Reports from './pages/Reports';
import Feedback from './pages/Feedback';

const { Header, Sider, Content } = Layout;
const { Title } = Typography;

const App: React.FC = () => {
  return (
    <Router>
      <Layout style={{ minHeight: '100vh' }}>
        <Header style={{ background: '#001529', padding: '0 24px', display: 'flex', alignItems: 'center' }}>
          <Title level={3} style={{ color: 'white', margin: 0 }}>
            FormalMath 评估系统
          </Title>
        </Header>
        
        <Layout>
          <Sider width={200} style={{ background: '#fff' }}>
            <Menu
              mode="inline"
              defaultSelectedKeys={['dashboard']}
              style={{ height: '100%', borderRight: 0 }}
            >
              <Menu.Item key="dashboard" icon={<DashboardOutlined />}>
                <Link to="/">总览</Link>
              </Menu.Item>
              <Menu.Item key="learners" icon={<UserOutlined />}>
                <Link to="/learners">学习者管理</Link>
              </Menu.Item>
              <Menu.Item key="evaluation" icon={<BarChartOutlined />}>
                <Link to="/evaluation">评估中心</Link>
              </Menu.Item>
              <Menu.Item key="reports" icon={<FileTextOutlined />}>
                <Link to="/reports">报告中心</Link>
              </Menu.Item>
              <Menu.Item key="feedback" icon={<MessageOutlined />}>
                <Link to="/feedback">反馈管理</Link>
              </Menu.Item>
            </Menu>
          </Sider>
          
          <Layout style={{ padding: '24px' }}>
            <Content
              style={{
                background: '#fff',
                padding: 24,
                margin: 0,
                minHeight: 280,
                borderRadius: 8
              }}
            >
              <Routes>
                <Route path="/" element={<Dashboard />} />
                <Route path="/learners" element={<LearnerList />} />
                <Route path="/learners/:id" element={<LearnerDetail />} />
                <Route path="/evaluation" element={<Evaluation />} />
                <Route path="/reports" element={<Reports />} />
                <Route path="/feedback" element={<Feedback />} />
              </Routes>
            </Content>
          </Layout>
        </Layout>
      </Layout>
    </Router>
  );
};

export default App;
