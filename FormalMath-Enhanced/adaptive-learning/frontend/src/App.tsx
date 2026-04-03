import React from 'react';
import { BrowserRouter as Router, Routes, Route, Link } from 'react-router-dom';
import { Layout, Menu, Typography } from 'antd';
import {
  HomeOutlined,
  BranchesOutlined,
  CompassOutlined,
  PlusCircleOutlined
} from '@ant-design/icons';
import Home from './pages/Home';
import Paths from './pages/Paths';
import CreatePath from './pages/CreatePath';
import Explore from './pages/Explore';
import './App.css';

const { Header, Content, Footer } = Layout;
const { Title } = Typography;

const App: React.FC = () => {
  const menuItems = [
    {
      key: '/',
      icon: <HomeOutlined />,
      label: <Link to="/">首页</Link>
    },
    {
      key: '/paths',
      icon: <BranchesOutlined />,
      label: <Link to="/paths">我的路径</Link>
    },
    {
      key: '/paths/create',
      icon: <PlusCircleOutlined />,
      label: <Link to="/paths/create">创建路径</Link>
    },
    {
      key: '/explore',
      icon: <CompassOutlined />,
      label: <Link to="/explore">探索</Link>
    }
  ];

  return (
    <Router>
      <Layout className="app-layout">
        <Header className="app-header">
          <div className="logo">
            <Title level={4} style={{ color: 'white', margin: 0 }}>
              FormalMath
            </Title>
          </div>
          <Menu
            theme="dark"
            mode="horizontal"
            items={menuItems}
            className="app-menu"
          />
        </Header>

        <Content className="app-content">
          <Routes>
            <Route path="/" element={<Home />} />
            <Route path="/paths" element={<Paths />} />
            <Route path="/paths/create" element={<CreatePath />} />
            <Route path="/explore" element={<Explore />} />
          </Routes>
        </Content>

        <Footer className="app-footer">
          FormalMath 自适应学习路径系统 © 2026
        </Footer>
      </Layout>
    </Router>
  );
};

export default App;
