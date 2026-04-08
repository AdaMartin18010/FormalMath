import React, { useState, useEffect } from 'react';
import { BrowserRouter as Router, Routes, Route, Link, useLocation } from 'react-router-dom';
import { Layout, Menu, Typography, Drawer, Button } from 'antd';
import {
  HomeOutlined,
  BranchesOutlined,
  CompassOutlined,
  PlusCircleOutlined,
  MenuOutlined,
  WifiOutlined,
  DisconnectOutlined
} from '@ant-design/icons';
import Home from './pages/Home';
import Paths from './pages/Paths';
import CreatePath from './pages/CreatePath';
import Explore from './pages/Explore';
import './App.css';

const { Header, Content, Footer } = Layout;
const { Title } = Typography;

// 移动端菜单组件
const MobileMenu: React.FC<{
  visible: boolean;
  onClose: () => void;
  menuItems: any[];
  selectedKey: string;
}> = ({ visible, onClose, menuItems, selectedKey }) => {
  return (
    <Drawer
      title="菜单"
      placement="left"
      onClose={onClose}
      open={visible}
      width={280}
    >
      <Menu
        mode="vertical"
        selectedKeys={[selectedKey]}
        items={menuItems}
        onClick={onClose}
      />
    </Drawer>
  );
};

// 离线状态指示器
const OfflineIndicator: React.FC = () => {
  const [isOnline, setIsOnline] = useState(navigator.onLine);

  useEffect(() => {
    const handleOnline = () => setIsOnline(true);
    const handleOffline = () => setIsOnline(false);

    window.addEventListener('online', handleOnline);
    window.addEventListener('offline', handleOffline);

    return () => {
      window.removeEventListener('online', handleOnline);
      window.removeEventListener('offline', handleOffline);
    };
  }, []);

  if (isOnline) return null;

  return (
    <div className="offline-indicator">
      <DisconnectOutlined /> 离线模式 - 部分功能可能受限
    </div>
  );
};

// 主应用内容
const AppContent: React.FC = () => {
  const [mobileMenuVisible, setMobileMenuVisible] = useState(false);
  const location = useLocation();

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

  const showMobileMenu = () => setMobileMenuVisible(true);
  const hideMobileMenu = () => setMobileMenuVisible(false);

  return (
    <Layout className="app-layout">
      <OfflineIndicator />
      
      <Header className="app-header">
        {/* 移动端菜单按钮 */}
        <Button
          type="text"
          icon={<MenuOutlined />}
          className="mobile-menu-toggle"
          onClick={showMobileMenu}
          aria-label="打开菜单"
        />
        
        <div className="logo">
          <Link to="/">
            <Title level={4} style={{ color: 'white', margin: 0 }}>
              FormalMath
            </Title>
          </Link>
        </div>
        
        {/* 桌面端菜单 */}
        <Menu
          theme="dark"
          mode="horizontal"
          selectedKeys={[location.pathname]}
          items={menuItems}
          className="app-menu"
        />
      </Header>

      {/* 移动端菜单抽屉 */}
      <MobileMenu
        visible={mobileMenuVisible}
        onClose={hideMobileMenu}
        menuItems={menuItems}
        selectedKey={location.pathname}
      />

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
  );
};

const App: React.FC = () => {
  return (
    <Router>
      <AppContent />
    </Router>
  );
};

export default App;
