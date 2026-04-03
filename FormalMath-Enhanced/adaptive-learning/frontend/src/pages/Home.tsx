import React from 'react';
import { Layout, Typography, Row, Col, Card, Button, Space } from 'antd';
import { 
  RocketOutlined, 
  BookOutlined, 
  LineChartOutlined,
  TeamOutlined
} from '@ant-design/icons';
import { useNavigate } from 'react-router-dom';
import './Home.css';

const { Content } = Layout;
const { Title, Paragraph } = Typography;

const Home: React.FC = () => {
  const navigate = useNavigate();

  const features = [
    {
      icon: <RocketOutlined className="feature-icon" />,
      title: '智能路径规划',
      description: '基于 A* 算法和动态规划，为您生成最优学习路径'
    },
    {
      icon: <BookOutlined className="feature-icon" />,
      title: '个性化推荐',
      description: '根据您的认知风格和学习偏好，推荐最适合的学习资源'
    },
    {
      icon: <LineChartOutlined className="feature-icon" />,
      title: '实时进度追踪',
      description: '随时查看学习进度，获得即时的学习建议和调整'
    },
    {
      icon: <TeamOutlined className="feature-icon" />,
      title: '知识图谱导航',
      description: '可视化的知识图谱，帮助您理解概念间的关联'
    }
  ];

  return (
    <Content className="home-content">
      {/* Hero Section */}
      <div className="hero-section">
        <Title level={1} className="hero-title">
          FormalMath 自适应学习路径系统
        </Title>
        <Paragraph className="hero-description">
          基于知识图谱和智能算法的个性化数学学习平台
        </Paragraph>
        <Space size="large">
          <Button 
            type="primary" 
            size="large"
            icon={<RocketOutlined />}
            onClick={() => navigate('/paths/create')}
          >
            开始学习
          </Button>
          <Button 
            size="large"
            onClick={() => navigate('/explore')}
          >
            探索知识图谱
          </Button>
        </Space>
      </div>

      {/* Features Section */}
      <div className="features-section">
        <Title level={2} className="section-title">核心功能</Title>
        <Row gutter={[24, 24]}>
          {features.map((feature, index) => (
            <Col xs={24} sm={12} md={6} key={index}>
              <Card className="feature-card" bordered={false}>
                {feature.icon}
                <Title level={4}>{feature.title}</Title>
                <Paragraph>{feature.description}</Paragraph>
              </Card>
            </Col>
          ))}
        </Row>
      </div>

      {/* How It Works Section */}
      <div className="how-it-works-section">
        <Title level={2} className="section-title">如何使用</Title>
        <Row gutter={[24, 24]} justify="center">
          <Col xs={24} md={8}>
            <Card className="step-card">
              <div className="step-number">1</div>
              <Title level={4}>设定目标</Title>
              <Paragraph>选择您想要学习的数学概念或领域</Paragraph>
            </Card>
          </Col>
          <Col xs={24} md={8}>
            <Card className="step-card">
              <div className="step-number">2</div>
              <Title level={4}>获取路径</Title>
              <Paragraph>系统将自动生成个性化学习路径</Paragraph>
            </Card>
          </Col>
          <Col xs={24} md={8}>
            <Card className="step-card">
              <div className="step-number">3</div>
              <Title level={4}>开始学习</Title>
              <Paragraph>按照推荐顺序学习，实时调整优化</Paragraph>
            </Card>
          </Col>
        </Row>
      </div>
    </Content>
  );
};

export default Home;
