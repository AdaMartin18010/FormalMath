import React, { useState, useEffect } from 'react';
import { Layout, Typography, Input, Row, Col, Card, Tag, Spin, Empty, Tree } from 'antd';
import { SearchOutlined, BranchesOutlined } from '@ant-design/icons';
import { adaptiveApi } from '../api/adaptiveApi';
import { ConceptCard } from '../components/Adaptive';
import type { ConceptNode, ConceptGraph } from '../types';
import './Explore.css';

const { Content } = Layout;
const { Title } = Typography;
const { Search } = Input;

const Explore: React.FC = () => {
  const [concepts, setConcepts] = useState<ConceptNode[]>([]);
  const [graph, setGraph] = useState<ConceptGraph | null>(null);
  const [loading, setLoading] = useState(true);
  const [searchQuery, setSearchQuery] = useState('');
  const [selectedBranch, setSelectedBranch] = useState<string | null>(null);

  useEffect(() => {
    fetchData();
  }, []);

  const fetchData = async () => {
    try {
      setLoading(true);
      const [conceptsResult, graphResult] = await Promise.all([
        adaptiveApi.searchConcepts('', { limit: 200 }),
        adaptiveApi.getConceptGraph()
      ]);
      setConcepts(conceptsResult.concepts);
      setGraph(graphResult);
    } catch (error) {
      console.error('获取数据失败:', error);
    } finally {
      setLoading(false);
    }
  };

  const handleSearch = async (value: string) => {
    if (!value.trim()) {
      const result = await adaptiveApi.searchConcepts('', { limit: 100 });
      setConcepts(result.concepts);
      return;
    }
    
    const result = await adaptiveApi.searchConcepts(value, { limit: 50 });
    setConcepts(result.concepts);
  };

  // 构建树形结构
  const buildTreeData = () => {
    if (!graph) return [];
    
    const branchMap = new Map<string, ConceptNode[]>();
    
    graph.nodes.forEach(node => {
      if (!branchMap.has(node.branch)) {
        branchMap.set(node.branch, []);
      }
      const concept = concepts.find(c => c.id === node.id);
      if (concept) {
        branchMap.get(node.branch)!.push(concept);
      }
    });

    return Array.from(branchMap.entries()).map(([branch, branchConcepts]) => ({
      title: branch,
      key: branch,
      icon: <BranchesOutlined />,
      children: branchConcepts.map(c => ({
        title: c.name,
        key: c.id,
        isLeaf: true
      }))
    }));
  };

  const filteredConcepts = concepts.filter(c => {
    if (selectedBranch && c.branch !== selectedBranch) return false;
    return true;
  });

  // 获取所有分支
  const branches = Array.from(new Set(concepts.map(c => c.branch)));

  if (loading) {
    return (
      <Content className="explore-content">
        <div className="loading-container">
          <Spin size="large" />
        </div>
      </Content>
    );
  }

  return (
    <Content className="explore-content">
      <Title level={2}>探索知识图谱</Title>
      
      <Row gutter={[24, 24]}>
        <Col xs={24} lg={6}>
          <Card title="数学分支" className="branch-card">
            <Search
              placeholder="搜索概念..."
              allowClear
              enterButton={<SearchOutlined />}
              onSearch={handleSearch}
              onChange={(e) => setSearchQuery(e.target.value)}
              style={{ marginBottom: 16 }}
            />
            
            <div className="branch-tags">
              <Tag 
                color={!selectedBranch ? 'blue' : 'default'}
                onClick={() => setSelectedBranch(null)}
                style={{ cursor: 'pointer', marginBottom: 8 }}
              >
                全部
              </Tag>
              {branches.map(branch => (
                <Tag
                  key={branch}
                  color={selectedBranch === branch ? 'blue' : 'default'}
                  onClick={() => setSelectedBranch(branch)}
                  style={{ cursor: 'pointer', marginBottom: 8 }}
                >
                  {branch}
                </Tag>
              ))}
            </div>

            <Tree
              treeData={buildTreeData()}
              onSelect={(keys) => {
                if (keys.length > 0) {
                  const key = keys[0] as string;
                  if (!branches.includes(key)) {
                    // 选中的是概念
                    const concept = concepts.find(c => c.id === key);
                    if (concept) {
                      console.log('Selected concept:', concept);
                    }
                  }
                }
              }}
            />
          </Card>
        </Col>

        <Col xs={24} lg={18}>
          <Card 
            title={`概念列表 (${filteredConcepts.length})`}
            className="concepts-card"
          >
            {filteredConcepts.length === 0 ? (
              <Empty description="没有找到相关概念" />
            ) : (
              <Row gutter={[16, 16]}>
                {filteredConcepts.map(concept => (
                  <Col xs={24} sm={12} md={8} key={concept.id}>
                    <ConceptCard
                      concept={concept}
                      showActions={false}
                    />
                  </Col>
                ))}
              </Row>
            )}
          </Card>
        </Col>
      </Row>
    </Content>
  );
};

export default Explore;
