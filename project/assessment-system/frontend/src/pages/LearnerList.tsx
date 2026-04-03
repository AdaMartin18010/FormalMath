import React, { useState, useEffect } from 'react';
import { Table, Button, Modal, Form, Input, Tag, Space, message } from 'antd';
import { PlusOutlined, EyeOutlined } from '@ant-design/icons';
import { useNavigate } from 'react-router-dom';
import { learnerAPI } from '../services/api';

interface Learner {
  id: string;
  name: string;
  email: string;
  created_at: string;
  overall_score?: number;
  level?: string;
}

const LearnerList: React.FC = () => {
  const navigate = useNavigate();
  const [learners, setLearners] = useState<Learner[]>([]);
  const [loading, setLoading] = useState(false);
  const [modalVisible, setModalVisible] = useState(false);
  const [form] = Form.useForm();
  
  useEffect(() => {
    loadLearners();
  }, []);
  
  const loadLearners = async () => {
    setLoading(true);
    try {
      // 模拟数据，实际应从API获取
      setLearners([
        { id: '1', name: '张三', email: 'zhangsan@example.com', created_at: '2026-03-01', overall_score: 85, level: 'advanced' },
        { id: '2', name: '李四', email: 'lisi@example.com', created_at: '2026-03-05', overall_score: 72, level: 'proficient' },
        { id: '3', name: '王五', email: 'wangwu@example.com', created_at: '2026-03-10', overall_score: 58, level: 'developing' },
      ]);
    } catch (error) {
      message.error('加载学习者列表失败');
    } finally {
      setLoading(false);
    }
  };
  
  const handleCreate = async (values: any) => {
    try {
      await learnerAPI.create(values);
      message.success('学习者创建成功');
      setModalVisible(false);
      form.resetFields();
      loadLearners();
    } catch (error) {
      message.error('创建失败');
    }
  };
  
  const getLevelTag = (level: string) => {
    const colors: Record<string, string> = {
      expert: 'gold',
      advanced: 'green',
      proficient: 'blue',
      developing: 'orange',
      beginner: 'default'
    };
    const names: Record<string, string> = {
      expert: '专家',
      advanced: '高级',
      proficient: '熟练',
      developing: '发展中',
      beginner: '初级'
    };
    return <Tag color={colors[level] || 'default'}>{names[level] || level}</Tag>;
  };
  
  const columns = [
    {
      title: '姓名',
      dataIndex: 'name',
      key: 'name',
    },
    {
      title: '邮箱',
      dataIndex: 'email',
      key: 'email',
    },
    {
      title: '综合得分',
      dataIndex: 'overall_score',
      key: 'overall_score',
      render: (score: number) => score ? `${score}分` : '-',
    },
    {
      title: '等级',
      dataIndex: 'level',
      key: 'level',
      render: (level: string) => level ? getLevelTag(level) : '-',
    },
    {
      title: '创建时间',
      dataIndex: 'created_at',
      key: 'created_at',
    },
    {
      title: '操作',
      key: 'action',
      render: (_: any, record: Learner) => (
        <Space>
          <Button 
            type="primary" 
            icon={<EyeOutlined />}
            onClick={() => navigate(`/learners/${record.id}`)}
          >
            详情
          </Button>
        </Space>
      ),
    },
  ];
  
  return (
    <div>
      <div style={{ display: 'flex', justifyContent: 'space-between', marginBottom: 16 }}>
        <h1>学习者管理</h1>
        <Button 
          type="primary" 
          icon={<PlusOutlined />}
          onClick={() => setModalVisible(true)}
        >
          添加学习者
        </Button>
      </div>
      
      <Table
        columns={columns}
        dataSource={learners}
        rowKey="id"
        loading={loading}
      />
      
      <Modal
        title="添加学习者"
        visible={modalVisible}
        onCancel={() => setModalVisible(false)}
        onOk={() => form.submit()}
      >
        <Form form={form} onFinish={handleCreate} layout="vertical">
          <Form.Item
            name="name"
            label="姓名"
            rules={[{ required: true, message: '请输入姓名' }]}
          >
            <Input />
          </Form.Item>
          <Form.Item
            name="email"
            label="邮箱"
            rules={[{ type: 'email', message: '请输入有效的邮箱' }]}
          >
            <Input />
          </Form.Item>
        </Form>
      </Modal>
    </div>
  );
};

export default LearnerList;
