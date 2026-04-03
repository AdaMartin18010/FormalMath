import React, { useState } from 'react';
import { Card, Table, Button, Form, Select, Input, DatePicker, message, Tag } from 'antd';
import { FileTextOutlined, DownloadOutlined } from '@ant-design/icons';
import { reportAPI } from '../services/api';

const { Option } = Select;
const { RangePicker } = DatePicker;

const Reports: React.FC = () => {
  const [reports, setReports] = useState<any[]>([]);
  const [loading, setLoading] = useState(false);
  const [form] = Form.useForm();
  
  // 模拟报告数据
  const mockReports = [
    { id: '1', type: 'personal_learning', title: '张三 - 月度学习报告', created_at: '2026-04-01', status: 'completed' },
    { id: '2', type: 'ability', title: '李四 - 能力评估报告', created_at: '2026-03-28', status: 'completed' },
    { id: '3', type: 'group_analysis', title: '高一(3)班 - 群体分析报告', created_at: '2026-03-25', status: 'completed' },
  ];
  
  const handleGenerate = async (values: any) => {
    setLoading(true);
    try {
      message.success('报告生成任务已提交');
    } catch (error) {
      message.error('生成失败');
    } finally {
      setLoading(false);
    }
  };
  
  const getTypeTag = (type: string) => {
    const typeMap: Record<string, { text: string; color: string }> = {
      personal_learning: { text: '个人学习', color: 'blue' },
      ability: { text: '能力评估', color: 'green' },
      group_analysis: { text: '群体分析', color: 'purple' },
      value_added: { text: '增值评价', color: 'orange' },
    };
    const config = typeMap[type] || { text: type, color: 'default' };
    return <Tag color={config.color}>{config.text}</Tag>;
  };
  
  const columns = [
    {
      title: '报告类型',
      dataIndex: 'type',
      key: 'type',
      render: (type: string) => getTypeTag(type),
    },
    {
      title: '标题',
      dataIndex: 'title',
      key: 'title',
    },
    {
      title: '生成时间',
      dataIndex: 'created_at',
      key: 'created_at',
    },
    {
      title: '状态',
      dataIndex: 'status',
      key: 'status',
      render: (status: string) => (
        <Tag color={status === 'completed' ? 'success' : 'processing'}>
          {status === 'completed' ? '已完成' : '生成中'}
        </Tag>
      ),
    },
    {
      title: '操作',
      key: 'action',
      render: (_: any, record: any) => (
        <Button icon={<DownloadOutlined />}>下载</Button>
      ),
    },
  ];
  
  return (
    <div>
      <h1>报告中心</h1>
      
      <Card title="生成新报告" style={{ marginBottom: 24 }}>
        <Form form={form} onFinish={handleGenerate} layout="inline">
          <Form.Item name="report_type" label="报告类型" rules={[{ required: true }]}>
            <Select style={{ width: 200 }} placeholder="选择报告类型">
              <Option value="personal_learning">个人学习报告</Option>
              <Option value="ability">能力评估报告</Option>
              <Option value="value_added">增值评价报告</Option>
              <Option value="group_analysis">群体分析报告</Option>
            </Select>
          </Form.Item>
          
          <Form.Item name="learner_id" label="学习者ID">
            <Input placeholder="输入学习者ID" />
          </Form.Item>
          
          <Form.Item name="period" label="时间范围">
            <RangePicker />
          </Form.Item>
          
          <Form.Item name="format" label="格式">
            <Select defaultValue="html" style={{ width: 100 }}>
              <Option value="html">HTML</Option>
              <Option value="pdf">PDF</Option>
              <Option value="markdown">Markdown</Option>
            </Select>
          </Form.Item>
          
          <Form.Item>
            <Button type="primary" htmlType="submit" icon={<FileTextOutlined />} loading={loading}>
              生成报告
            </Button>
          </Form.Item>
        </Form>
      </Card>
      
      <Card title="报告列表">
        <Table columns={columns} dataSource={mockReports} rowKey="id" />
      </Card>
    </div>
  );
};

export default Reports;
