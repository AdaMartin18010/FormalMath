import React, { useEffect, useRef, useState } from 'react';
import * as d3 from 'd3';
import { Card, Button, Space, Tag, Tooltip } from 'antd';
import { ZoomInOutlined, ZoomOutOutlined, ReloadOutlined } from '@ant-design/icons';
import type { LearningPath, PathNode, PathStatus } from '../../types';
import './PathVisualization.css';

interface PathVisualizationProps {
  path: LearningPath;
  onNodeClick?: (node: PathNode) => void;
  onNodeStatusChange?: (nodeId: string, status: PathStatus) => void;
}

const statusColors: Record<PathStatus, string> = {
  pending: '#d9d9d9',
  in_progress: '#1890ff',
  completed: '#52c41a',
  adjusted: '#faad14',
  abandoned: '#ff4d4f'
};

const statusLabels: Record<PathStatus, string> = {
  pending: '待开始',
  in_progress: '进行中',
  completed: '已完成',
  adjusted: '已调整',
  abandoned: '已放弃'
};

const PathVisualization: React.FC<PathVisualizationProps> = ({
  path,
  onNodeClick,
  onNodeStatusChange
}) => {
  const svgRef = useRef<SVGSVGElement>(null);
  const containerRef = useRef<HTMLDivElement>(null);
  const [zoom, setZoom] = useState(1);
  const [selectedNode, setSelectedNode] = useState<PathNode | null>(null);

  useEffect(() => {
    if (!svgRef.current || !path.nodes.length) return;

    const svg = d3.select(svgRef.current);
    svg.selectAll('*').remove();

    const width = containerRef.current?.clientWidth || 800;
    const height = 400;
    const nodeRadius = 30;
    const nodeSpacing = 120;

    svg.attr('width', width).attr('height', height);

    // 创建组
    const g = svg.append('g');

    // 缩放行为
    const zoomBehavior = d3.zoom<SVGSVGElement, unknown>()
      .scaleExtent([0.5, 2])
      .on('zoom', (event) => {
        g.attr('transform', event.transform);
        setZoom(event.transform.k);
      });

    svg.call(zoomBehavior);

    // 计算节点位置
    const nodes = path.nodes.map((node, index) => ({
      ...node,
      x: 80 + index * nodeSpacing,
      y: height / 2
    }));

    // 绘制连接线
    const links = nodes.slice(0, -1).map((node, i) => ({
      source: node,
      target: nodes[i + 1]
    }));

    g.selectAll('.link')
      .data(links)
      .enter()
      .append('line')
      .attr('class', 'link')
      .attr('x1', d => d.source.x)
      .attr('y1', d => d.source.y)
      .attr('x2', d => d.target.x)
      .attr('y2', d => d.target.y)
      .attr('stroke', '#999')
      .attr('stroke-width', 2)
      .attr('stroke-dasharray', '5,5');

    // 绘制节点
    const nodeGroups = g.selectAll('.node')
      .data(nodes)
      .enter()
      .append('g')
      .attr('class', 'node')
      .attr('transform', d => `translate(${d.x},${d.y})`)
      .style('cursor', 'pointer')
      .on('click', (event, d) => {
        setSelectedNode(d);
        onNodeClick?.(d);
      });

    // 节点圆圈
    nodeGroups.append('circle')
      .attr('r', nodeRadius)
      .attr('fill', d => statusColors[d.status])
      .attr('stroke', '#fff')
      .attr('stroke-width', 3)
      .attr('class', 'node-circle');

    // 节点序号
    nodeGroups.append('text')
      .attr('text-anchor', 'middle')
      .attr('dy', '0.35em')
      .style('fill', '#fff')
      .style('font-weight', 'bold')
      .style('font-size', '14px')
      .text(d => d.order + 1);

    // 概念名称
    nodeGroups.append('text')
      .attr('text-anchor', 'middle')
      .attr('dy', nodeRadius + 20)
      .style('font-size', '12px')
      .style('fill', '#333')
      .text(d => d.concept.name.length > 8 
        ? d.concept.name.substring(0, 8) + '...' 
        : d.concept.name);

    // 状态标签
    nodeGroups.append('text')
      .attr('text-anchor', 'middle')
      .attr('dy', nodeRadius + 35)
      .style('font-size', '10px')
      .style('fill', '#666')
      .text(d => statusLabels[d.status]);

    // 进度指示器
    const progressWidth = (width - 100) * (path.progress_percentage / 100);
    svg.append('rect')
      .attr('x', 50)
      .attr('y', 20)
      .attr('width', progressWidth)
      .attr('height', 8)
      .attr('fill', '#52c41a')
      .attr('rx', 4);

    svg.append('rect')
      .attr('x', 50)
      .attr('y', 20)
      .attr('width', width - 100)
      .attr('height', 8)
      .attr('fill', 'none')
      .attr('stroke', '#d9d9d9')
      .attr('stroke-width', 1)
      .attr('rx', 4);

    svg.append('text')
      .attr('x', width - 40)
      .attr('y', 28)
      .style('font-size', '12px')
      .style('fill', '#666')
      .text(`${path.progress_percentage.toFixed(1)}%`);

  }, [path, onNodeClick]);

  const handleZoomIn = () => {
    if (svgRef.current) {
      const svg = d3.select(svgRef.current);
      svg.transition().call(
        (d3.zoom() as any).transform,
        d3.zoomTransform(svgRef.current).scale(zoom * 1.2)
      );
    }
  };

  const handleZoomOut = () => {
    if (svgRef.current) {
      const svg = d3.select(svgRef.current);
      svg.transition().call(
        (d3.zoom() as any).transform,
        d3.zoomTransform(svgRef.current).scale(zoom * 0.8)
      );
    }
  };

  const handleReset = () => {
    if (svgRef.current) {
      const svg = d3.select(svgRef.current);
      svg.transition().call(
        (d3.zoom() as any).transform,
        d3.zoomIdentity
      );
    }
  };

  return (
    <Card
      title={
        <Space>
          <span>学习路径: {path.name}</span>
          <Tag color="blue">{path.total_concepts} 个概念</Tag>
          <Tag color="green">{Math.round(path.total_estimated_time / 60)} 小时</Tag>
        </Space>
      }
      extra={
        <Space>
          <Button icon={<ZoomInOutlined />} onClick={handleZoomIn} size="small" />
          <Button icon={<ZoomOutOutlined />} onClick={handleZoomOut} size="small" />
          <Button icon={<ReloadOutlined />} onClick={handleReset} size="small">重置</Button>
        </Space>
      }
    >
      <div ref={containerRef} className="path-visualization-container">
        <svg ref={svgRef} className="path-svg" />
      </div>
      
      {/* 图例 */}
      <div className="path-legend">
        <Space wrap>
          {Object.entries(statusColors).map(([status, color]) => (
            <Space key={status}>
              <span 
                className="legend-color" 
                style={{ backgroundColor: color }}
              />
              <span className="legend-label">
                {statusLabels[status as PathStatus]}
              </span>
            </Space>
          ))}
        </Space>
      </div>

      {/* 选中节点详情 */}
      {selectedNode && (
        <div className="node-detail">
          <h4>{selectedNode.concept.name}</h4>
          <p>难度: {selectedNode.concept.difficulty}</p>
          <p>预计时间: {selectedNode.estimated_time} 分钟</p>
          <p>状态: {statusLabels[selectedNode.status]}</p>
          {onNodeStatusChange && (
            <Space>
              <Button 
                size="small" 
                onClick={() => onNodeStatusChange(selectedNode.node_id, 'completed')}
              >
                标记完成
              </Button>
              <Button 
                size="small"
                onClick={() => onNodeStatusChange(selectedNode.node_id, 'in_progress')}
              >
                标记进行中
              </Button>
            </Space>
          )}
        </div>
      )}
    </Card>
  );
};

export default PathVisualization;
