#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
GraphML 格式导出器
支持Gephi、Cytoscape等网络分析工具
"""

import xml.etree.ElementTree as ET
from xml.dom import minidom
from pathlib import Path
from typing import List, Dict, Any, Optional
from datetime import datetime


class GraphMLExporter:
    """
    GraphML格式导出器
    
    GraphML是图形标记语言，被Gephi、Cytoscape等网络分析工具广泛支持
    """
    
    # 类别颜色映射
    CATEGORY_COLORS = {
        "分析学": "#E3F2FD",
        "代数学": "#F3E5F5",
        "几何拓扑": "#E8F5E9",
        "数论逻辑": "#FBE9E7",
        "概率统计": "#FFF8E1",
        "最优化": "#E0F2F1",
        "控制论": "#E1F5FE",
        "信息论": "#F3E5F5",
        "密码学": "#ECEFF1",
        "基础数学": "#F5F5F5",
        "未分类": "#CCCCCC"
    }
    
    def __init__(self, output_dir: Path):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
        self.nodes: List[Dict[str, Any]] = []
        self.edges: List[Dict[str, Any]] = []
        self.metadata: Dict[str, Any] = {}
    
    def set_data(self, nodes: List[Dict], edges: List[Dict], metadata: Dict[str, Any] = None):
        """设置导出数据"""
        self.nodes = nodes
        self.edges = edges
        self.metadata = metadata or {}
    
    def export_graphml(self, output_path: Optional[Path] = None,
                      include_visual: bool = True) -> Path:
        """
        导出为GraphML格式
        
        Args:
            output_path: 输出文件路径
            include_visual: 是否包含可视化属性（颜色、大小等）
            
        Returns:
            输出文件路径
        """
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph.graphml"
        
        # 创建GraphML根元素
        root = ET.Element("graphml")
        root.set("xmlns", "http://graphml.graphdrawing.org/xmlns")
        root.set("xmlns:xsi", "http://www.w3.org/2001/XMLSchema-instance")
        root.set("xsi:schemaLocation", 
                "http://graphml.graphdrawing.org/xmlns "
                "http://graphml.graphdrawing.org/xmlns/1.0/graphml.xsd")
        
        # 定义节点属性
        self._define_node_keys(root, include_visual)
        
        # 定义边属性
        self._define_edge_keys(root)
        
        # 创建图
        graph = ET.SubElement(root, "graph")
        graph.set("id", "G")
        graph.set("edgedefault", "directed")
        
        # 添加描述
        desc = ET.SubElement(graph, "desc")
        desc.text = f"FormalMath Knowledge Graph - Generated on {datetime.now().isoformat()}"
        
        # 添加节点
        for node in self.nodes:
            self._add_node(graph, node, include_visual)
        
        # 添加边
        for i, edge in enumerate(self.edges):
            self._add_edge(graph, edge, i)
        
        # 美化XML输出
        xml_str = ET.tostring(root, encoding='unicode')
        dom = minidom.parseString(xml_str)
        pretty_xml = dom.toprettyxml(indent="  ")
        
        # 移除空行
        lines = [line for line in pretty_xml.split('\n') if line.strip()]
        pretty_xml = '\n'.join(lines)
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(pretty_xml)
        
        return output_path
    
    def _define_node_keys(self, root: ET.Element, include_visual: bool):
        """定义节点属性键"""
        keys = [
            ('label', 'label', 'string'),
            ('category', 'category', 'string'),
            ('difficulty', 'difficulty', 'int'),
            ('estimated_hours', 'estimated_hours', 'float'),
            ('description', 'description', 'string'),
            ('msc_code', 'msc_code', 'string'),
        ]
        
        if include_visual:
            keys.extend([
                ('color', 'color', 'string'),
                ('size', 'size', 'float'),
                ('x', 'x', 'float'),
                ('y', 'y', 'float'),
            ])
        
        for key_id, attr_name, attr_type in keys:
            key = ET.SubElement(root, "key")
            key.set("id", key_id)
            key.set("for", "node")
            key.set("attr.name", attr_name)
            key.set("attr.type", attr_type)
    
    def _define_edge_keys(self, root: ET.Element):
        """定义边属性键"""
        keys = [
            ('edge_label', 'label', 'string'),
            ('edge_level', 'level', 'string'),
            ('edge_weight', 'weight', 'float'),
        ]
        
        for key_id, attr_name, attr_type in keys:
            key = ET.SubElement(root, "key")
            key.set("id", key_id)
            key.set("for", "edge")
            key.set("attr.name", attr_name)
            key.set("attr.type", attr_type)
    
    def _add_node(self, graph: ET.Element, node: Dict[str, Any], include_visual: bool):
        """添加节点"""
        node_elem = ET.SubElement(graph, "node")
        node_id = node.get('id', '')
        node_elem.set("id", str(node_id))
        
        # 添加基本属性
        data_mappings = [
            ('label', node.get('name', node.get('label', ''))),
            ('category', node.get('category', '未分类')),
            ('difficulty', str(node.get('difficulty', 1))),
            ('estimated_hours', str(node.get('estimated_hours', 0))),
            ('description', node.get('description', '')[:200]),
            ('msc_code', node.get('msc_code', '')),
        ]
        
        for key_id, value in data_mappings:
            data = ET.SubElement(node_elem, "data")
            data.set("key", key_id)
            data.text = str(value)
        
        # 添加可视化属性
        if include_visual:
            category = node.get('category', '未分类')
            color = self.CATEGORY_COLORS.get(category, "#CCCCCC")
            difficulty = node.get('difficulty', 1)
            size = 10 + difficulty * 3
            
            visual_mappings = [
                ('color', color),
                ('size', str(size)),
                ('x', str(node.get('x', 0))),
                ('y', str(node.get('y', 0))),
            ]
            
            for key_id, value in visual_mappings:
                data = ET.SubElement(node_elem, "data")
                data.set("key", key_id)
                data.text = str(value)
    
    def _add_edge(self, graph: ET.Element, edge: Dict[str, Any], index: int):
        """添加边"""
        edge_elem = ET.SubElement(graph, "edge")
        edge_elem.set("id", f"e{index}")
        
        source = edge.get('source', edge.get('from', ''))
        target = edge.get('target', edge.get('to', ''))
        
        edge_elem.set("source", str(source))
        edge_elem.set("target", str(target))
        
        # 添加属性
        label = edge.get('relation_type', edge.get('label', '依赖'))
        level = edge.get('level', 'L1')
        
        # 根据级别设置权重
        weight_map = {'L1': 3, 'L2': 2, 'L3': 1}
        weight = weight_map.get(level, 1)
        
        data_mappings = [
            ('edge_label', label),
            ('edge_level', level),
            ('edge_weight', str(weight)),
        ]
        
        for key_id, value in data_mappings:
            data = ET.SubElement(edge_elem, "data")
            data.set("key", key_id)
            data.text = str(value)
    
    def export_for_gephi(self, output_path: Optional[Path] = None) -> Path:
        """
        导出为Gephi优化格式
        
        Gephi特定的优化，包含更多可视化属性
        """
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph_gephi.graphml"
        
        return self.export_graphml(output_path, include_visual=True)
    
    def export_for_cytoscape(self, output_path: Optional[Path] = None) -> Path:
        """
        导出为Cytoscape优化格式
        
        Cytoscape特定的优化
        """
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph_cytoscape.graphml"
        
        # Cytoscape与标准GraphML兼容，但可能需要特定的属性命名
        return self.export_graphml(output_path, include_visual=True)
    
    def get_statistics(self) -> Dict[str, Any]:
        """获取图的统计信息"""
        from collections import defaultdict
        
        stats = {
            "total_nodes": len(self.nodes),
            "total_edges": len(self.edges),
            "density": 0.0,
            "by_category": defaultdict(int),
            "avg_degree": 0.0
        }
        
        if len(self.nodes) > 1:
            max_edges = len(self.nodes) * (len(self.nodes) - 1)
            stats["density"] = len(self.edges) / max_edges if max_edges > 0 else 0
        
        for node in self.nodes:
            cat = node.get('category', '未分类')
            stats["by_category"][cat] += 1
        
        # 计算平均度数
        if len(self.nodes) > 0:
            stats["avg_degree"] = (len(self.edges) * 2) / len(self.nodes)
        
        return stats
