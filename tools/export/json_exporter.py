#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
JSON/CSV 数据导出器
支持JSON和CSV格式的知识图谱数据导出
"""

import json
import csv
from pathlib import Path
from typing import List, Dict, Any, Optional, Union
from datetime import datetime
from collections import defaultdict


class JSONExporter:
    """
    JSON和CSV格式导出器
    
    支持导出：
    - JSON: 完整数据结构
    - CSV: 节点、边、统计信息分开导出
    """
    
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
    
    def export_json(self, output_path: Optional[Path] = None, 
                   include_metadata: bool = True) -> Path:
        """
        导出为JSON格式
        
        Args:
            output_path: 输出文件路径
            include_metadata: 是否包含元数据
            
        Returns:
            输出文件路径
        """
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph.json"
        
        data = {
            "schema_version": "1.0",
            "export_date": datetime.now().isoformat(),
            "total_nodes": len(self.nodes),
            "total_edges": len(self.edges)
        }
        
        if include_metadata and self.metadata:
            data["metadata"] = self.metadata
        
        data["nodes"] = self.nodes
        data["edges"] = self.edges
        
        # 添加统计信息
        data["statistics"] = self._calculate_statistics()
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        
        return output_path
    
    def export_csv(self, output_dir: Optional[Path] = None) -> Path:
        """
        导出为CSV格式（节点、边、统计分开存储）
        
        Args:
            output_dir: 输出目录
            
        Returns:
            输出目录路径
        """
        if output_dir is None:
            output_dir = self.output_dir / "csv_export"
        output_dir.mkdir(exist_ok=True)
        
        # 导出节点
        self._export_nodes_csv(output_dir / "nodes.csv")
        
        # 导出边
        self._export_edges_csv(output_dir / "edges.csv")
        
        # 导出统计
        self._export_statistics_csv(output_dir / "statistics.csv")
        
        return output_dir
    
    def _export_nodes_csv(self, output_path: Path):
        """导出节点CSV"""
        with open(output_path, 'w', newline='', encoding='utf-8') as f:
            if self.nodes:
                fieldnames = ['id', 'name', 'category', 'difficulty', 
                             'estimated_hours', 'description', 'msc_code', 'x', 'y']
                # 使用实际存在的字段
                available_fields = [f for f in fieldnames if f in self.nodes[0] or f in ['name', 'label']]
                if 'label' in self.nodes[0] and 'name' not in self.nodes[0]:
                    available_fields = ['label' if f == 'name' else f for f in available_fields]
                
                writer = csv.DictWriter(f, fieldnames=available_fields, extrasaction='ignore')
                writer.writeheader()
                
                for node in self.nodes:
                    row = node.copy()
                    # 截断描述
                    if 'description' in row and row['description']:
                        row['description'] = row['description'][:200]
                    writer.writerow(row)
    
    def _export_edges_csv(self, output_path: Path):
        """导出边CSV"""
        with open(output_path, 'w', newline='', encoding='utf-8') as f:
            if self.edges:
                fieldnames = ['source', 'target', 'relation_type', 'level', 'from', 'to', 'label']
                writer = csv.DictWriter(f, fieldnames=fieldnames, extrasaction='ignore')
                writer.writeheader()
                
                for edge in self.edges:
                    row = edge.copy()
                    # 统一字段名
                    if 'from' in row and 'source' not in row:
                        row['source'] = row['from']
                    if 'to' in row and 'target' not in row:
                        row['target'] = row['to']
                    if 'label' in row and 'relation_type' not in row:
                        row['relation_type'] = row['label']
                    writer.writerow(row)
    
    def _export_statistics_csv(self, output_path: Path):
        """导出统计CSV"""
        with open(output_path, 'w', newline='', encoding='utf-8') as f:
            writer = csv.writer(f)
            
            # 基本信息
            writer.writerow(['Metric', 'Value'])
            writer.writerow(['Total Nodes', len(self.nodes)])
            writer.writerow(['Total Edges', len(self.edges)])
            writer.writerow(['Export Date', datetime.now().strftime('%Y-%m-%d %H:%M:%S')])
            writer.writerow([])
            
            # 按类别统计
            by_category = defaultdict(int)
            category_hours = defaultdict(float)
            
            for node in self.nodes:
                cat = node.get('category', '未分类')
                by_category[cat] += 1
                category_hours[cat] += node.get('estimated_hours', 0)
            
            writer.writerow(['Category', 'Count', 'Total Hours'])
            for cat in sorted(by_category.keys()):
                writer.writerow([cat, by_category[cat], f"{category_hours[cat]:.1f}"])
            writer.writerow([])
            
            # 按难度统计
            by_difficulty = defaultdict(int)
            for node in self.nodes:
                diff = node.get('difficulty', 1)
                by_difficulty[diff] += 1
            
            writer.writerow(['Difficulty', 'Count'])
            for diff in sorted(by_difficulty.keys()):
                writer.writerow([diff, by_difficulty[diff]])
    
    def _calculate_statistics(self) -> Dict[str, Any]:
        """计算统计信息"""
        stats = {
            "total_nodes": len(self.nodes),
            "total_edges": len(self.edges),
            "by_category": {},
            "by_difficulty": {},
            "total_hours": 0
        }
        
        for node in self.nodes:
            cat = node.get('category', '未分类')
            stats["by_category"][cat] = stats["by_category"].get(cat, 0) + 1
            
            diff = node.get('difficulty', 1)
            stats["by_difficulty"][diff] = stats["by_difficulty"].get(diff, 0) + 1
            
            stats["total_hours"] += node.get('estimated_hours', 0)
        
        return stats
    
    def export_simple_json(self, output_path: Optional[Path] = None) -> Path:
        """
        导出简化版JSON（仅节点和边）
        
        适用于只需要基本数据的场景
        """
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph_simple.json"
        
        data = {
            "nodes": self.nodes,
            "edges": self.edges
        }
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        
        return output_path
    
    def export_for_d3(self, output_path: Optional[Path] = None) -> Path:
        """
        导出为D3.js兼容格式
        
        D3.js力导向图需要特定的数据格式
        """
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph_d3.json"
        
        # D3格式：节点需要id，边需要source/target为id或索引
        d3_nodes = []
        d3_links = []
        
        node_id_map = {}
        for i, node in enumerate(self.nodes):
            node_id = node.get('id', f'node_{i}')
            node_id_map[node_id] = i
            d3_nodes.append({
                "id": node_id,
                "name": node.get('name', node.get('label', '')),
                "category": node.get('category', '未分类'),
                "difficulty": node.get('difficulty', 1),
                "group": hash(node.get('category', '未分类')) % 10
            })
        
        for edge in self.edges:
            source = edge.get('source', edge.get('from', ''))
            target = edge.get('target', edge.get('to', ''))
            d3_links.append({
                "source": source,
                "target": target,
                "value": 1,
                "type": edge.get('relation_type', edge.get('label', '依赖'))
            })
        
        data = {
            "nodes": d3_nodes,
            "links": d3_links
        }
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        
        return output_path
