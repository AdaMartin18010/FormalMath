#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
知识图谱主导出器
整合所有导出功能的统一接口
"""

import json
from pathlib import Path
from typing import List, Dict, Any, Optional, Union
from dataclasses import dataclass, asdict
from datetime import datetime
from collections import defaultdict

try:
    from .json_exporter import JSONExporter
    from .graphml_exporter import GraphMLExporter
    from .pdf_exporter import PDFExporter
    from .image_exporter import ImageExporter
except ImportError:
    from json_exporter import JSONExporter
    from graphml_exporter import GraphMLExporter
    from pdf_exporter import PDFExporter
    from image_exporter import ImageExporter


@dataclass
class ConceptNode:
    """概念节点"""
    id: str
    name: str
    category: str = "未分类"
    difficulty: int = 1
    estimated_hours: float = 1.0
    description: str = ""
    msc_code: str = ""
    x: float = 0.0
    y: float = 0.0
    
    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


@dataclass
class ConceptEdge:
    """概念关系边"""
    source: str
    target: str
    relation_type: str = "依赖"
    level: str = "L1"
    
    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


class KnowledgeGraphExporter:
    """
    知识图谱统一导出器
    
    整合所有导出格式，提供统一的导出接口
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
    
    # 难度颜色映射
    DIFFICULTY_COLORS = {
        1: "#4CAF50",
        2: "#8BC34A",
        3: "#FFC107",
        4: "#FF9800",
        5: "#F44336"
    }
    
    def __init__(self, output_dir: Union[str, Path] = "output/export"):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
        self.nodes: Dict[str, ConceptNode] = {}
        self.edges: List[ConceptEdge] = []
        self.metadata: Dict[str, Any] = {}
        
        # 初始化各导出器
        self.json_exporter = JSONExporter(self.output_dir)
        self.graphml_exporter = GraphMLExporter(self.output_dir)
        self.pdf_exporter = PDFExporter(self.output_dir)
        self.image_exporter = ImageExporter(self.output_dir)
    
    def load_from_json(self, json_path: Union[str, Path]) -> bool:
        """从JSON文件加载知识图谱数据"""
        try:
            with open(json_path, 'r', encoding='utf-8') as f:
                data = json.load(f)
            
            self.metadata = data.get('metadata', {})
            
            # 加载节点
            for node_data in data.get('nodes', []):
                node = ConceptNode(
                    id=node_data['id'],
                    name=node_data.get('label', node_data.get('name', '')),
                    category=node_data.get('category', '未分类'),
                    difficulty=node_data.get('difficulty', 1),
                    estimated_hours=node_data.get('estimated_hours', 1.0),
                    description=node_data.get('description', ''),
                    msc_code=node_data.get('msc_code', '')
                )
                self.nodes[node.id] = node
            
            # 加载边
            for edge_data in data.get('edges', []):
                edge = ConceptEdge(
                    source=edge_data.get('from', edge_data.get('source', '')),
                    target=edge_data.get('to', edge_data.get('target', '')),
                    relation_type=edge_data.get('label', edge_data.get('relation_type', '依赖')),
                    level=edge_data.get('level', 'L1')
                )
                self.edges.append(edge)
            
            # 同步数据到各导出器
            self._sync_data()
            
            print(f"✓ 从JSON加载了 {len(self.nodes)} 个节点, {len(self.edges)} 条边")
            return True
            
        except Exception as e:
            print(f"✗ 加载JSON失败: {e}")
            return False
    
    def load_from_yaml(self, yaml_path: Union[str, Path]) -> bool:
        """从YAML文件加载概念数据"""
        try:
            import yaml
            with open(yaml_path, 'r', encoding='utf-8') as f:
                data = yaml.safe_load(f)
            
            concepts = data.get('concepts', [])
            
            # 创建节点
            for concept in concepts:
                node = ConceptNode(
                    id=concept['concept_id'],
                    name=concept['name'],
                    category=concept.get('category', '未分类'),
                    difficulty=concept.get('difficulty', 1),
                    estimated_hours=concept.get('estimated_hours', 1.0),
                    description=concept.get('description', ''),
                    msc_code=concept.get('msc_code', '')
                )
                self.nodes[node.id] = node
            
            # 创建边
            for concept in concepts:
                for prereq in concept.get('prerequisites', []):
                    edge = ConceptEdge(
                        source=prereq['concept_id'],
                        target=concept['concept_id'],
                        relation_type=prereq.get('relation', '依赖'),
                        level=prereq.get('level', 'L1')
                    )
                    self.edges.append(edge)
            
            self.metadata = {
                'version': data.get('version', '1.0'),
                'generated_date': datetime.now().isoformat(),
                'source': str(yaml_path)
            }
            
            # 同步数据到各导出器
            self._sync_data()
            
            print(f"✓ 从YAML加载了 {len(self.nodes)} 个节点, {len(self.edges)} 条边")
            return True
            
        except ImportError:
            print("✗ PyYAML未安装，无法加载YAML文件")
            return False
        except Exception as e:
            print(f"✗ 加载YAML失败: {e}")
            return False
    
    def _sync_data(self):
        """同步数据到各导出器"""
        nodes_data = [node.to_dict() for node in self.nodes.values()]
        edges_data = [edge.to_dict() for edge in self.edges]
        
        self.json_exporter.set_data(nodes_data, edges_data, self.metadata)
        self.graphml_exporter.set_data(nodes_data, edges_data, self.metadata)
        self.pdf_exporter.set_data(nodes_data, edges_data, self.metadata)
        self.image_exporter.set_data(nodes_data, edges_data, self.metadata)
    
    def export_all(self, formats: List[str] = None) -> Dict[str, Path]:
        """
        导出所有格式
        
        Args:
            formats: 要导出的格式列表，默认为全部
            
        Returns:
            格式到文件路径的映射
        """
        if formats is None:
            formats = ['json', 'csv', 'graphml', 'pdf', 'svg', 'png', 'html']
        
        results = {}
        
        for fmt in formats:
            try:
                if fmt == 'json':
                    results['json'] = self.json_exporter.export_json()
                elif fmt == 'csv':
                    results['csv'] = self.json_exporter.export_csv()
                elif fmt == 'graphml':
                    results['graphml'] = self.graphml_exporter.export_graphml()
                elif fmt == 'pdf':
                    results['pdf'] = self.pdf_exporter.export_pdf()
                elif fmt == 'svg':
                    results['svg'] = self.image_exporter.export_svg()
                elif fmt == 'png':
                    results['png'] = self.image_exporter.export_png()
                elif fmt == 'html':
                    results['html'] = self.pdf_exporter.export_html()
                print(f"  ✓ {fmt.upper()} 导出成功")
            except Exception as e:
                print(f"  ✗ {fmt.upper()} 导出失败: {e}")
        
        return results


def main():
    """主函数 - 命令行入口"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description='FormalMath 知识图谱多格式导出工具',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  # 导出所有格式
  python main_exporter.py -i data.json -o ./output
  
  # 只导出PDF和PNG
  python main_exporter.py -i data.json -f pdf png
  
  # 从YAML导出
  python main_exporter.py -i concepts.yaml -o ./export
        """
    )
    
    parser.add_argument('--input', '-i', required=True, 
                       help='输入文件路径 (JSON或YAML)')
    parser.add_argument('--output', '-o', default='output/export', 
                       help='输出目录 (默认: output/export)')
    parser.add_argument('--formats', '-f', nargs='+',
                       choices=['json', 'csv', 'graphml', 'pdf', 'svg', 'png', 'html', 'all'],
                       default=['all'],
                       help='导出格式 (默认: all)')
    
    args = parser.parse_args()
    
    # 创建导出器
    exporter = KnowledgeGraphExporter(output_dir=args.output)
    
    # 加载数据
    input_path = Path(args.input)
    if input_path.suffix == '.json':
        success = exporter.load_from_json(input_path)
    elif input_path.suffix in ['.yaml', '.yml']:
        success = exporter.load_from_yaml(input_path)
    else:
        print(f"不支持的文件格式: {input_path.suffix}")
        return
    
    if not success:
        print("数据加载失败，退出")
        return
    
    # 确定导出格式
    formats = args.formats
    if 'all' in formats:
        formats = ['json', 'csv', 'graphml', 'pdf', 'svg', 'png', 'html']
    
    # 导出
    print(f"\n开始导出到: {args.output}")
    results = exporter.export_all(formats)
    
    print("\n导出完成!")
    print("生成文件:")
    for fmt, path in results.items():
        print(f"  - {fmt.upper()}: {path}")


if __name__ == '__main__':
    main()
