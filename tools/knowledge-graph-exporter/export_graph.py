#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath 知识图谱导出工具 (Knowledge Graph Export Tool)
============================================================

支持多格式导出：
- PDF (使用 Playwright/Puppeteer 渲染 HTML)
- PNG/SVG (图片格式)
- GraphML (Gephi/Cytoscape 兼容)
- JSON (数据交换)
- CSV (表格格式)
- HTML (交互式网页)

作者: FormalMath Project
版本: 2.0.0
"""

import json
import csv
import xml.etree.ElementTree as ET
from xml.dom import minidom
from pathlib import Path
from typing import List, Dict, Any, Optional, Tuple, Union
from dataclasses import dataclass, field, asdict
from datetime import datetime
from collections import defaultdict
import argparse
import sys
import asyncio
import tempfile
import base64

# 可选依赖检测
try:
    from playwright.async_api import async_playwright
    PLAYWRIGHT_AVAILABLE = True
except ImportError:
    PLAYWRIGHT_AVAILABLE = False

try:
    from reportlab.lib import colors
    from reportlab.lib.pagesizes import A4
    from reportlab.platypus import SimpleDocTemplate, Table, TableStyle, Paragraph, Spacer
    from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
    from reportlab.lib.units import inch, cm
    REPORTLAB_AVAILABLE = True
except ImportError:
    REPORTLAB_AVAILABLE = False

try:
    import cairosvg
    CAIROSVG_AVAILABLE = True
except ImportError:
    CAIROSVG_AVAILABLE = False

try:
    from PIL import Image as PILImage, ImageDraw, ImageFont
    PIL_AVAILABLE = True
except ImportError:
    PIL_AVAILABLE = False

try:
    import yaml
    YAML_AVAILABLE = True
except ImportError:
    YAML_AVAILABLE = False


# ============ 数据模型 ============

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


# ============ 导出器类 ============

class GraphExporter:
    """
    知识图谱多格式导出器
    
    支持导出为 PDF(Playwright)、PNG/SVG、GraphML、JSON、CSV、HTML
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
        1: "#4CAF50",  # 绿色
        2: "#8BC34A",
        3: "#FFC107",  # 黄色
        4: "#FF9800",
        5: "#F44336"   # 红色
    }
    
    def __init__(self, output_dir: Union[str, Path] = "output/export"):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
        self.nodes: Dict[str, ConceptNode] = {}
        self.edges: List[ConceptEdge] = []
        self.metadata: Dict[str, Any] = {}
        
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
            
            print(f"✓ 从JSON加载了 {len(self.nodes)} 个节点, {len(self.edges)} 条边")
            return True
            
        except Exception as e:
            print(f"✗ 加载JSON失败: {e}")
            return False
    
    def load_from_yaml(self, yaml_path: Union[str, Path]) -> bool:
        """从YAML文件加载概念数据"""
        if not YAML_AVAILABLE:
            print("✗ PyYAML未安装，无法加载YAML文件")
            return False
            
        try:
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
            
            # 创建边（从prerequisites）
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
            
            print(f"✓ 从YAML加载了 {len(self.nodes)} 个节点, {len(self.edges)} 条边")
            return True
            
        except Exception as e:
            print(f"✗ 加载YAML失败: {e}")
            return False
    
    def export_all(self, formats: List[str] = None) -> Dict[str, Path]:
        """导出所有格式"""
        if formats is None:
            formats = ['json', 'csv', 'graphml', 'html', 'svg', 'png', 'pdf']
        
        results = {}
        
        for fmt in formats:
            try:
                if fmt == 'json':
                    results['json'] = self.export_json()
                elif fmt == 'csv':
                    results['csv'] = self.export_csv()
                elif fmt == 'graphml':
                    results['graphml'] = self.export_graphml()
                elif fmt == 'html':
                    results['html'] = self.export_html()
                elif fmt == 'svg':
                    results['svg'] = self.export_svg()
                elif fmt == 'png':
                    results['png'] = self.export_png()
                elif fmt == 'pdf':
                    if PLAYWRIGHT_AVAILABLE:
                        results['pdf'] = asyncio.run(self.export_pdf_playwright())
                    elif REPORTLAB_AVAILABLE:
                        results['pdf'] = self.export_pdf_reportlab()
                    else:
                        print(f"⚠ PDF导出需要Playwright或ReportLab")
                        continue
                print(f"  ✓ {fmt.upper()} 导出成功")
            except Exception as e:
                print(f"  ✗ {fmt.upper()} 导出失败: {e}")
        
        return results

    # ============ JSON 导出 ============
    
    def export_json(self, output_path: Optional[Path] = None) -> Path:
        """导出为JSON格式"""
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph.json"
        
        data = {
            "metadata": {
                **self.metadata,
                "export_date": datetime.now().isoformat(),
                "total_nodes": len(self.nodes),
                "total_edges": len(self.edges)
            },
            "nodes": [node.to_dict() for node in self.nodes.values()],
            "edges": [edge.to_dict() for edge in self.edges]
        }
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        
        return output_path

    # ============ CSV 导出 ============
    
    def export_csv(self, output_dir: Optional[Path] = None) -> Path:
        """导出为CSV格式（节点和边分开）"""
        if output_dir is None:
            output_dir = self.output_dir / "csv_export"
        output_dir.mkdir(exist_ok=True)
        
        # 导出节点
        nodes_path = output_dir / "nodes.csv"
        with open(nodes_path, 'w', newline='', encoding='utf-8') as f:
            if self.nodes:
                writer = csv.DictWriter(f, fieldnames=['id', 'name', 'category', 'difficulty', 
                                                        'estimated_hours', 'description', 'msc_code'])
                writer.writeheader()
                for node in self.nodes.values():
                    writer.writerow({
                        'id': node.id,
                        'name': node.name,
                        'category': node.category,
                        'difficulty': node.difficulty,
                        'estimated_hours': node.estimated_hours,
                        'description': node.description[:100] if node.description else '',
                        'msc_code': node.msc_code
                    })
        
        # 导出边
        edges_path = output_dir / "edges.csv"
        with open(edges_path, 'w', newline='', encoding='utf-8') as f:
            writer = csv.DictWriter(f, fieldnames=['source', 'target', 'relation_type', 'level'])
            writer.writeheader()
            for edge in self.edges:
                writer.writerow(edge.to_dict())
        
        # 导出统计
        stats_path = output_dir / "statistics.csv"
        with open(stats_path, 'w', newline='', encoding='utf-8') as f:
            writer = csv.writer(f)
            writer.writerow(['Metric', 'Value'])
            writer.writerow(['Total Nodes', len(self.nodes)])
            writer.writerow(['Total Edges', len(self.edges)])
            
            by_category = defaultdict(int)
            for node in self.nodes.values():
                by_category[node.category] += 1
            
            writer.writerow([])
            writer.writerow(['Category', 'Count'])
            for cat, count in sorted(by_category.items(), key=lambda x: -x[1]):
                writer.writerow([cat, count])
        
        return output_dir

    # ============ GraphML 导出 ============
    
    def export_graphml(self, output_path: Optional[Path] = None) -> Path:
        """导出为GraphML格式（Gephi兼容）"""
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph.graphml"
        
        root = ET.Element("graphml")
        root.set("xmlns", "http://graphml.graphdrawing.org/xmlns")
        root.set("xmlns:xsi", "http://www.w3.org/2001/XMLSchema-instance")
        root.set("xsi:schemaLocation", "http://graphml.graphdrawing.org/xmlns http://graphml.graphdrawing.org/xmlns/1.0/graphml.xsd")
        
        # 定义属性
        keys = [
            ('id', 'node', 'id', 'string'),
            ('label', 'node', 'label', 'string'),
            ('category', 'node', 'category', 'string'),
            ('difficulty', 'node', 'difficulty', 'int'),
            ('estimated_hours', 'node', 'estimated_hours', 'float'),
            ('color', 'node', 'color', 'string'),
            ('edge_label', 'edge', 'label', 'string'),
            ('edge_level', 'edge', 'level', 'string')
        ]
        
        for key_id, key_for, attr_name, attr_type in keys:
            key = ET.SubElement(root, "key")
            key.set("id", key_id)
            key.set("for", key_for)
            key.set("attr.name", attr_name)
            key.set("attr.type", attr_type)
        
        graph = ET.SubElement(root, "graph")
        graph.set("id", "G")
        graph.set("edgedefault", "directed")
        
        # 添加节点
        for node in self.nodes.values():
            node_elem = ET.SubElement(graph, "node")
            node_elem.set("id", node.id)
            
            for key_id, value in [
                ('label', node.name),
                ('category', node.category),
                ('difficulty', str(node.difficulty)),
                ('estimated_hours', str(node.estimated_hours)),
                ('color', self.CATEGORY_COLORS.get(node.category, "#CCCCCC"))
            ]:
                data = ET.SubElement(node_elem, "data")
                data.set("key", key_id)
                data.text = value
        
        # 添加边
        for i, edge in enumerate(self.edges):
            edge_elem = ET.SubElement(graph, "edge")
            edge_elem.set("id", f"e{i}")
            edge_elem.set("source", edge.source)
            edge_elem.set("target", edge.target)
            
            data_label = ET.SubElement(edge_elem, "data")
            data_label.set("key", "edge_label")
            data_label.text = edge.relation_type
            
            data_level = ET.SubElement(edge_elem, "data")
            data_level.set("key", "edge_level")
            data_level.text = edge.level
        
        # 美化XML输出
        xml_str = ET.tostring(root, encoding='unicode')
        dom = minidom.parseString(xml_str)
        pretty_xml = dom.toprettyxml(indent="  ")
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(pretty_xml)
        
        return output_path

    # ============ HTML 导出 ============
    
    def export_html(self, output_path: Optional[Path] = None, 
                    include_graph: bool = True,
                    template: Optional[str] = None) -> Path:
        """导出为交互式HTML"""
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph.html"
        
        nodes_data = [node.to_dict() for node in self.nodes.values()]
        edges_data = [edge.to_dict() for edge in self.edges]
        
        # 按类别统计
        by_category = defaultdict(int)
        for node in self.nodes.values():
            by_category[node.category] += 1
        
        # 计算总学时
        total_hours = sum(node.estimated_hours for node in self.nodes.values())
        
        html_content = self._generate_html_template(
            nodes=nodes_data,
            edges=edges_data,
            by_category=dict(by_category),
            total_hours=total_hours,
            include_graph=include_graph
        )
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(html_content)
        
        return output_path
    
    def _generate_html_template(self, nodes: List[Dict], edges: List[Dict], 
                                by_category: Dict[str, int], total_hours: float,
                                include_graph: bool) -> str:
        """生成HTML模板"""
        
        category_tags = "\n".join([
            f'<span class="category-tag" style="background: {self.CATEGORY_COLORS.get(cat, "#f5f5f5")}">'
            f'{cat} ({count})</span>'
            for cat, count in sorted(by_category.items(), key=lambda x: -x[1])
        ])
        
        concept_rows = "\n".join([
            f'''<tr>
                <td><strong>{node.get('name', '')}</strong></td>
                <td>{node.get('category', '未分类')}</td>
                <td class="difficulty">{'★' * node.get('difficulty', 1)}{'☆' * (5 - node.get('difficulty', 1))}</td>
                <td>{node.get('estimated_hours', '-')}h</td>
                <td>{node.get('msc_code', '-')}</td>
            </tr>'''
            for node in sorted(nodes, key=lambda x: x.get('category', ''))
        ])
        
        return f'''<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>FormalMath 知识图谱</title>
    <style>
        /* 基础样式 */
        * {{ margin: 0; padding: 0; box-sizing: border-box; }}
        
        body {{
            font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, 
                         "Noto Sans SC", "Microsoft YaHei", sans-serif;
            line-height: 1.6;
            color: #333;
            background: #f5f7fa;
        }}
        
        .container {{
            max-width: 1400px;
            margin: 0 auto;
            padding: 20px;
            background: white;
        }}
        
        /* 头部样式 */
        .header {{
            text-align: center;
            padding: 40px 0;
            border-bottom: 3px solid #1a73e8;
            margin-bottom: 40px;
        }}
        
        .header h1 {{
            font-size: 2.5em;
            color: #1a73e8;
            margin-bottom: 15px;
        }}
        
        .meta {{
            color: #666;
            font-size: 0.95em;
        }}
        
        /* 统计卡片 */
        .stats-grid {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
            gap: 20px;
            margin: 40px 0;
        }}
        
        .stat-card {{
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white;
            padding: 25px;
            border-radius: 12px;
            text-align: center;
            box-shadow: 0 4px 6px rgba(0,0,0,0.1);
        }}
        
        .stat-card h3 {{
            font-size: 2.5em;
            margin-bottom: 8px;
        }}
        
        /* 类别分布 */
        .category-section {{ margin: 40px 0; }}
        
        .section-title {{
            font-size: 1.5em;
            color: #333;
            margin-bottom: 20px;
            padding-bottom: 10px;
            border-bottom: 2px solid #e0e0e0;
        }}
        
        .category-list {{
            display: flex;
            flex-wrap: wrap;
            gap: 12px;
        }}
        
        .category-tag {{
            padding: 10px 18px;
            border-radius: 25px;
            font-size: 0.95em;
            border: 1px solid #ddd;
            font-weight: 500;
        }}
        
        /* 概念表格 */
        .concepts-table {{
            width: 100%;
            border-collapse: collapse;
            margin: 30px 0;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }}
        
        .concepts-table th {{
            background: #1a73e8;
            color: white;
            padding: 15px;
            text-align: left;
            font-weight: 600;
        }}
        
        .concepts-table td {{
            padding: 12px 15px;
            border-bottom: 1px solid #e0e0e0;
        }}
        
        .concepts-table tr:nth-child(even) {{ background: #f8f9fa; }}
        .concepts-table tr:hover {{ background: #e3f2fd; }}
        
        .difficulty {{ color: #ffc107; font-size: 1.1em; }}
        
        /* 图谱可视化 */
        .graph-section {{
            margin: 40px 0;
            text-align: center;
            background: #fafafa;
            padding: 30px;
            border-radius: 12px;
        }}
        
        #graph-container {{
            width: 100%;
            height: 600px;
            background: white;
            border-radius: 8px;
            box-shadow: 0 2px 8px rgba(0,0,0,0.1);
        }}
        
        /* 打印样式 - 优化版 */
        @media print {{
            @page {{
                size: A4;
                margin: 1.5cm;
                @top-center {{
                    content: "FormalMath 知识图谱";
                    font-size: 9pt;
                    color: #666;
                }}
                @bottom-center {{
                    content: "第 " counter(page) " 页";
                    font-size: 9pt;
                }}
            }}
            
            * {{
                -webkit-print-color-adjust: exact !important;
                print-color-adjust: exact !important;
            }}
            
            body {{
                background: white;
                font-size: 10pt;
            }}
            
            .container {{
                max-width: 100%;
                padding: 0;
            }}
            
            .header {{
                padding: 20px 0;
                page-break-after: avoid;
            }}
            
            .stats-grid {{
                page-break-inside: avoid;
            }}
            
            .concepts-table {{
                page-break-inside: auto;
                font-size: 9pt;
            }}
            
            .concepts-table tr {{
                page-break-inside: avoid;
            }}
            
            .no-print {{ display: none !important; }}
            
            .page-break {{ page-break-before: always; }}
            
            .graph-section {{ display: none; }}
        }}
        
        /* 按钮样式 */
        .btn {{
            display: inline-block;
            padding: 12px 24px;
            background: #1a73e8;
            color: white;
            text-decoration: none;
            border-radius: 6px;
            margin: 5px;
            cursor: pointer;
            border: none;
            font-size: 1em;
            transition: background 0.2s;
        }}
        
        .btn:hover {{ background: #1557b0; }}
        
        .btn-secondary {{ background: #5f6368; }}
        .btn-secondary:hover {{ background: #494c50; }}
        
        .actions {{
            text-align: center;
            margin: 30px 0;
            padding: 25px;
            background: #f8f9fa;
            border-radius: 10px;
        }}
    </style>
</head>
<body>
    <div class="container">
        <header class="header">
            <h1>📚 FormalMath 知识图谱</h1>
            <div class="meta">
                <p>生成时间: {datetime.now().strftime('%Y年%m月%d日 %H:%M')}</p>
                <p>概念总数: {len(nodes)} | 关系总数: {len(edges)} | 预计总学时: {total_hours:.0f}小时</p>
            </div>
        </header>
        
        <div class="actions no-print">
            <button class="btn" onclick="window.print()">🖨️ 打印 / 另存为PDF</button>
            <button class="btn btn-secondary" onclick="exportJSON()">📥 导出JSON</button>
            <button class="btn btn-secondary" onclick="exportCSV()">📊 导出CSV</button>
        </div>
        
        <section class="stats-grid">
            <div class="stat-card">
                <h3>{len(nodes)}</h3>
                <p>概念总数</p>
            </div>
            <div class="stat-card">
                <h3>{len(edges)}</h3>
                <p>依赖关系</p>
            </div>
            <div class="stat-card">
                <h3>{len(by_category)}</h3>
                <p>学科类别</p>
            </div>
            <div class="stat-card">
                <h3>{total_hours:.0f}h</h3>
                <p>预计总学时</p>
            </div>
        </section>
        
        <section class="category-section">
            <h2 class="section-title">📂 类别分布</h2>
            <div class="category-list">
                {category_tags}
            </div>
        </section>
        
        <section class="page-break">
            <h2 class="section-title">📋 概念详情</h2>
            <table class="concepts-table">
                <thead>
                    <tr>
                        <th>概念名称</th>
                        <th>类别</th>
                        <th>难度</th>
                        <th>预计学时</th>
                        <th>MSC编码</th>
                    </tr>
                </thead>
                <tbody>
                    {concept_rows}
                </tbody>
            </table>
        </section>
        
        {'<section class="graph-section page-break no-print">' if include_graph else '<section class="graph-section page-break">' if include_graph else ''}
        {'<h2 class="section-title">🕸️ 关系图谱</h2>' if include_graph else ''}
        {'<div id="graph-container"></div>' if include_graph else ''}
        {'</section>' if include_graph else ''}
    </div>
    
    <script>
        const graphData = {json.dumps(dict(nodes=nodes, edges=edges), ensure_ascii=False)};
        
        function exportJSON() {{
            const dataStr = JSON.stringify(graphData, null, 2);
            const blob = new Blob([dataStr], {{type: 'application/json'}});
            const url = URL.createObjectURL(blob);
            const a = document.createElement('a');
            a.href = url;
            a.download = 'knowledge_graph.json';
            a.click();
            URL.revokeObjectURL(url);
        }}
        
        function exportCSV() {{
            let csv = 'ID,Name,Category,Difficulty,Hours\\n';
            graphData.nodes.forEach(n => {{
                csv += `${{n.id}},"${{n.name}}",${{n.category || '未分类'}},${{n.difficulty || 1}},${{n.estimated_hours || 0}}\\n`;
            }});
            const blob = new Blob(['\\ufeff' + csv], {{type: 'text/csv;charset=utf-8;'}});
            const url = URL.createObjectURL(blob);
            const a = document.createElement('a');
            a.href = url;
            a.download = 'concepts.csv';
            a.click();
            URL.revokeObjectURL(url);
        }}
        
        {'// 渲染力导向图\n        function renderGraph() {\n            const container = document.getElementById("graph-container");\n            if (!container) return;\n            \n            const width = container.clientWidth;\n            const height = 600;\n            \n            // 初始化节点位置\n            const nodeMap = {};\n            const nodes = graphData.nodes.map((n, i) => {\n                const node = {\n                    ...n,\n                    x: width/2 + Math.cos(i * 2 * Math.PI / graphData.nodes.length) * 250,\n                    y: height/2 + Math.sin(i * 2 * Math.PI / graphData.nodes.length) * 250,\n                    vx: 0, vy: 0\n                };\n                nodeMap[n.id] = node;\n                return node;\n            });\n            \n            // 力导向模拟\n            for (let iter = 0; iter < 100; iter++) {\n                // 斥力\n                for (let i = 0; i < nodes.length; i++) {\n                    for (let j = i + 1; j < nodes.length; j++) {\n                        const dx = nodes[j].x - nodes[i].x;\n                        const dy = nodes[j].y - nodes[i].y;\n                        const dist = Math.sqrt(dx*dx + dy*dy) || 1;\n                        if (dist < 200) {\n                            const force = 2000 / (dist * dist);\n                            const fx = force * dx / dist;\n                            const fy = force * dy / dist;\n                            nodes[i].x -= fx; nodes[i].y -= fy;\n                            nodes[j].x += fx; nodes[j].y += fy;\n                        }\n                    }\n                }\n                // 引力\n                graphData.edges.forEach(e => {\n                    const s = nodeMap[e.source || e.from];\n                    const t = nodeMap[e.target || e.to];\n                    if (s && t) {\n                        const dx = t.x - s.x;\n                        const dy = t.y - s.y;\n                        const dist = Math.sqrt(dx*dx + dy*dy) || 1;\n                        const force = (dist - 100) * 0.01;\n                        const fx = force * dx / dist;\n                        const fy = force * dy / dist;\n                        s.x += fx; s.y += fy;\n                        t.x -= fx; t.y -= fy;\n                    }\n                });\n                // 边界\n                nodes.forEach(n => {\n                    n.x = Math.max(50, Math.min(width - 50, n.x));\n                    n.y = Math.max(50, Math.min(height - 50, n.y));\n                });\n            }\n            \n            // 生成SVG\n            const colors = {json.dumps(self.CATEGORY_COLORS, ensure_ascii=False)};\n            let svg = `<svg width="${width}" height="${height}">\n                <defs>\n                    <marker id="arrow" markerWidth="10" markerHeight="7" refX="9" refY="3.5" orient="auto">\n                        <polygon points="0 0, 10 3.5, 0 7" fill="#999"/>\n                    </marker>\n                </defs>\n                <rect width="100%" height="100%" fill="#fafafa"/>`;\n            \n            // 边\n            graphData.edges.forEach(e => {\n                const s = nodeMap[e.source || e.from];\n                const t = nodeMap[e.target || e.to];\n                if (s && t) {\n                    svg += `<line x1="${s.x}" y1="${s.y}" x2="${t.x}" y2="${t.y}" stroke="#bbb" stroke-width="1.5" marker-end="url(#arrow)"/>`;\n                }\n            });\n            \n            // 节点\n            nodes.forEach(n => {\n                const color = colors[n.category] || "#ccc";\n                const r = 8 + (n.difficulty || 1) * 2;\n                svg += `<circle cx="${n.x}" cy="${n.y}" r="${r}" fill="${color}" stroke="#333" stroke-width="1.5"/>\n                    <text x="${n.x}" y="${n.y + r + 14}" text-anchor="middle" font-size="10" fill="#333">${n.name}</text>`;\n            });\n            \n            // 图例\n            let lx = width - 160, ly = 20;\n            svg += `<rect x="${lx-10}" y="${ly}" width="150" height="${Object.keys(colors).length * 22 + 25}" fill="white" stroke="#ddd" rx="5"/>\n                <text x="${lx}" y="${ly+20}" font-size="12" font-weight="bold" fill="#333">类别图例</text>`;\n            Object.entries(colors).forEach(([cat, col], i) => {\n                const y = ly + 40 + i * 22;\n                svg += `<circle cx="${lx+10}" cy="${y}" r="7" fill="${col}" stroke="#333"/>\n                    <text x="${lx+25}" y="${y+4}" font-size="10" fill="#333">${cat}</text>`;\n            });\n            \n            svg += "</svg>";\n            container.innerHTML = svg;\n        }\n        \n        if (document.getElementById("graph-container")) {\n            renderGraph();\n        }' if include_graph else ''}
    </script>
</body>
</html>'''

    # ============ SVG 导出 ============
    
    def export_svg(self, output_path: Optional[Path] = None, 
                   width: int = 1200, height: int = 800,
                   layout: str = "force") -> Path:
        """导出为SVG格式"""
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph.svg"
        
        # 计算布局
        self._calculate_layout(width, height)
        
        svg_parts = [f'''<?xml version="1.0" encoding="UTF-8"?>
<svg width="{width}" height="{height}" xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}">
    <defs>
        <marker id="arrowhead" markerWidth="10" markerHeight="7" refX="9" refY="3.5" orient="auto">
            <polygon points="0 0, 10 3.5, 0 7" fill="#666"/>
        </marker>
        <filter id="shadow" x="-20%" y="-20%" width="140%" height="140%">
            <feDropShadow dx="1" dy="1" stdDeviation="2" flood-opacity="0.3"/>
        </filter>
    </defs>
    <rect width="100%" height="100%" fill="#fafafa"/>
    <text x="{width/2}" y="35" text-anchor="middle" font-family="Arial, sans-serif" font-size="22" font-weight="bold" fill="#333">
        FormalMath 知识图谱
    </text>
    <text x="{width/2}" y="60" text-anchor="middle" font-family="Arial, sans-serif" font-size="12" fill="#666">
        {len(self.nodes)} 概念 | {len(self.edges)} 关系 | 生成于 {datetime.now().strftime('%Y-%m-%d')}
    </text>
''']
        
        # 绘制边
        for edge in self.edges:
            if edge.source in self.nodes and edge.target in self.nodes:
                source = self.nodes[edge.source]
                target = self.nodes[edge.target]
                svg_parts.append(f'''    <line x1="{source.x}" y1="{source.y}" x2="{target.x}" y2="{target.y}" 
        stroke="#bbb" stroke-width="1.5" marker-end="url(#arrowhead)" opacity="0.7"/>
''')
        
        # 绘制节点
        for node in self.nodes.values():
            color = self.CATEGORY_COLORS.get(node.category, "#CCCCCC")
            r = 10 + node.difficulty * 2
            
            svg_parts.append(f'''    <circle cx="{node.x}" cy="{node.y}" r="{r}" 
        fill="{color}" stroke="#333" stroke-width="1.5" filter="url(#shadow)"/>
    <text x="{node.x}" y="{node.y + r + 16}" text-anchor="middle" 
        font-family="Arial, sans-serif" font-size="10" fill="#333" font-weight="500">{node.name}</text>
''')
        
        # 图例
        legend_x = width - 190
        legend_y = 100
        svg_parts.append(f'''    <rect x="{legend_x - 15}" y="{legend_y - 30}" width="185" height="{len(self.CATEGORY_COLORS) * 26 + 50}" 
        fill="white" stroke="#ddd" stroke-width="1" rx="8" filter="url(#shadow)"/>
    <text x="{legend_x}" y="{legend_y - 8}" font-family="Arial, sans-serif" font-size="13" font-weight="bold" fill="#333">类别图例</text>
''')
        
        for i, (category, color) in enumerate(self.CATEGORY_COLORS.items()):
            if category == "未分类":
                continue
            y = legend_y + i * 26
            svg_parts.append(f'''    <circle cx="{legend_x + 10}" cy="{y}" r="9" fill="{color}" stroke="#333" stroke-width="1"/>
    <text x="{legend_x + 28}" y="{y + 4}" font-family="Arial, sans-serif" font-size="11" fill="#333">{category}</text>
''')
        
        svg_parts.append('</svg>')
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(''.join(svg_parts))
        
        return output_path

    # ============ PNG 导出 ============
    
    def export_png(self, output_path: Optional[Path] = None, 
                   width: int = 1200, height: int = 800) -> Path:
        """导出为PNG格式"""
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph.png"
        
        if CAIROSVG_AVAILABLE:
            # 使用cairosvg转换SVG为PNG
            svg_path = self.export_svg(output_path=self.output_dir / ".temp.svg", width=width, height=height)
            cairosvg.svg2png(url=str(svg_path), write_to=str(output_path), 
                           output_width=width, output_height=height)
            svg_path.unlink()
            return output_path
            
        elif PIL_AVAILABLE:
            return self._export_png_with_pil(output_path, width, height)
        else:
            raise ImportError("PNG导出需要cairosvg或Pillow。请安装: pip install cairosvg pillow")
    
    def _export_png_with_pil(self, output_path: Path, width: int, height: int) -> Path:
        """使用PIL导出PNG"""
        img = PILImage.new('RGB', (width, height), color='#fafafa')
        draw = ImageDraw.Draw(img)
        
        self._calculate_layout(width, height)
        
        # 绘制标题
        draw.text((width//2, 35), "FormalMath 知识图谱", fill='#333333', anchor='mm')
        draw.text((width//2, 60), f"{len(self.nodes)} 概念 | {len(self.edges)} 关系", fill='#666666', anchor='mm')
        
        # 绘制边
        for edge in self.edges:
            if edge.source in self.nodes and edge.target in self.nodes:
                source = self.nodes[edge.source]
                target = self.nodes[edge.target]
                draw.line([(source.x, source.y), (target.x, target.y)], fill='#bbbbbb', width=1)
        
        # 绘制节点
        for node in self.nodes.values():
            color = self.CATEGORY_COLORS.get(node.category, "#CCCCCC")
            rgb = self._hex_to_rgb(color)
            r = 10 + node.difficulty * 2
            
            draw.ellipse([node.x - r, node.y - r, node.x + r, node.y + r], 
                        fill=rgb, outline='#333333', width=2)
            draw.text((node.x, node.y + r + 12), node.name, fill='#333333', anchor='mm')
        
        img.save(output_path, 'PNG')
        return output_path

    # ============ PDF 导出 (Playwright) ============
    
    async def export_pdf_playwright(self, output_path: Optional[Path] = None,
                                     width: int = 1200, height: int = 800) -> Path:
        """使用Playwright导出PDF（推荐，渲染效果更好）"""
        if not PLAYWRIGHT_AVAILABLE:
            raise ImportError("PDF导出需要Playwright。请安装: pip install playwright && playwright install chromium")
        
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph.pdf"
        
        # 生成HTML临时文件
        html_content = self._generate_html_for_pdf()
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.html', delete=False, encoding='utf-8') as f:
            f.write(html_content)
            temp_html = f.name
        
        try:
            async with async_playwright() as p:
                browser = await p.chromium.launch()
                page = await browser.new_page()
                
                await page.goto(f'file://{temp_html}')
                await page.wait_for_load_state('networkidle')
                
                # 等待图表渲染（如果有）
                await page.wait_for_timeout(1000)
                
                await page.pdf(
                    path=str(output_path),
                    format='A4',
                    print_background=True,
                    margin={
                        'top': '2cm',
                        'bottom': '2cm',
                        'left': '2cm',
                        'right': '2cm'
                    },
                    display_header_footer=True,
                    header_template='<div style="font-size:9px; margin-left:2cm; color:#666;">FormalMath 知识图谱</div>',
                    footer_template='<div style="font-size:9px; margin:0 auto; color:#666;"><span class="pageNumber"></span> / <span class="totalPages"></span></div>'
                )
                
                await browser.close()
        finally:
            Path(temp_html).unlink(missing_ok=True)
        
        return output_path
    
    def _generate_html_for_pdf(self) -> str:
        """生成用于PDF渲染的优化HTML"""
        nodes_data = [node.to_dict() for node in self.nodes.values()]
        edges_data = [edge.to_dict() for edge in self.edges]
        
        by_category = defaultdict(lambda: {'count': 0, 'hours': 0})
        for node in self.nodes.values():
            by_category[node.category]['count'] += 1
            by_category[node.category]['hours'] += node.estimated_hours
        
        category_rows = "\n".join([
            f'''<tr>
                <td>{cat}</td>
                <td>{data['count']}</td>
                <td>{data['hours']:.0f}h</td>
            </tr>'''
            for cat, data in sorted(by_category.items(), key=lambda x: -x[1]['count'])
        ])
        
        concept_rows = "\n".join([
            f'''<tr>
                <td>{node.name}</td>
                <td>{node.category}</td>
                <td>{'★' * node.difficulty}{'☆' * (5 - node.difficulty)}</td>
                <td>{node.estimated_hours:.0f}h</td>
            </tr>'''
            for node in sorted(self.nodes.values(), key=lambda x: x.category)
        ])
        
        return f'''<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>FormalMath 知识图谱</title>
    <style>
        @page {{
            size: A4;
            margin: 2cm;
            @top-center {{ content: "FormalMath 知识图谱"; font-size: 9pt; color: #666; }}
            @bottom-center {{ content: counter(page); font-size: 9pt; }}
        }}
        
        * {{
            -webkit-print-color-adjust: exact !important;
            print-color-adjust: exact !important;
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }}
        
        body {{
            font-family: "Noto Sans CJK SC", "Microsoft YaHei", sans-serif;
            font-size: 10pt;
            line-height: 1.5;
            color: #333;
        }}
        
        .header {{
            text-align: center;
            padding: 20px 0;
            border-bottom: 3px solid #1a73e8;
            margin-bottom: 30px;
        }}
        
        .header h1 {{
            font-size: 22pt;
            color: #1a73e8;
            margin-bottom: 10px;
        }}
        
        .meta {{
            color: #666;
            font-size: 10pt;
        }}
        
        h2 {{
            font-size: 14pt;
            color: #333;
            margin: 25px 0 15px 0;
            padding-bottom: 8px;
            border-bottom: 2px solid #e0e0e0;
            page-break-after: avoid;
        }}
        
        table {{
            width: 100%;
            border-collapse: collapse;
            margin: 15px 0;
            font-size: 9pt;
        }}
        
        th {{
            background: #1a73e8;
            color: white;
            padding: 10px;
            text-align: left;
            font-weight: 600;
        }}
        
        td {{
            padding: 8px 10px;
            border-bottom: 1px solid #e0e0e0;
        }}
        
        tr:nth-child(even) {{ background: #f8f9fa; }}
        
        .stats {{
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white;
            padding: 15px;
            border-radius: 8px;
            margin: 20px 0;
        }}
        
        .stats-grid {{
            display: grid;
            grid-template-columns: repeat(4, 1fr);
            gap: 20px;
            text-align: center;
        }}
        
        .stat-item h3 {{
            font-size: 24pt;
            margin-bottom: 5px;
        }}
        
        .page-break {{ page-break-before: always; }}
        
        .no-break {{ page-break-inside: avoid; }}
    </style>
</head>
<body>
    <div class="header">
        <h1>📚 FormalMath 知识图谱</h1>
        <div class="meta">
            <p>生成时间: {datetime.now().strftime('%Y年%m月%d日 %H:%M')}</p>
            <p>概念总数: {len(self.nodes)} | 关系总数: {len(self.edges)}</p>
        </div>
    </div>
    
    <div class="stats no-break">
        <div class="stats-grid">
            <div class="stat-item">
                <h3>{len(self.nodes)}</h3>
                <p>概念总数</p>
            </div>
            <div class="stat-item">
                <h3>{len(self.edges)}</h3>
                <p>依赖关系</p>
            </div>
            <div class="stat-item">
                <h3>{len(by_category)}</h3>
                <p>学科类别</p>
            </div>
            <div class="stat-item">
                <h3>{sum(n.estimated_hours for n in self.nodes.values()):.0f}h</h3>
                <p>预计总学时</p>
            </div>
        </div>
    </div>
    
    <h2>📊 类别统计</h2>
    <table>
        <thead>
            <tr><th>类别</th><th>概念数</th><th>预计学时</th></tr>
        </thead>
        <tbody>
            {category_rows}
        </tbody>
    </table>
    
    <div class="page-break"></div>
    
    <h2>📋 概念详情</h2>
    <table>
        <thead>
            <tr><th>概念名称</th><th>类别</th><th>难度</th><th>预计学时</th></tr>
        </thead>
        <tbody>
            {concept_rows}
        </tbody>
    </table>
</body>
</html>'''

    # ============ PDF 导出 (ReportLab 备选) ============
    
    def export_pdf_reportlab(self, output_path: Optional[Path] = None) -> Path:
        """使用ReportLab导出PDF（备选方案）"""
        if not REPORTLAB_AVAILABLE:
            raise ImportError("ReportLab未安装。请安装: pip install reportlab")
        
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph.pdf"
        
        doc = SimpleDocTemplate(
            str(output_path),
            pagesize=A4,
            rightMargin=2*cm,
            leftMargin=2*cm,
            topMargin=2*cm,
            bottomMargin=2*cm
        )
        
        styles = getSampleStyleSheet()
        story = []
        
        # 标题
        title_style = ParagraphStyle(
            'CustomTitle',
            parent=styles['Heading1'],
            fontSize=22,
            spaceAfter=20,
            alignment=1,
            textColor=colors.HexColor('#1a73e8')
        )
        story.append(Paragraph("FormalMath 知识图谱", title_style))
        story.append(Paragraph(f"<b>生成日期:</b> {datetime.now().strftime('%Y年%m月%d日')}", styles['Normal']))
        story.append(Spacer(1, 0.2*inch))
        
        # 统计表格
        by_category = defaultdict(lambda: {'count': 0, 'hours': 0})
        for node in self.nodes.values():
            by_category[node.category]['count'] += 1
            by_category[node.category]['hours'] += node.estimated_hours
        
        stats_data = [['类别', '概念数', '预计学时']]
        for cat, data in sorted(by_category.items(), key=lambda x: -x[1]['count']):
            stats_data.append([cat, str(data['count']), f"{data['hours']:.0f}h"])
        
        stats_table = Table(stats_data, colWidths=[3*inch, 1.2*inch, 1.2*inch])
        stats_table.setStyle(TableStyle([
            ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#1a73e8')),
            ('TEXTCOLOR', (0, 0), (-1, 0), colors.whitesmoke),
            ('ALIGN', (0, 0), (-1, -1), 'CENTER'),
            ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
            ('FONTSIZE', (0, 0), (-1, 0), 11),
            ('BOTTOMPADDING', (0, 0), (-1, 0), 10),
            ('BACKGROUND', (0, 1), (-1, -1), colors.HexColor('#f8f9fa')),
            ('GRID', (0, 0), (-1, -1), 0.5, colors.grey),
            ('ROWBACKGROUNDS', (0, 1), (-1, -1), [colors.white, colors.HexColor('#f0f0f0')])
        ]))
        story.append(stats_table)
        story.append(Spacer(1, 0.3*inch))
        
        # 概念详情表格
        story.append(Paragraph("概念详情", styles['Heading2']))
        story.append(Spacer(1, 0.1*inch))
        
        concept_data = [['概念名称', '类别', '难度', '学时']]
        for node in sorted(self.nodes.values(), key=lambda x: x.category):
            difficulty_stars = '★' * node.difficulty + '☆' * (5 - node.difficulty)
            concept_data.append([node.name, node.category, difficulty_stars, f"{node.estimated_hours:.0f}h"])
        
        # 分批处理
        for i in range(0, len(concept_data), 35):
            chunk = concept_data[i:i+36] if i == 0 else [concept_data[0]] + concept_data[i:i+35]
            concept_table = Table(chunk, colWidths=[2.8*inch, 1.5*inch, 1*inch, 0.8*inch])
            concept_table.setStyle(TableStyle([
                ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#34a853')),
                ('TEXTCOLOR', (0, 0), (-1, 0), colors.whitesmoke),
                ('ALIGN', (0, 0), (-1, -1), 'CENTER'),
                ('ALIGN', (0, 0), (0, -1), 'LEFT'),
                ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
                ('FONTSIZE', (0, 0), (-1, 0), 10),
                ('BOTTOMPADDING', (0, 0), (-1, 0), 8),
                ('GRID', (0, 0), (-1, -1), 0.5, colors.grey),
                ('FONTSIZE', (0, 1), (-1, -1), 9),
                ('ROWBACKGROUNDS', (0, 1), (-1, -1), [colors.white, colors.HexColor('#f8f9fa')])
            ]))
            story.append(concept_table)
            if i + 35 < len(concept_data):
                story.append(PageBreak())
        
        doc.build(story)
        return output_path

    # ============ 工具方法 ============
    
    def _calculate_layout(self, width: int, height: int):
        """计算力导向布局"""
        import random
        import math
        
        margin = 80
        for node in self.nodes.values():
            node.x = random.uniform(margin, width - margin)
            node.y = random.uniform(margin + 50, height - margin)
        
        iterations = 100
        k = 120
        
        for _ in range(iterations):
            forces = {node_id: [0.0, 0.0] for node_id in self.nodes}
            
            # 斥力
            for i, node1 in enumerate(self.nodes.values()):
                for node2 in list(self.nodes.values())[i+1:]:
                    dx = node2.x - node1.x
                    dy = node2.y - node1.y
                    dist = math.sqrt(dx*dx + dy*dy)
                    if dist > 0 and dist < 250:
                        force = k * k / dist
                        fx = force * dx / dist
                        fy = force * dy / dist
                        forces[node1.id][0] -= fx
                        forces[node1.id][1] -= fy
                        forces[node2.id][0] += fx
                        forces[node2.id][1] += fy
            
            # 引力
            for edge in self.edges:
                if edge.source in self.nodes and edge.target in self.nodes:
                    source = self.nodes[edge.source]
                    target = self.nodes[edge.target]
                    dx = target.x - source.x
                    dy = target.y - source.y
                    dist = math.sqrt(dx*dx + dy*dy)
                    if dist > 0:
                        force = dist * dist / k * 0.08
                        fx = force * dx / dist
                        fy = force * dy / dist
                        forces[source.id][0] += fx
                        forces[source.id][1] += fy
                        forces[target.id][0] -= fx
                        forces[target.id][1] -= fy
            
            # 应用力
            for node in self.nodes.values():
                fx, fy = forces[node.id]
                node.x = max(margin, min(width - margin, node.x + fx * 0.1))
                node.y = max(margin + 50, min(height - margin, node.y + fy * 0.1))
    
    def _hex_to_rgb(self, hex_color: str) -> Tuple[int, int, int]:
        """十六进制颜色转RGB"""
        hex_color = hex_color.lstrip('#')
        return tuple(int(hex_color[i:i+2], 16) for i in (0, 2, 4))


# ============ CLI 接口 ============

def create_parser() -> argparse.ArgumentParser:
    """创建命令行参数解析器"""
    parser = argparse.ArgumentParser(
        prog='export_graph',
        description='FormalMath 知识图谱多格式导出工具',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
示例:
  # 导出所有格式
  python export_graph.py -i data.json -o ./output

  # 只导出PDF和PNG
  python export_graph.py -i data.yaml -f pdf png -o ./export

  # 从项目概念数据导出
  python export_graph.py -i ../../project/concept_prerequisites.yaml -o ./output

支持格式:
  json    - JSON数据交换格式
  csv     - CSV表格格式
  graphml - GraphML网络图格式(Gephi兼容)
  html    - 交互式HTML网页
  svg     - SVG矢量图
  png     - PNG位图
  pdf     - PDF文档(需要Playwright或ReportLab)
  all     - 导出所有格式

依赖安装:
  pip install playwright pyyaml reportlab cairosvg pillow
  playwright install chromium
        '''
    )
    
    parser.add_argument(
        '--input', '-i',
        required=True,
        help='输入文件路径 (JSON 或 YAML)'
    )
    
    parser.add_argument(
        '--output', '-o',
        default='output/export',
        help='输出目录 (默认: output/export)'
    )
    
    parser.add_argument(
        '--formats', '-f',
        nargs='+',
        choices=['json', 'csv', 'graphml', 'html', 'svg', 'png', 'pdf', 'all'],
        default=['all'],
        help='导出格式 (默认: all)'
    )
    
    parser.add_argument(
        '--width', '-W',
        type=int,
        default=1200,
        help='图片宽度 (默认: 1200)'
    )
    
    parser.add_argument(
        '--height', '-H',
        type=int,
        default=800,
        help='图片高度 (默认: 800)'
    )
    
    parser.add_argument(
        '--version', '-v',
        action='version',
        version='%(prog)s 2.0.0'
    )
    
    return parser


def main():
    """主函数"""
    parser = create_parser()
    args = parser.parse_args()
    
    input_path = Path(args.input)
    if not input_path.exists():
        print(f"✗ 输入文件不存在: {input_path}")
        sys.exit(1)
    
    # 创建导出器
    exporter = GraphExporter(output_dir=args.output)
    
    # 加载数据
    if input_path.suffix == '.json':
        success = exporter.load_from_json(input_path)
    elif input_path.suffix in ['.yaml', '.yml']:
        if not YAML_AVAILABLE:
            print("✗ PyYAML未安装，无法加载YAML文件。请运行: pip install pyyaml")
            sys.exit(1)
        success = exporter.load_from_yaml(input_path)
    else:
        print(f"✗ 不支持的文件格式: {input_path.suffix}。请使用 .json 或 .yaml/.yml 文件")
        sys.exit(1)
    
    if not success:
        print("✗ 数据加载失败")
        sys.exit(1)
    
    # 确定导出格式
    formats = args.formats
    if 'all' in formats:
        formats = ['json', 'csv', 'graphml', 'html', 'svg', 'png', 'pdf']
    
    # 导出
    print(f"\n开始导出到: {args.output}")
    print("=" * 50)
    
    results = exporter.export_all(formats)
    
    print("=" * 50)
    print(f"\n导出完成! 共生成 {len(results)} 个文件:")
    for fmt, path in results.items():
        print(f"  ✓ {fmt.upper():8} : {path}")
    
    print()


if __name__ == '__main__':
    main()
