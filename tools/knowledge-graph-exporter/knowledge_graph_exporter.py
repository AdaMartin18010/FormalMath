#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
知识图谱多格式导出器
Knowledge Graph Multi-Format Exporter

支持PDF、PNG/SVG、GraphML、JSON、CSV等多种格式导出
"""

import json
import csv
import xml.etree.ElementTree as ET
from xml.dom import minidom
from pathlib import Path
from typing import List, Dict, Any, Optional, Tuple
from dataclasses import dataclass, field, asdict
from datetime import datetime
from collections import defaultdict
import base64
import io

# 可选依赖
try:
    from reportlab.lib import colors
    from reportlab.lib.pagesizes import A4
    from reportlab.platypus import SimpleDocTemplate, Table, TableStyle, Paragraph, Spacer, Image, PageBreak
    from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
    from reportlab.lib.units import inch, cm
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.ttfonts import TTFont
    from reportlab.graphics.shapes import Drawing, Circle, Line, String
    from reportlab.graphics.charts.textlabels import Label
    REPORTLAB_AVAILABLE = True
except ImportError:
    REPORTLAB_AVAILABLE = False

try:
    import cairosvg
    import svgwrite
    CAIROSVG_AVAILABLE = True
except ImportError:
    CAIROSVG_AVAILABLE = False

try:
    from PIL import Image as PILImage, ImageDraw, ImageFont
    PIL_AVAILABLE = True
except ImportError:
    PIL_AVAILABLE = False


@dataclass
class ConceptNode:
    """概念节点"""
    id: str
    name: str
    category: str
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
    知识图谱多格式导出器
    
    支持导出为:
    - PDF (使用ReportLab)
    - PNG/SVG (图片格式)
    - GraphML (Gephi兼容)
    - JSON (数据交换)
    - CSV (表格格式)
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
        "基础数学": "#F5F5F5"
    }
    
    # 难度颜色映射
    DIFFICULTY_COLORS = {
        1: "#4CAF50",  # 绿色
        2: "#8BC34A",
        3: "#FFC107",  # 黄色
        4: "#FF9800",
        5: "#F44336"   # 红色
    }
    
    def __init__(self, output_dir: Path):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
        self.nodes: Dict[str, ConceptNode] = {}
        self.edges: List[ConceptEdge] = []
        self.metadata: Dict[str, Any] = {}
        
    def load_from_json(self, json_path: Path) -> bool:
        """从JSON文件加载知识图谱数据"""
        try:
            with open(json_path, 'r', encoding='utf-8') as f:
                data = json.load(f)
            
            # 加载元数据
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
            
            print(f"✓ 加载了 {len(self.nodes)} 个节点, {len(self.edges)} 条边")
            return True
            
        except Exception as e:
            print(f"✗ 加载失败: {e}")
            return False
    
    def load_from_yaml(self, yaml_path: Path) -> bool:
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
            formats = ['json', 'csv', 'graphml', 'pdf', 'svg', 'png']
        
        results = {}
        
        for fmt in formats:
            try:
                if fmt == 'json':
                    results['json'] = self.export_json()
                elif fmt == 'csv':
                    results['csv'] = self.export_csv()
                elif fmt == 'graphml':
                    results['graphml'] = self.export_graphml()
                elif fmt == 'pdf':
                    results['pdf'] = self.export_pdf()
                elif fmt == 'svg':
                    results['svg'] = self.export_svg()
                elif fmt == 'png':
                    results['png'] = self.export_png()
                print(f"✓ {fmt.upper()} 导出成功")
            except Exception as e:
                print(f"✗ {fmt.upper()} 导出失败: {e}")
        
        return results
    
    def export_json(self, output_path: Path = None) -> Path:
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
    
    def export_csv(self, output_dir: Path = None) -> Path:
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
            
            # 按类别统计
            by_category = defaultdict(int)
            for node in self.nodes.values():
                by_category[node.category] += 1
            
            writer.writerow([])
            writer.writerow(['Category', 'Count'])
            for cat, count in sorted(by_category.items(), key=lambda x: -x[1]):
                writer.writerow([cat, count])
        
        return output_dir
    
    def export_graphml(self, output_path: Path = None) -> Path:
        """导出为GraphML格式（Gephi兼容）"""
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph.graphml"
        
        # 创建GraphML根元素
        root = ET.Element("graphml")
        root.set("xmlns", "http://graphml.graphdrawing.org/xmlns")
        root.set("xmlns:xsi", "http://www.w3.org/2001/XMLSchema-instance")
        root.set("xsi:schemaLocation", "http://graphml.graphdrawing.org/xmlns http://graphml.graphdrawing.org/xmlns/1.0/graphml.xsd")
        
        # 定义属性
        # 节点属性
        key_id = ET.SubElement(root, "key")
        key_id.set("id", "id")
        key_id.set("for", "node")
        key_id.set("attr.name", "id")
        key_id.set("attr.type", "string")
        
        key_label = ET.SubElement(root, "key")
        key_label.set("id", "label")
        key_label.set("for", "node")
        key_label.set("attr.name", "label")
        key_label.set("attr.type", "string")
        
        key_category = ET.SubElement(root, "key")
        key_category.set("id", "category")
        key_category.set("for", "node")
        key_category.set("attr.name", "category")
        key_category.set("attr.type", "string")
        
        key_difficulty = ET.SubElement(root, "key")
        key_difficulty.set("id", "difficulty")
        key_difficulty.set("for", "node")
        key_difficulty.set("attr.name", "difficulty")
        key_difficulty.set("attr.type", "int")
        
        key_hours = ET.SubElement(root, "key")
        key_hours.set("id", "estimated_hours")
        key_hours.set("for", "node")
        key_hours.set("attr.name", "estimated_hours")
        key_hours.set("attr.type", "float")
        
        key_color = ET.SubElement(root, "key")
        key_color.set("id", "color")
        key_color.set("for", "node")
        key_color.set("attr.name", "color")
        key_color.set("attr.type", "string")
        
        # 边属性
        key_edge_label = ET.SubElement(root, "key")
        key_edge_label.set("id", "edge_label")
        key_edge_label.set("for", "edge")
        key_edge_label.set("attr.name", "label")
        key_edge_label.set("attr.type", "string")
        
        key_edge_level = ET.SubElement(root, "key")
        key_edge_level.set("id", "edge_level")
        key_edge_level.set("for", "edge")
        key_edge_level.set("attr.name", "level")
        key_edge_level.set("attr.type", "string")
        
        # 创建图
        graph = ET.SubElement(root, "graph")
        graph.set("id", "G")
        graph.set("edgedefault", "directed")
        
        # 添加节点
        for node in self.nodes.values():
            node_elem = ET.SubElement(graph, "node")
            node_elem.set("id", node.id)
            
            # 添加属性
            data_label = ET.SubElement(node_elem, "data")
            data_label.set("key", "label")
            data_label.text = node.name
            
            data_category = ET.SubElement(node_elem, "data")
            data_category.set("key", "category")
            data_category.text = node.category
            
            data_difficulty = ET.SubElement(node_elem, "data")
            data_difficulty.set("key", "difficulty")
            data_difficulty.text = str(node.difficulty)
            
            data_hours = ET.SubElement(node_elem, "data")
            data_hours.set("key", "estimated_hours")
            data_hours.text = str(node.estimated_hours)
            
            data_color = ET.SubElement(node_elem, "data")
            data_color.set("key", "color")
            data_color.text = self.CATEGORY_COLORS.get(node.category, "#CCCCCC")
        
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
        
        # 写入文件
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(pretty_xml)
        
        return output_path
    
    def export_pdf(self, output_path: Path = None) -> Path:
        """导出为PDF格式（使用ReportLab）"""
        if not REPORTLAB_AVAILABLE:
            raise ImportError("ReportLab not installed. Run: pip install reportlab")
        
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
            fontSize=24,
            spaceAfter=30,
            alignment=1  # 居中
        )
        story.append(Paragraph("FormalMath 知识图谱", title_style))
        story.append(Spacer(1, 0.2*inch))
        
        # 元信息
        story.append(Paragraph(f"<b>生成日期:</b> {datetime.now().strftime('%Y年%m月%d日')}", styles['Normal']))
        story.append(Paragraph(f"<b>概念总数:</b> {len(self.nodes)}", styles['Normal']))
        story.append(Paragraph(f"<b>关系总数:</b> {len(self.edges)}", styles['Normal']))
        story.append(Spacer(1, 0.3*inch))
        
        # 统计表格
        story.append(Paragraph("统计概览", styles['Heading2']))
        story.append(Spacer(1, 0.1*inch))
        
        # 按类别统计
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
            ('FONTSIZE', (0, 0), (-1, 0), 12),
            ('BOTTOMPADDING', (0, 0), (-1, 0), 12),
            ('BACKGROUND', (0, 1), (-1, -1), colors.HexColor('#f8f9fa')),
            ('GRID', (0, 0), (-1, -1), 1, colors.grey),
            ('FONTNAME', (0, 1), (-1, -1), 'Helvetica'),
            ('FONTSIZE', (0, 1), (-1, -1), 10),
            ('ROWBACKGROUNDS', (0, 1), (-1, -1), [colors.white, colors.HexColor('#f0f0f0')])
        ]))
        story.append(stats_table)
        story.append(Spacer(1, 0.3*inch))
        
        # 概念详情表格
        story.append(PageBreak())
        story.append(Paragraph("概念详情", styles['Heading2']))
        story.append(Spacer(1, 0.1*inch))
        
        # 分页显示概念
        concept_data = [['概念名称', '类别', '难度', '学时']]
        for node in sorted(self.nodes.values(), key=lambda x: x.category):
            difficulty_stars = '★' * node.difficulty + '☆' * (5 - node.difficulty)
            concept_data.append([node.name, node.category, difficulty_stars, f"{node.estimated_hours:.0f}h"])
        
        # 分批处理（每页约40行）
        for i in range(0, len(concept_data), 40):
            chunk = [concept_data[0]] + concept_data[i:i+40] if i > 0 else concept_data[i:i+41]
            concept_table = Table(chunk, colWidths=[2.5*inch, 1.5*inch, 1*inch, 0.8*inch])
            concept_table.setStyle(TableStyle([
                ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#34a853')),
                ('TEXTCOLOR', (0, 0), (-1, 0), colors.whitesmoke),
                ('ALIGN', (0, 0), (-1, -1), 'CENTER'),
                ('ALIGN', (0, 0), (0, -1), 'LEFT'),
                ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
                ('FONTSIZE', (0, 0), (-1, 0), 11),
                ('BOTTOMPADDING', (0, 0), (-1, 0), 10),
                ('GRID', (0, 0), (-1, -1), 0.5, colors.grey),
                ('FONTNAME', (0, 1), (-1, -1), 'Helvetica'),
                ('FONTSIZE', (0, 1), (-1, -1), 9),
                ('ROWBACKGROUNDS', (0, 1), (-1, -1), [colors.white, colors.HexColor('#f8f9fa')])
            ]))
            story.append(concept_table)
            if i + 40 < len(concept_data):
                story.append(PageBreak())
        
        # 构建PDF
        doc.build(story)
        return output_path
    
    def export_svg(self, output_path: Path = None, width: int = 1200, height: int = 800) -> Path:
        """导出为SVG格式"""
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph.svg"
        
        # 计算布局
        self._calculate_layout(width, height)
        
        # 创建SVG
        svg_parts = []
        svg_parts.append(f'''<?xml version="1.0" encoding="UTF-8"?>
<svg width="{width}" height="{height}" xmlns="http://www.w3.org/2000/svg">
    <defs>
        <marker id="arrowhead" markerWidth="10" markerHeight="7" refX="9" refY="3.5" orient="auto">
            <polygon points="0 0, 10 3.5, 0 7" fill="#666" />
        </marker>
    </defs>
    <rect width="100%" height="100%" fill="#fafafa"/>
    <text x="{width/2}" y="30" text-anchor="middle" font-family="Arial, sans-serif" font-size="20" font-weight="bold" fill="#333">
        FormalMath 知识图谱
    </text>
    <text x="{width/2}" y="55" text-anchor="middle" font-family="Arial, sans-serif" font-size="12" fill="#666">
        {len(self.nodes)} 概念 | {len(self.edges)} 关系 | 生成于 {datetime.now().strftime('%Y-%m-%d')}
    </text>
''')
        
        # 绘制边
        for edge in self.edges:
            if edge.source in self.nodes and edge.target in self.nodes:
                source = self.nodes[edge.source]
                target = self.nodes[edge.target]
                svg_parts.append(f'''    <line x1="{source.x}" y1="{source.y}" x2="{target.x}" y2="{target.y}" 
        stroke="#999" stroke-width="1.5" marker-end="url(#arrowhead)" opacity="0.6"/>
''')
        
        # 绘制节点
        for node in self.nodes.values():
            color = self.CATEGORY_COLORS.get(node.category, "#CCCCCC")
            r = 8 + node.difficulty * 2  # 根据难度调整大小
            
            svg_parts.append(f'''    <circle cx="{node.x}" cy="{node.y}" r="{r}" 
        fill="{color}" stroke="#333" stroke-width="1.5"/>
    <text x="{node.x}" y="{node.y + r + 15}" text-anchor="middle" 
        font-family="Arial, sans-serif" font-size="10" fill="#333">{node.name}</text>
''')
        
        # 绘制图例
        legend_x = width - 180
        legend_y = 100
        svg_parts.append(f'''    <rect x="{legend_x - 10}" y="{legend_y - 25}" width="170" height="{len(self.CATEGORY_COLORS) * 25 + 40}" 
        fill="white" stroke="#ddd" stroke-width="1" rx="5"/>
    <text x="{legend_x}" y="{legend_y - 5}" font-family="Arial, sans-serif" font-size="12" font-weight="bold" fill="#333">类别图例</text>
''')
        
        for i, (category, color) in enumerate(self.CATEGORY_COLORS.items()):
            y = legend_y + i * 25
            svg_parts.append(f'''    <circle cx="{legend_x + 10}" cy="{y}" r="8" fill="{color}" stroke="#333" stroke-width="1"/>
    <text x="{legend_x + 25}" y="{y + 4}" font-family="Arial, sans-serif" font-size="10" fill="#333">{category}</text>
''')
        
        svg_parts.append('</svg>')
        
        # 写入文件
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(''.join(svg_parts))
        
        return output_path
    
    def export_png(self, output_path: Path = None, width: int = 1200, height: int = 800) -> Path:
        """导出为PNG格式"""
        if CAIROSVG_AVAILABLE:
            # 使用cairosvg转换SVG为PNG
            svg_path = self.export_svg(output_path=self.output_dir / "temp.svg", width=width, height=height)
            if output_path is None:
                output_path = self.output_dir / "knowledge_graph.png"
            
            cairosvg.svg2png(url=str(svg_path), write_to=str(output_path), output_width=width, output_height=height)
            svg_path.unlink()  # 删除临时SVG文件
            return output_path
            
        elif PIL_AVAILABLE:
            # 使用PIL绘制
            return self._export_png_with_pil(output_path, width, height)
        else:
            raise ImportError("Neither cairosvg nor PIL available. Install one to export PNG.")
    
    def _export_png_with_pil(self, output_path: Path = None, width: int = 1200, height: int = 800) -> Path:
        """使用PIL导出PNG"""
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph.png"
        
        # 创建图像
        img = PILImage.new('RGB', (width, height), color='#fafafa')
        draw = ImageDraw.Draw(img)
        
        # 计算布局
        self._calculate_layout(width, height)
        
        # 绘制标题
        title = "FormalMath 知识图谱"
        draw.text((width//2, 30), title, fill='#333333', anchor='mm')
        subtitle = f"{len(self.nodes)} 概念 | {len(self.edges)} 关系"
        draw.text((width//2, 55), subtitle, fill='#666666', anchor='mm')
        
        # 绘制边
        for edge in self.edges:
            if edge.source in self.nodes and edge.target in self.nodes:
                source = self.nodes[edge.source]
                target = self.nodes[edge.target]
                draw.line([(source.x, source.y), (target.x, target.y)], fill='#999999', width=1)
        
        # 绘制节点
        for node in self.nodes.values():
            color = self.CATEGORY_COLORS.get(node.category, "#CCCCCC")
            r = 8 + node.difficulty * 2
            
            # 转换颜色
            rgb = self._hex_to_rgb(color)
            
            # 绘制圆形
            draw.ellipse([node.x - r, node.y - r, node.x + r, node.y + r], 
                        fill=rgb, outline='#333333', width=2)
            
            # 绘制标签
            draw.text((node.x, node.y + r + 10), node.name, fill='#333333', anchor='mm')
        
        # 保存
        img.save(output_path, 'PNG')
        return output_path
    
    def _calculate_layout(self, width: int, height: int):
        """计算节点布局（使用简单的力导向布局）"""
        import random
        import math
        
        # 初始化随机位置
        margin = 100
        for node in self.nodes.values():
            node.x = random.uniform(margin, width - margin)
            node.y = random.uniform(margin + 50, height - margin)
        
        # 简单的力导向迭代
        iterations = 100
        k = 100  # 理想边长
        
        for _ in range(iterations):
            # 计算力
            forces = {node_id: [0.0, 0.0] for node_id in self.nodes}
            
            # 斥力（节点之间）
            for i, node1 in enumerate(self.nodes.values()):
                for node2 in list(self.nodes.values())[i+1:]:
                    dx = node2.x - node1.x
                    dy = node2.y - node1.y
                    dist = math.sqrt(dx*dx + dy*dy)
                    if dist > 0 and dist < 200:
                        force = k * k / dist
                        fx = force * dx / dist
                        fy = force * dy / dist
                        forces[node1.id][0] -= fx
                        forces[node1.id][1] -= fy
                        forces[node2.id][0] += fx
                        forces[node2.id][1] += fy
            
            # 引力（边连接）
            for edge in self.edges:
                if edge.source in self.nodes and edge.target in self.nodes:
                    source = self.nodes[edge.source]
                    target = self.nodes[edge.target]
                    dx = target.x - source.x
                    dy = target.y - source.y
                    dist = math.sqrt(dx*dx + dy*dy)
                    if dist > 0:
                        force = dist * dist / k
                        fx = force * dx / dist * 0.1
                        fy = force * dy / dist * 0.1
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
        """将十六进制颜色转换为RGB元组"""
        hex_color = hex_color.lstrip('#')
        return tuple(int(hex_color[i:i+2], 16) for i in (0, 2, 4))


def main():
    """主函数 - 示例用法"""
    import argparse
    
    parser = argparse.ArgumentParser(description='知识图谱多格式导出工具')
    parser.add_argument('--input', '-i', required=True, help='输入文件路径 (JSON或YAML)')
    parser.add_argument('--output', '-o', default='output/export', help='输出目录')
    parser.add_argument('--formats', '-f', nargs='+', 
                       choices=['json', 'csv', 'graphml', 'pdf', 'svg', 'png', 'all'],
                       default=['all'], help='导出格式')
    
    args = parser.parse_args()
    
    # 创建导出器
    exporter = KnowledgeGraphExporter(output_dir=Path(args.output))
    
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
        formats = ['json', 'csv', 'graphml', 'pdf', 'svg', 'png']
    
    # 导出
    print(f"\n开始导出到: {args.output}")
    results = exporter.export_all(formats)
    
    print("\n导出完成!")
    print("生成文件:")
    for fmt, path in results.items():
        print(f"  - {fmt.upper()}: {path}")


if __name__ == '__main__':
    main()
