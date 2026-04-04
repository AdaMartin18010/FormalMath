#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
PDF 导出器
支持ReportLab和Playwright两种导出方式
"""

import asyncio
import tempfile
from pathlib import Path
from typing import List, Dict, Any, Optional, Union
from datetime import datetime
from collections import defaultdict

# 可选依赖
try:
    from reportlab.lib import colors
    from reportlab.lib.pagesizes import A4, letter
    from reportlab.platypus import (SimpleDocTemplate, Table, TableStyle, 
                                   Paragraph, Spacer, PageBreak, KeepTogether)
    from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
    from reportlab.lib.units import inch, cm
    REPORTLAB_AVAILABLE = True
except ImportError:
    REPORTLAB_AVAILABLE = False

try:
    from playwright.async_api import async_playwright
    PLAYWRIGHT_AVAILABLE = True
except ImportError:
    PLAYWRIGHT_AVAILABLE = False


class PDFExporter:
    """
    PDF格式导出器
    
    支持两种导出方式：
    1. ReportLab: 纯Python方案，无需外部依赖
    2. Playwright: 使用浏览器渲染HTML生成高质量PDF
    """
    
    # 类别颜色映射
    CATEGORY_COLORS = {
        "分析学": (227, 242, 253),      # #E3F2FD
        "代数学": (243, 229, 245),      # #F3E5F5
        "几何拓扑": (232, 245, 233),    # #E8F5E9
        "数论逻辑": (251, 233, 231),    # #FBE9E7
        "概率统计": (255, 248, 225),    # #FFF8E1
        "最优化": (224, 242, 241),      # #E0F2F1
        "控制论": (225, 245, 254),      # #E1F5FE
        "信息论": (243, 229, 245),      # #F3E5F5
        "密码学": (236, 239, 241),      # #ECEFF1
        "基础数学": (245, 245, 245),    # #F5F5F5
        "未分类": (204, 204, 204)       # #CCCCCC
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
    
    def export_pdf(self, output_path: Optional[Path] = None,
                  method: str = "auto") -> Path:
        """
        导出为PDF格式
        
        Args:
            output_path: 输出文件路径
            method: 导出方法 ('auto', 'playwright', 'reportlab')
            
        Returns:
            输出文件路径
        """
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph.pdf"
        
        # 自动选择方法
        if method == "auto":
            if PLAYWRIGHT_AVAILABLE:
                method = "playwright"
            elif REPORTLAB_AVAILABLE:
                method = "reportlab"
            else:
                raise ImportError("PDF导出需要Playwright或ReportLab")
        
        if method == "playwright":
            if not PLAYWRIGHT_AVAILABLE:
                raise ImportError("Playwright未安装")
            return asyncio.run(self._export_with_playwright(output_path))
        elif method == "reportlab":
            if not REPORTLAB_AVAILABLE:
                raise ImportError("ReportLab未安装")
            return self._export_with_reportlab(output_path)
        else:
            raise ValueError(f"未知的导出方法: {method}")
    
    def _export_with_reportlab(self, output_path: Path) -> Path:
        """使用ReportLab导出PDF"""
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
        
        # 自定义样式
        title_style = ParagraphStyle(
            'CustomTitle',
            parent=styles['Heading1'],
            fontSize=24,
            spaceAfter=30,
            alignment=1,  # 居中
            textColor=colors.HexColor('#1a73e8')
        )
        
        # 标题
        story.append(Paragraph("FormalMath 知识图谱", title_style))
        story.append(Spacer(1, 0.2*inch))
        
        # 元信息
        story.append(Paragraph(
            f"<b>生成日期:</b> {datetime.now().strftime('%Y年%m月%d日')}",
            styles['Normal']
        ))
        story.append(Paragraph(
            f"<b>概念总数:</b> {len(self.nodes)}",
            styles['Normal']
        ))
        story.append(Paragraph(
            f"<b>关系总数:</b> {len(self.edges)}",
            styles['Normal']
        ))
        story.append(Spacer(1, 0.3*inch))
        
        # 统计表格
        story.append(Paragraph("统计概览", styles['Heading2']))
        story.append(Spacer(1, 0.1*inch))
        
        # 按类别统计
        by_category = defaultdict(lambda: {'count': 0, 'hours': 0})
        for node in self.nodes:
            cat = node.get('category', '未分类')
            by_category[cat]['count'] += 1
            by_category[cat]['hours'] += node.get('estimated_hours', 0)
        
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
        
        # 按类别排序
        sorted_nodes = sorted(self.nodes, key=lambda x: (x.get('category', ''), x.get('name', '')))
        
        for node in sorted_nodes:
            diff = node.get('difficulty', 1)
            difficulty_stars = '★' * diff + '☆' * (5 - diff)
            concept_data.append([
                node.get('name', node.get('label', '')),
                node.get('category', '未分类'),
                difficulty_stars,
                f"{node.get('estimated_hours', 0):.0f}h"
            ])
        
        # 分批处理（每页约45行）
        header = concept_data[0]
        data_rows = concept_data[1:]
        
        for i in range(0, len(data_rows), 45):
            chunk = [header] + data_rows[i:i+45]
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
            
            story.append(KeepTogether([concept_table]))
            if i + 45 < len(data_rows):
                story.append(PageBreak())
        
        # 构建PDF
        doc.build(story)
        return output_path
    
    async def _export_with_playwright(self, output_path: Path) -> Path:
        """使用Playwright导出PDF"""
        # 生成HTML内容
        html_content = self._generate_html_for_pdf()
        
        # 创建临时HTML文件
        with tempfile.NamedTemporaryFile(mode='w', suffix='.html', 
                                         delete=False, encoding='utf-8') as f:
            f.write(html_content)
            temp_html = f.name
        
        try:
            async with async_playwright() as p:
                browser = await p.chromium.launch()
                page = await browser.new_page()
                
                await page.goto(f'file://{temp_html}')
                await page.wait_for_load_state('networkidle')
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
        """生成用于PDF渲染的HTML"""
        # 按类别统计
        by_category = defaultdict(lambda: {'count': 0, 'hours': 0})
        for node in self.nodes:
            cat = node.get('category', '未分类')
            by_category[cat]['count'] += 1
            by_category[cat]['hours'] += node.get('estimated_hours', 0)
        
        category_rows = "\n".join([
            f"<tr><td>{cat}</td><td>{data['count']}</td><td>{data['hours']:.0f}h</td></tr>"
            for cat, data in sorted(by_category.items(), key=lambda x: -x[1]['count'])
        ])
        
        concept_rows = "\n".join([
            f"""<tr>
                <td>{node.get('name', node.get('label', ''))}</td>
                <td>{node.get('category', '未分类')}</td>
                <td>{'★' * node.get('difficulty', 1)}{'☆' * (5 - node.get('difficulty', 1))}</td>
                <td>{node.get('estimated_hours', 0):.0f}h</td>
            </tr>"""
            for node in sorted(self.nodes, key=lambda x: x.get('category', ''))
        ])
        
        return f"""<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>FormalMath 知识图谱</title>
    <style>
        @page {{
            size: A4;
            margin: 2cm;
            @top-center {{
                content: "FormalMath 知识图谱";
                font-size: 10pt;
                color: #666;
            }}
            @bottom-center {{
                content: counter(page) " / " counter(pages);
                font-size: 10pt;
            }}
        }}
        
        * {{
            -webkit-print-color-adjust: exact !important;
            print-color-adjust: exact !important;
        }}
        
        body {{
            font-family: "Noto Sans CJK SC", "Source Han Sans SC", "Microsoft YaHei", sans-serif;
            font-size: 11pt;
            line-height: 1.6;
            color: #333;
        }}
        
        .header {{
            text-align: center;
            margin-bottom: 30px;
            padding-bottom: 20px;
            border-bottom: 3px solid #1a73e8;
        }}
        
        .header h1 {{
            font-size: 28pt;
            color: #1a73e8;
            margin: 0 0 15px 0;
        }}
        
        .meta {{
            color: #666;
            font-size: 11pt;
        }}
        
        h2 {{
            color: #333;
            font-size: 16pt;
            margin-top: 25px;
            margin-bottom: 15px;
            padding-bottom: 8px;
            border-bottom: 2px solid #e0e0e0;
        }}
        
        table {{
            width: 100%;
            border-collapse: collapse;
            margin: 15px 0;
        }}
        
        th {{
            background-color: #1a73e8;
            color: white;
            padding: 12px;
            text-align: left;
            font-weight: 600;
        }}
        
        td {{
            padding: 10px 12px;
            border-bottom: 1px solid #ddd;
        }}
        
        tr:nth-child(even) {{
            background-color: #f8f9fa;
        }}
        
        .stats-table th {{
            background-color: #1a73e8;
        }}
        
        .concepts-table th {{
            background-color: #34a853;
        }}
        
        .page-break {{
            page-break-before: always;
        }}
    </style>
</head>
<body>
    <div class="header">
        <h1>📚 FormalMath 知识图谱</h1>
        <div class="meta">
            <p>生成日期: {datetime.now().strftime('%Y年%m月%d日')}</p>
            <p>概念总数: {len(self.nodes)} | 关系总数: {len(self.edges)}</p>
        </div>
    </div>
    
    <h2>📊 统计概览</h2>
    <table class="stats-table">
        <thead>
            <tr>
                <th>类别</th>
                <th>概念数</th>
                <th>预计学时</th>
            </tr>
        </thead>
        <tbody>
            {category_rows}
        </tbody>
    </table>
    
    <div class="page-break"></div>
    
    <h2>📋 概念详情</h2>
    <table class="concepts-table">
        <thead>
            <tr>
                <th>概念名称</th>
                <th>类别</th>
                <th>难度</th>
                <th>学时</th>
            </tr>
        </thead>
        <tbody>
            {concept_rows}
        </tbody>
    </table>
</body>
</html>"""
    
    def export_html(self, output_path: Optional[Path] = None) -> Path:
        """
        导出为交互式HTML（可作为PDF的中间格式）
        """
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph.html"
        
        html_content = self._generate_html_for_pdf()
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(html_content)
        
        return output_path
