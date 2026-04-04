#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
HTML导出器 - 带打印优化
HTML Exporter with Print Optimization
"""

import json
from pathlib import Path
from typing import Dict, Any, List
from datetime import datetime
from dataclasses import dataclass


@dataclass
class HTMLExporter:
    """HTML导出器"""
    
    output_dir: Path
    
    # 类别颜色
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
    
    def __post_init__(self):
        self.output_dir = Path(self.output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
    
    def export(self, data: Dict[str, Any], output_name: str = "knowledge_graph") -> Path:
        """导出为HTML"""
        output_path = self.output_dir / f"{output_name}.html"
        
        nodes = data.get('nodes', [])
        edges = data.get('edges', [])
        metadata = data.get('metadata', {})
        
        html_content = self._generate_html(nodes, edges, metadata)
        
        output_path.write_text(html_content, encoding='utf-8')
        return output_path
    
    def _generate_html(self, nodes: List[Dict], edges: List[Dict], metadata: Dict) -> str:
        """生成HTML内容"""
        
        # 统计数据
        by_category = {}
        for node in nodes:
            cat = node.get('category', '未分类')
            by_category[cat] = by_category.get(cat, 0) + 1
        
        html = f'''<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>FormalMath 知识图谱</title>
    <style>
        /* 基础样式 */
        * {{
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }}
        
        body {{
            font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, "Noto Sans SC", "Microsoft YaHei", sans-serif;
            line-height: 1.6;
            color: #333;
            background: #f5f7fa;
        }}
        
        .container {{
            max-width: 1200px;
            margin: 0 auto;
            padding: 20px;
            background: white;
        }}
        
        /* 头部样式 */
        .header {{
            text-align: center;
            padding: 30px 0;
            border-bottom: 3px solid #1a73e8;
            margin-bottom: 30px;
        }}
        
        .header h1 {{
            font-size: 2.5em;
            color: #1a73e8;
            margin-bottom: 10px;
        }}
        
        .meta {{
            color: #666;
            font-size: 0.9em;
        }}
        
        /* 统计卡片 */
        .stats-grid {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
            gap: 20px;
            margin: 30px 0;
        }}
        
        .stat-card {{
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white;
            padding: 20px;
            border-radius: 10px;
            text-align: center;
        }}
        
        .stat-card h3 {{
            font-size: 2em;
            margin-bottom: 5px;
        }}
        
        .stat-card p {{
            opacity: 0.9;
        }}
        
        /* 类别分布 */
        .category-section {{
            margin: 30px 0;
        }}
        
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
            gap: 10px;
        }}
        
        .category-tag {{
            padding: 8px 16px;
            border-radius: 20px;
            font-size: 0.9em;
            border: 1px solid #ddd;
        }}
        
        /* 概念表格 */
        .concepts-table {{
            width: 100%;
            border-collapse: collapse;
            margin: 20px 0;
        }}
        
        .concepts-table th {{
            background: #1a73e8;
            color: white;
            padding: 12px;
            text-align: left;
            font-weight: 600;
        }}
        
        .concepts-table td {{
            padding: 12px;
            border-bottom: 1px solid #e0e0e0;
        }}
        
        .concepts-table tr:nth-child(even) {{
            background: #f8f9fa;
        }}
        
        .concepts-table tr:hover {{
            background: #e3f2fd;
        }}
        
        /* 难度星级 */
        .difficulty {{
            color: #ffc107;
        }}
        
        /* 关系图 */
        .graph-section {{
            margin: 30px 0;
            text-align: center;
        }}
        
        #graph-svg {{
            max-width: 100%;
            height: auto;
            border: 1px solid #e0e0e0;
            border-radius: 8px;
        }}
        
        /* 打印样式 */
        @media print {{
            @page {{
                size: A4;
                margin: 2cm;
            }}
            
            body {{
                background: white;
                font-size: 11pt;
            }}
            
            .container {{
                max-width: 100%;
                padding: 0;
            }}
            
            .header {{
                page-break-after: avoid;
            }}
            
            .stats-grid {{
                page-break-inside: avoid;
            }}
            
            .concepts-table {{
                page-break-inside: auto;
            }}
            
            .concepts-table tr {{
                page-break-inside: avoid;
                page-break-after: auto;
            }}
            
            .no-print {{
                display: none !important;
            }}
            
            .page-break {{
                page-break-before: always;
            }}
        }}
        
        /* 按钮样式 */
        .btn {{
            display: inline-block;
            padding: 10px 20px;
            background: #1a73e8;
            color: white;
            text-decoration: none;
            border-radius: 5px;
            margin: 5px;
            cursor: pointer;
            border: none;
            font-size: 1em;
        }}
        
        .btn:hover {{
            background: #1557b0;
        }}
        
        .btn-secondary {{
            background: #5f6368;
        }}
        
        .btn-secondary:hover {{
            background: #494c50;
        }}
        
        .actions {{
            text-align: center;
            margin: 20px 0;
            padding: 20px;
            background: #f8f9fa;
            border-radius: 8px;
        }}
    </style>
</head>
<body>
    <div class="container">
        <header class="header">
            <h1>📚 FormalMath 知识图谱</h1>
            <div class="meta">
                <p>生成时间: {datetime.now().strftime('%Y年%m月%d日')}</p>
                <p>概念总数: {len(nodes)} | 关系总数: {len(edges)}</p>
            </div>
        </header>
        
        <div class="actions no-print">
            <button class="btn" onclick="window.print()">🖨️ 打印 / 另存为PDF</button>
            <button class="btn btn-secondary" onclick="toggleGraph()">📊 显示/隐藏关系图</button>
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
        </section>
        
        <section class="category-section">
            <h2 class="section-title">类别分布</h2>
            <div class="category-list">
                {self._generate_category_tags(by_category)}
            </div>
        </section>
        
        <section class="page-break">
            <h2 class="section-title">概念详情</h2>
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
                    {self._generate_concept_rows(nodes)}
                </tbody>
            </table>
        </section>
        
        <section class="graph-section page-break" id="graph-section" style="display: none;">
            <h2 class="section-title">关系图谱</h2>
            <div id="graph-container">
                <!-- SVG将通过JS动态生成 -->
            </div>
        </section>
    </div>
    
    <script>
        // 图谱数据
        const graphData = {json.dumps(dict(nodes=nodes, edges=edges), ensure_ascii=False)};
        
        // 切换图谱显示
        function toggleGraph() {{
            const section = document.getElementById('graph-section');
            if (section.style.display === 'none') {{
                section.style.display = 'block';
                renderGraph();
            }} else {{
                section.style.display = 'none';
            }}
        }}
        
        // 简单力导向布局
        function renderGraph() {{
            const container = document.getElementById('graph-container');
            const width = 800;
            const height = 600;
            
            // 初始化位置
            const nodes = graphData.nodes.map((n, i) => ({{
                ...n,
                x: width/2 + Math.cos(i * 2 * Math.PI / graphData.nodes.length) * 200,
                y: height/2 + Math.sin(i * 2 * Math.PI / graphData.nodes.length) * 200
            }}));
            
            const nodeMap = Object.fromEntries(nodes.map(n => [n.id, n]));
            
            // 简单迭代
            for (let iter = 0; iter < 50; iter++) {{
                // 斥力
                for (let i = 0; i < nodes.length; i++) {{
                    for (let j = i + 1; j < nodes.length; j++) {{
                        const dx = nodes[j].x - nodes[i].x;
                        const dy = nodes[j].y - nodes[i].y;
                        const dist = Math.sqrt(dx*dx + dy*dy);
                        if (dist > 0 && dist < 150) {{
                            const force = 1000 / (dist * dist);
                            const fx = force * dx / dist;
                            const fy = force * dy / dist;
                            nodes[i].x -= fx;
                            nodes[i].y -= fy;
                            nodes[j].x += fx;
                            nodes[j].y += fy;
                        }}
                    }}
                }}
                
                // 引力（边）
                graphData.edges.forEach(edge => {{
                    const source = nodeMap[edge.from || edge.source];
                    const target = nodeMap[edge.to || edge.target];
                    if (source && target) {{
                        const dx = target.x - source.x;
                        const dy = target.y - source.y;
                        const dist = Math.sqrt(dx*dx + dy*dy);
                        if (dist > 0) {{
                            const force = (dist - 100) * 0.01;
                            const fx = force * dx / dist;
                            const fy = force * dy / dist;
                            source.x += fx;
                            source.y += fy;
                            target.x -= fx;
                            target.y -= fy;
                        }}
                    }}
                }});
                
                // 边界约束
                nodes.forEach(n => {{
                    n.x = Math.max(50, Math.min(width - 50, n.x));
                    n.y = Math.max(50, Math.min(height - 50, n.y));
                }});
            }}
            
            // 生成SVG
            const colors = {json.dumps(self.CATEGORY_COLORS, ensure_ascii=False)};
            
            let svg = `<svg width="${{width}}" height="${{height}}" style="background: #fafafa; border-radius: 8px;">`;
            
            // 边
            graphData.edges.forEach(edge => {{
                const s = nodeMap[edge.from || edge.source];
                const t = nodeMap[edge.to || edge.target];
                if (s && t) {{
                    svg += `<line x1="${{s.x}}" y1="${{s.y}}" x2="${{t.x}}" y2="${{t.y}}" stroke="#999" stroke-width="1" marker-end="url(#arrow)"/>`;
                }}
            }});
            
            // 节点
            nodes.forEach(n => {{
                const color = colors[n.category] || '#ccc';
                const r = 8 + (n.difficulty || 1) * 2;
                svg += `<circle cx="${{n.x}}" cy="${{n.y}}" r="${{r}}" fill="${{color}}" stroke="#333" stroke-width="1.5"/>`;
                svg += `<text x="${{n.x}}" y="${{n.y + r + 12}}" text-anchor="middle" font-size="10" fill="#333">${{n.label || n.name}}</text>`;
            }});
            
            // 箭头标记
            svg += `<defs><marker id="arrow" markerWidth="10" markerHeight="7" refX="9" refY="3.5" orient="auto"><polygon points="0 0, 10 3.5, 0 7" fill="#666"/></marker></defs>`;
            
            svg += '</svg>';
            container.innerHTML = svg;
        }}
    </script>
</body>
</html>
'''
        return html
    
    def _generate_category_tags(self, by_category: Dict[str, int]) -> str:
        """生成分类标签"""
        tags = []
        for category, count in sorted(by_category.items(), key=lambda x: -x[1]):
            color = self.CATEGORY_COLORS.get(category, "#f5f5f5")
            tags.append(f'<span class="category-tag" style="background: {color}">{category} ({count})</span>')
        return '\n'.join(tags)
    
    def _generate_concept_rows(self, nodes: List[Dict]) -> str:
        """生成概念表格行"""
        rows = []
        for node in sorted(nodes, key=lambda x: x.get('category', '')):
            difficulty = node.get('difficulty', 1)
            stars = '★' * difficulty + '☆' * (5 - difficulty)
            
            rows.append(f'''<tr>
                <td><strong>{node.get('label', node.get('name', ''))}</strong></td>
                <td>{node.get('category', '未分类')}</td>
                <td class="difficulty">{stars}</td>
                <td>{node.get('estimated_hours', '-')}h</td>
                <td>{node.get('msc_code', '-')}</td>
            </tr>''')
        return '\n'.join(rows)


def main():
    """示例用法"""
    import sys
    
    if len(sys.argv) < 2:
        print("用法: python html_exporter.py <input.json> [output.html]")
        return
    
    input_file = Path(sys.argv[1])
    output_file = sys.argv[2] if len(sys.argv) > 2 else None
    
    # 读取数据
    with open(input_file, 'r', encoding='utf-8') as f:
        data = json.load(f)
    
    # 导出
    exporter = HTMLExporter(output_dir=Path("output"))
    output_path = exporter.export(data, Path(output_file).stem if output_file else "knowledge_graph")
    
    print(f"HTML已导出: {output_path}")


if __name__ == '__main__':
    main()
