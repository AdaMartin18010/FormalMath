#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
导出界面组件
提供命令行交互界面和HTML导出界面
"""

import json
from pathlib import Path
from typing import List, Dict, Any, Optional, Callable
from datetime import datetime
from collections import defaultdict


class ExportUI:
    """
    导出界面组件
    
    提供：
    1. 命令行交互界面
    2. HTML导出界面（用于浏览器）
    3. Web组件模板
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
    
    def generate_export_portal(self, output_path: Optional[Path] = None,
                               data_source: str = "knowledge_graph.json") -> Path:
        """
        生成导出门户HTML页面
        
        提供交互式导出界面，支持浏览器中直接导出
        """
        if output_path is None:
            output_path = self.output_dir / "export_portal.html"
        
        html = self._get_portal_template(data_source)
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(html)
        
        return output_path
    
    def generate_embedded_widget(self, output_path: Optional[Path] = None) -> Path:
        """
        生成可嵌入的导出组件
        
        可以作为iframe嵌入到其他页面
        """
        if output_path is None:
            output_path = self.output_dir / "export_widget.html"
        
        html = self._get_widget_template()
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(html)
        
        return output_path
    
    def _get_portal_template(self, data_source: str) -> str:
        """获取导出门户模板"""
        return f'''<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>FormalMath 知识图谱导出中心</title>
    <style>
        * {{
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }}
        
        body {{
            font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto,
                         "Noto Sans SC", "Microsoft YaHei", sans-serif;
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            min-height: 100vh;
            padding: 20px;
        }}
        
        .container {{
            max-width: 1200px;
            margin: 0 auto;
        }}
        
        .header {{
            text-align: center;
            padding: 40px 0;
            color: white;
        }}
        
        .header h1 {{
            font-size: 2.5em;
            margin-bottom: 15px;
            text-shadow: 0 2px 4px rgba(0,0,0,0.2);
        }}
        
        .header p {{
            font-size: 1.1em;
            opacity: 0.9;
        }}
        
        .export-grid {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(280px, 1fr));
            gap: 25px;
            margin: 40px 0;
        }}
        
        .export-card {{
            background: white;
            border-radius: 16px;
            padding: 30px;
            box-shadow: 0 10px 40px rgba(0,0,0,0.15);
            transition: transform 0.3s, box-shadow 0.3s;
            cursor: pointer;
        }}
        
        .export-card:hover {{
            transform: translateY(-5px);
            box-shadow: 0 15px 50px rgba(0,0,0,0.2);
        }}
        
        .export-card h3 {{
            color: #333;
            font-size: 1.4em;
            margin-bottom: 10px;
            display: flex;
            align-items: center;
            gap: 10px;
        }}
        
        .export-card p {{
            color: #666;
            font-size: 0.95em;
            line-height: 1.6;
            margin-bottom: 20px;
        }}
        
        .export-btn {{
            display: inline-block;
            padding: 12px 24px;
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white;
            text-decoration: none;
            border-radius: 8px;
            font-weight: 500;
            transition: opacity 0.2s;
            border: none;
            cursor: pointer;
            font-size: 1em;
        }}
        
        .export-btn:hover {{
            opacity: 0.9;
        }}
        
        .export-btn.secondary {{
            background: #f0f0f0;
            color: #333;
        }}
        
        .icon {{
            font-size: 1.5em;
        }}
        
        .features {{
            display: flex;
            flex-wrap: wrap;
            gap: 8px;
            margin-top: 15px;
        }}
        
        .feature-tag {{
            font-size: 0.75em;
            padding: 4px 10px;
            background: #f0f0f0;
            border-radius: 12px;
            color: #555;
        }}
        
        .preview-section {{
            background: white;
            border-radius: 16px;
            padding: 30px;
            margin-top: 30px;
            box-shadow: 0 10px 40px rgba(0,0,0,0.15);
        }}
        
        .preview-section h2 {{
            color: #333;
            margin-bottom: 20px;
            font-size: 1.5em;
        }}
        
        #graph-preview {{
            width: 100%;
            height: 500px;
            background: #fafafa;
            border-radius: 8px;
            border: 1px solid #e0e0e0;
        }}
        
        .status-bar {{
            position: fixed;
            bottom: 0;
            left: 0;
            right: 0;
            background: rgba(0,0,0,0.8);
            color: white;
            padding: 15px 20px;
            display: none;
            align-items: center;
            justify-content: center;
            gap: 10px;
        }}
        
        .status-bar.show {{
            display: flex;
        }}
        
        .spinner {{
            width: 20px;
            height: 20px;
            border: 2px solid white;
            border-top-color: transparent;
            border-radius: 50%;
            animation: spin 1s linear infinite;
        }}
        
        @keyframes spin {{
            to {{ transform: rotate(360deg); }}
        }}
    </style>
</head>
<body>
    <div class="container">
        <header class="header">
            <h1>📚 FormalMath 知识图谱导出中心</h1>
            <p>选择您需要的格式，一键导出知识图谱数据</p>
        </header>
        
        <div class="export-grid">
            <div class="export-card" onclick="exportData('json')">
                <h3><span class="icon">📄</span> JSON格式</h3>
                <p>完整的数据交换格式，包含所有节点、关系和元数据，适用于程序处理和数据备份。</p>
                <button class="export-btn">导出 JSON</button>
                <div class="features">
                    <span class="feature-tag">数据交换</span>
                    <span class="feature-tag">程序处理</span>
                </div>
            </div>
            
            <div class="export-card" onclick="exportData('csv')">
                <h3><span class="icon">📊</span> CSV格式</h3>
                <p>表格格式导出，节点和边分开存储，便于Excel分析和数据处理。</p>
                <button class="export-btn">导出 CSV</button>
                <div class="features">
                    <span class="feature-tag">Excel兼容</span>
                    <span class="feature-tag">数据分析</span>
                </div>
            </div>
            
            <div class="export-card" onclick="exportData('graphml')">
                <h3><span class="icon">🕸️</span> GraphML格式</h3>
                <p>网络分析标准格式，兼容Gephi、Cytoscape等专业网络可视化工具。</p>
                <button class="export-btn">导出 GraphML</button>
                <div class="features">
                    <span class="feature-tag">Gephi</span>
                    <span class="feature-tag">网络分析</span>
                </div>
            </div>
            
            <div class="export-card" onclick="exportData('svg')">
                <h3><span class="icon">🎨</span> SVG格式</h3>
                <p>矢量图格式，无损缩放，适合网页嵌入和高清打印。</p>
                <button class="export-btn">导出 SVG</button>
                <div class="features">
                    <span class="feature-tag">矢量图</span>
                    <span class="feature-tag">无损缩放</span>
                </div>
            </div>
            
            <div class="export-card" onclick="exportData('png')">
                <h3><span class="icon">🖼️</span> PNG格式</h3>
                <p>高质量位图，透明背景支持，适合演示文稿和文档插图。</p>
                <button class="export-btn">导出 PNG</button>
                <div class="features">
                    <span class="feature-tag">演示文稿</span>
                    <span class="feature-tag">透明背景</span>
                </div>
            </div>
            
            <div class="export-card" onclick="exportData('pdf')">
                <h3><span class="icon">📑</span> PDF格式</h3>
                <p>打印优化格式，包含完整的概念列表和统计数据，适合存档和分享。</p>
                <button class="export-btn">导出 PDF</button>
                <div class="features">
                    <span class="feature-tag">打印</span>
                    <span class="feature-tag">存档</span>
                </div>
            </div>
        </div>
        
        <div class="preview-section">
            <h2>🔍 图谱预览</h2>
            <div id="graph-preview">
                <canvas id="graph-canvas"></canvas>
            </div>
        </div>
    </div>
    
    <div class="status-bar" id="statusBar">
        <div class="spinner"></div>
        <span id="statusText">正在准备导出...</span>
    </div>
    
    <script>
        // 数据存储
        let graphData = null;
        
        // 加载数据
        async function loadData() {{
            try {{
                const response = await fetch('{data_source}');
                graphData = await response.json();
                renderPreview();
            }} catch (error) {{
                console.error('加载数据失败:', error);
                document.getElementById('graph-preview').innerHTML = 
                    '<p style="text-align:center;padding-top:200px;color:#999;">数据加载失败，请检查数据源</p>';
            }}
        }}
        
        // 渲染预览
        function renderPreview() {{
            const canvas = document.getElementById('graph-canvas');
            const ctx = canvas.getContext('2d');
            const container = document.getElementById('graph-preview');
            
            canvas.width = container.clientWidth;
            canvas.height = 500;
            
            // 绘制背景
            ctx.fillStyle = '#fafafa';
            ctx.fillRect(0, 0, canvas.width, canvas.height);
            
            if (!graphData || !graphData.nodes) return;
            
            const nodes = graphData.nodes;
            const edges = graphData.edges || [];
            
            // 简单的圆形布局
            const centerX = canvas.width / 2;
            const centerY = canvas.height / 2;
            const radius = Math.min(canvas.width, canvas.height) / 2 - 80;
            
            const positions = {{}};
            nodes.forEach((node, i) => {{
                const angle = (i / nodes.length) * 2 * Math.PI;
                positions[node.id] = {{
                    x: centerX + Math.cos(angle) * radius,
                    y: centerY + Math.sin(angle) * radius
                }};
            }});
            
            // 绘制边
            ctx.strokeStyle = '#bbb';
            ctx.lineWidth = 1;
            edges.forEach(edge => {{
                const source = positions[edge.source || edge.from];
                const target = positions[edge.target || edge.to];
                if (source && target) {{
                    ctx.beginPath();
                    ctx.moveTo(source.x, source.y);
                    ctx.lineTo(target.x, target.y);
                    ctx.stroke();
                }}
            }});
            
            // 绘制节点
            const colors = {json.dumps(self.CATEGORY_COLORS, ensure_ascii=False)};
            nodes.forEach(node => {{
                const pos = positions[node.id];
                if (!pos) return;
                
                const color = colors[node.category] || '#CCCCCC';
                const r = 8 + (node.difficulty || 1) * 2;
                
                ctx.beginPath();
                ctx.arc(pos.x, pos.y, r, 0, 2 * Math.PI);
                ctx.fillStyle = color;
                ctx.fill();
                ctx.strokeStyle = '#333';
                ctx.lineWidth = 2;
                ctx.stroke();
                
                ctx.fillStyle = '#333';
                ctx.font = '10px Arial';
                ctx.textAlign = 'center';
                ctx.fillText(node.name || node.label, pos.x, pos.y + r + 14);
            }});
        }}
        
        // 导出数据
        function exportData(format) {{
            const statusBar = document.getElementById('statusBar');
            const statusText = document.getElementById('statusText');
            
            statusBar.classList.add('show');
            statusText.textContent = `正在导出${{format.toUpperCase()}}格式...`;
            
            // 模拟导出过程
            setTimeout(() => {{
                if (format === 'json' && graphData) {{
                    downloadJSON(graphData, 'knowledge_graph.json');
                }} else if (format === 'csv' && graphData) {{
                    downloadCSV(graphData, 'knowledge_graph.csv');
                }} else {{
                    alert(`${{format.toUpperCase()}}导出功能需要后端支持\\n请使用命令行工具导出`);
                }}
                statusBar.classList.remove('show');
            }}, 1000);
        }}
        
        // 下载JSON
        function downloadJSON(data, filename) {{
            const blob = new Blob([JSON.stringify(data, null, 2)], {{type: 'application/json'}});
            const url = URL.createObjectURL(blob);
            const a = document.createElement('a');
            a.href = url;
            a.download = filename;
            a.click();
            URL.revokeObjectURL(url);
        }}
        
        // 下载CSV
        function downloadCSV(data, filename) {{
            let csv = 'ID,Name,Category,Difficulty,Hours\\n';
            data.nodes.forEach(node => {{
                csv += `${{node.id}},"${{node.name || node.label}}",${{node.category || '未分类'}},${{node.difficulty || 1}},${{node.estimated_hours || 0}}\\n`;
            }});
            const blob = new Blob(['\\ufeff' + csv], {{type: 'text/csv;charset=utf-8;'}});
            const url = URL.createObjectURL(blob);
            const a = document.createElement('a');
            a.href = url;
            a.download = filename;
            a.click();
            URL.revokeObjectURL(url);
        }}
        
        // 初始化
        window.onload = loadData;
        window.onresize = renderPreview;
    </script>
</body>
</html>'''
    
    def _get_widget_template(self) -> str:
        """获取嵌入式组件模板"""
        return '''<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>导出组件</title>
    <style>
        body { margin: 0; font-family: sans-serif; }
        .export-widget { padding: 20px; background: #f5f5f5; }
        .export-widget h4 { margin: 0 0 15px 0; color: #333; }
        .export-widget button {
            padding: 8px 16px;
            margin: 5px;
            border: none;
            border-radius: 4px;
            background: #1a73e8;
            color: white;
            cursor: pointer;
        }
        .export-widget button:hover { background: #1557b0; }
    </style>
</head>
<body>
    <div class="export-widget">
        <h4>导出知识图谱</h4>
        <button onclick="parent.postMessage({type:'export', format:'json'}, '*')">JSON</button>
        <button onclick="parent.postMessage({type:'export', format:'csv'}, '*')">CSV</button>
        <button onclick="parent.postMessage({type:'export', format:'svg'}, '*')">SVG</button>
    </div>
</body>
</html>'''
    
    def print_cli_menu(self, formats: Dict[str, str]) -> str:
        """
        打印命令行菜单
        
        Args:
            formats: 格式名称到描述的映射
        """
        menu = """
╔══════════════════════════════════════════════════════════╗
║         FormalMath 知识图谱导出工具                      ║
╠══════════════════════════════════════════════════════════╣
║  请选择导出格式:                                          ║
╠══════════════════════════════════════════════════════════╣"""
        
        for i, (fmt, desc) in enumerate(formats.items(), 1):
            menu += f"\n║  [{i}] {fmt.upper():8} - {desc:40} ║"
        
        menu += """
╠══════════════════════════════════════════════════════════╣
║  [0] 全部导出    [q] 退出                                ║
╚══════════════════════════════════════════════════════════╝
"""
        return menu
    
    def cli_interactive(self, export_callback: Callable[[List[str]], None]):
        """
        命令行交互界面
        
        Args:
            export_callback: 导出回调函数，接收选中的格式列表
        """
        formats = {
            'json': 'JSON数据格式，适合程序处理',
            'csv': 'CSV表格格式，适合Excel分析',
            'graphml': 'GraphML格式，Gephi兼容',
            'svg': 'SVG矢量图，可无损缩放',
            'png': 'PNG位图，适合演示文稿',
            'pdf': 'PDF文档，打印优化'
        }
        
        fmt_list = list(formats.keys())
        
        while True:
            print(self.print_cli_menu(formats))
            choice = input("请输入选项: ").strip().lower()
            
            if choice == 'q':
                print("再见!")
                break
            elif choice == '0':
                export_callback(fmt_list)
                break
            elif choice.isdigit() and 1 <= int(choice) <= len(fmt_list):
                export_callback([fmt_list[int(choice) - 1]])
                break
            else:
                print("无效选项，请重新输入")
