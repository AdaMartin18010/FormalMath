#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
图片导出器
支持PNG、SVG格式导出
"""

import math
import random
from pathlib import Path
from typing import List, Dict, Any, Optional, Tuple
from datetime import datetime
from collections import defaultdict

# 可选依赖
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


class ImageExporter:
    """
    图片格式导出器
    
    支持导出：
    - SVG: 矢量图格式，可无损缩放
    - PNG: 位图格式，适合演示文稿
    
    使用力导向布局算法自动计算节点位置
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
    
    # 边框颜色
    CATEGORY_BORDERS = {
        "分析学": "#1565C0",
        "代数学": "#7B1FA2",
        "几何拓扑": "#2E7D32",
        "数论逻辑": "#D84315",
        "概率统计": "#F9A825",
        "最优化": "#00695C",
        "控制论": "#0277BD",
        "信息论": "#6A1B9A",
        "密码学": "#455A64",
        "基础数学": "#616161",
        "未分类": "#757575"
    }
    
    def __init__(self, output_dir: Path):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
        self.nodes: List[Dict[str, Any]] = []
        self.edges: List[Dict[str, Any]] = []
        self.metadata: Dict[str, Any] = {}
        
        # 节点位置缓存
        self.node_positions: Dict[str, Tuple[float, float]] = {}
    
    def set_data(self, nodes: List[Dict], edges: List[Dict], metadata: Dict[str, Any] = None):
        """设置导出数据"""
        self.nodes = nodes
        self.edges = edges
        self.metadata = metadata or {}
        self.node_positions = {}
    
    def export_svg(self, output_path: Optional[Path] = None,
                  width: int = 1200, height: int = 800,
                  layout: str = "force") -> Path:
        """
        导出为SVG格式
        
        Args:
            output_path: 输出文件路径
            width: 画布宽度
            height: 画布高度
            layout: 布局算法 ('force' 或 'circular')
            
        Returns:
            输出文件路径
        """
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph.svg"
        
        # 计算布局
        if layout == "force":
            self._calculate_force_layout(width, height)
        else:
            self._calculate_circular_layout(width, height)
        
        # 构建SVG
        svg_parts = []
        
        # SVG头部
        svg_parts.append(f'''<?xml version="1.0" encoding="UTF-8"?>
<svg width="{width}" height="{height}" xmlns="http://www.w3.org/2000/svg" 
     viewBox="0 0 {width} {height}" style="background-color: #fafafa;">
    <defs>
        <!-- 箭头标记 -->
        <marker id="arrowhead" markerWidth="10" markerHeight="7" 
                refX="9" refY="3.5" orient="auto">
            <polygon points="0 0, 10 3.5, 0 7" fill="#666"/>
        </marker>
        <!-- 阴影滤镜 -->
        <filter id="shadow" x="-20%" y="-20%" width="140%" height="140%">
            <feDropShadow dx="1" dy="2" stdDeviation="2" flood-opacity="0.2"/>
        </filter>
        <!-- 渐变定义 -->
        <linearGradient id="headerGrad" x1="0%" y1="0%" x2="100%" y2="0%">
            <stop offset="0%" style="stop-color:#1a73e8;stop-opacity:1" />
            <stop offset="100%" style="stop-color:#34a853;stop-opacity:1" />
        </linearGradient>
    </defs>
    
    <!-- 背景 -->
    <rect width="100%" height="100%" fill="#fafafa"/>
    
    <!-- 标题区域 -->
    <rect x="0" y="0" width="100%" height="80" fill="url(#headerGrad)"/>
    <text x="{width/2}" y="45" text-anchor="middle" 
          font-family="Arial, sans-serif" font-size="24" font-weight="bold" fill="white">
        FormalMath 知识图谱
    </text>
    <text x="{width/2}" y="68" text-anchor="middle" 
          font-family="Arial, sans-serif" font-size="12" fill="rgba(255,255,255,0.9)">
        {len(self.nodes)} 概念 | {len(self.edges)} 关系 | 生成于 {datetime.now().strftime('%Y-%m-%d')}
    </text>
''')
        
        # 绘制边
        for edge in self.edges:
            source_id = edge.get('source', edge.get('from', ''))
            target_id = edge.get('target', edge.get('to', ''))
            
            if source_id in self.node_positions and target_id in self.node_positions:
                sx, sy = self.node_positions[source_id]
                tx, ty = self.node_positions[target_id]
                
                svg_parts.append(f'''    <line x1="{sx}" y1="{sy}" x2="{tx}" y2="{ty}" 
            stroke="#bbb" stroke-width="1.5" marker-end="url(#arrowhead)" opacity="0.6"/>
''')
        
        # 绘制节点
        for node in self.nodes:
            node_id = node.get('id', '')
            if node_id not in self.node_positions:
                continue
            
            x, y = self.node_positions[node_id]
            category = node.get('category', '未分类')
            color = self.CATEGORY_COLORS.get(category, "#CCCCCC")
            border_color = self.CATEGORY_BORDERS.get(category, "#757575")
            difficulty = node.get('difficulty', 1)
            r = 12 + difficulty * 2
            
            name = node.get('name', node.get('label', ''))
            
            # 节点圆形
            svg_parts.append(f'''    <circle cx="{x}" cy="{y}" r="{r}" 
            fill="{color}" stroke="{border_color}" stroke-width="2" filter="url(#shadow)"/>
    <text x="{x}" y="{y + r + 18}" text-anchor="middle" 
          font-family="Arial, sans-serif" font-size="10" fill="#333" font-weight="500">{name}</text>
''')
        
        # 绘制图例
        legend_x = width - 200
        legend_y = 120
        legend_height = len(self.CATEGORY_COLORS) * 28 + 60
        
        svg_parts.append(f'''    <!-- 图例 -->
    <rect x="{legend_x - 15}" y="{legend_y - 35}" width="190" height="{legend_height}" 
          fill="white" stroke="#e0e0e0" stroke-width="1" rx="8" filter="url(#shadow)"/>
    <text x="{legend_x}" y="{legend_y - 12}" font-family="Arial, sans-serif" 
          font-size="13" font-weight="bold" fill="#333">📂 类别图例</text>
''')
        
        for i, (category, color) in enumerate(self.CATEGORY_COLORS.items()):
            if category == "未分类":
                continue
            y = legend_y + i * 28
            border = self.CATEGORY_BORDERS.get(category, "#757575")
            svg_parts.append(f'''    <circle cx="{legend_x + 12}" cy="{y}" r="10" 
          fill="{color}" stroke="{border}" stroke-width="1.5"/>
    <text x="{legend_x + 32}" y="{y + 4}" font-family="Arial, sans-serif" 
          font-size="11" fill="#333">{category}</text>
''')
        
        # 统计信息
        stats_x = 30
        stats_y = height - 100
        
        by_category = defaultdict(int)
        for node in self.nodes:
            by_category[node.get('category', '未分类')] += 1
        
        top_categories = sorted(by_category.items(), key=lambda x: -x[1])[:5]
        
        svg_parts.append(f'''    <!-- 统计信息 -->
    <rect x="{stats_x - 15}" y="{stats_y - 25}" width="200" height="90" 
          fill="white" stroke="#e0e0e0" stroke-width="1" rx="8" filter="url(#shadow)"/>
    <text x="{stats_x}" y="{stats_y - 5}" font-family="Arial, sans-serif" 
          font-size="12" font-weight="bold" fill="#333">📊 统计概览</text>
    <text x="{stats_x}" y="{stats_y + 15}" font-family="Arial, sans-serif" 
          font-size="10" fill="#666">概念: {len(self.nodes)} | 关系: {len(self.edges)}</text>
''')
        
        svg_parts.append('</svg>')
        
        # 写入文件
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(''.join(svg_parts))
        
        return output_path
    
    def export_png(self, output_path: Optional[Path] = None,
                  width: int = 1200, height: int = 800) -> Path:
        """
        导出为PNG格式
        
        Args:
            output_path: 输出文件路径
            width: 图片宽度
            height: 图片高度
            
        Returns:
            输出文件路径
        """
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph.png"
        
        if CAIROSVG_AVAILABLE:
            # 使用cairosvg将SVG转换为PNG（更高质量）
            svg_path = self.output_dir / ".temp_export.svg"
            self.export_svg(svg_path, width, height)
            cairosvg.svg2png(url=str(svg_path), write_to=str(output_path),
                           output_width=width, output_height=height)
            svg_path.unlink(missing_ok=True)
            return output_path
            
        elif PIL_AVAILABLE:
            return self._export_png_with_pil(output_path, width, height)
        else:
            raise ImportError("PNG导出需要cairosvg或Pillow。请安装: pip install cairosvg pillow")
    
    def _export_png_with_pil(self, output_path: Path, width: int, height: int) -> Path:
        """使用PIL导出PNG"""
        # 创建图像
        img = PILImage.new('RGB', (width, height), color='#fafafa')
        draw = ImageDraw.Draw(img)
        
        # 计算布局
        self._calculate_force_layout(width, height)
        
        # 绘制标题背景
        draw.rectangle([0, 0, width, 80], fill='#1a73e8')
        
        # 绘制标题
        draw.text((width//2, 40), "FormalMath 知识图谱", 
                 fill='white', anchor='mm')
        draw.text((width//2, 65), 
                 f"{len(self.nodes)} 概念 | {len(self.edges)} 关系",
                 fill='#cccccc', anchor='mm')
        
        # 绘制边
        for edge in self.edges:
            source_id = edge.get('source', edge.get('from', ''))
            target_id = edge.get('target', edge.get('to', ''))
            
            if source_id in self.node_positions and target_id in self.node_positions:
                sx, sy = self.node_positions[source_id]
                tx, ty = self.node_positions[target_id]
                draw.line([(sx, sy), (tx, ty)], fill='#bbbbbb', width=1)
        
        # 绘制节点
        for node in self.nodes:
            node_id = node.get('id', '')
            if node_id not in self.node_positions:
                continue
            
            x, y = self.node_positions[node_id]
            category = node.get('category', '未分类')
            color = self.CATEGORY_COLORS.get(category, "#CCCCCC")
            difficulty = node.get('difficulty', 1)
            r = 12 + difficulty * 2
            
            rgb = self._hex_to_rgb(color)
            draw.ellipse([x - r, y - r, x + r, y + r],
                        fill=rgb, outline='#333333', width=2)
            
            name = node.get('name', node.get('label', ''))
            draw.text((x, y + r + 12), name, fill='#333333', anchor='mm')
        
        # 保存
        img.save(output_path, 'PNG')
        return output_path
    
    def _calculate_force_layout(self, width: int, height: int, iterations: int = 100):
        """
        力导向布局算法
        
        模拟物理力使节点达到稳定布局
        """
        margin = 100
        
        # 初始化随机位置
        for node in self.nodes:
            node_id = node.get('id', '')
            if node_id not in self.node_positions:
                self.node_positions[node_id] = (
                    random.uniform(margin, width - margin),
                    random.uniform(margin + 80, height - margin)
                )
        
        k = 80  # 理想边长
        
        for _ in range(iterations):
            forces = {node_id: [0.0, 0.0] for node_id in self.node_positions}
            
            # 斥力（节点之间）
            node_ids = list(self.node_positions.keys())
            for i, id1 in enumerate(node_ids):
                x1, y1 = self.node_positions[id1]
                for id2 in node_ids[i+1:]:
                    x2, y2 = self.node_positions[id2]
                    dx = x2 - x1
                    dy = y2 - y1
                    dist = math.sqrt(dx*dx + dy*dy)
                    if dist > 0 and dist < 250:
                        force = k * k / dist
                        fx = force * dx / dist
                        fy = force * dy / dist
                        forces[id1][0] -= fx
                        forces[id1][1] -= fy
                        forces[id2][0] += fx
                        forces[id2][1] += fy
            
            # 引力（边连接）
            for edge in self.edges:
                source_id = edge.get('source', edge.get('from', ''))
                target_id = edge.get('target', edge.get('to', ''))
                
                if source_id in self.node_positions and target_id in self.node_positions:
                    sx, sy = self.node_positions[source_id]
                    tx, ty = self.node_positions[target_id]
                    dx = tx - sx
                    dy = ty - sy
                    dist = math.sqrt(dx*dx + dy*dy)
                    if dist > 0:
                        force = dist * dist / k * 0.05
                        fx = force * dx / dist
                        fy = force * dy / dist
                        forces[source_id][0] += fx
                        forces[source_id][1] += fy
                        forces[target_id][0] -= fx
                        forces[target_id][1] -= fy
            
            # 应用力
            for node_id, (fx, fy) in forces.items():
                x, y = self.node_positions[node_id]
                x = max(margin, min(width - margin, x + fx * 0.1))
                y = max(margin + 80, min(height - margin, y + fy * 0.1))
                self.node_positions[node_id] = (x, y)
    
    def _calculate_circular_layout(self, width: int, height: int):
        """圆形布局算法"""
        margin = 150
        cx = width / 2
        cy = height / 2
        radius = min(width, height) / 2 - margin
        
        # 按类别分组
        by_category = defaultdict(list)
        for node in self.nodes:
            by_category[node.get('category', '未分类')].append(node)
        
        # 为每个类别分配一个扇区
        categories = list(by_category.keys())
        angle_per_category = 2 * math.pi / len(categories) if categories else 0
        
        for i, category in enumerate(categories):
            nodes_in_cat = by_category[category]
            start_angle = i * angle_per_category
            angle_per_node = angle_per_category / len(nodes_in_cat) if nodes_in_cat else 0
            
            for j, node in enumerate(nodes_in_cat):
                angle = start_angle + j * angle_per_node + angle_per_node / 2
                node_id = node.get('id', '')
                self.node_positions[node_id] = (
                    cx + radius * math.cos(angle),
                    cy + radius * math.sin(angle)
                )
    
    def _hex_to_rgb(self, hex_color: str) -> Tuple[int, int, int]:
        """将十六进制颜色转换为RGB元组"""
        hex_color = hex_color.lstrip('#')
        return tuple(int(hex_color[i:i+2], 16) for i in (0, 2, 4))
    
    def export_thumbnail(self, output_path: Optional[Path] = None,
                        size: int = 300) -> Path:
        """
        导出缩略图
        
        Args:
            output_path: 输出文件路径
            size: 缩略图尺寸
            
        Returns:
            输出文件路径
        """
        if output_path is None:
            output_path = self.output_dir / "knowledge_graph_thumbnail.png"
        
        return self.export_png(output_path, width=size, height=size)
