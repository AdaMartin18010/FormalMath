"""
个性化学习路径推荐系统 - 路径可视化组件

提供多种可视化方式：
1. 时间线视图 - 展示学习进度和时间安排
2. 依赖图高亮 - 在概念依赖图中高亮推荐路径
3. 进度追踪 - 可视化学习进度和成就
4. 交互式仪表板 - 综合展示所有信息
"""

import json
import base64
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Set, Tuple, Any
from dataclasses import dataclass, field
from enum import Enum
import uuid

from user_profile import UserProfile, LearningHistory, ConceptMastery
from recommendation_engine import LearningPath, PathNode, ConceptGraph, PathStrategy


class VisualizationTheme(Enum):
    """可视化主题"""
    LIGHT = "light"
    DARK = "dark"
    COLORFUL = "colorful"
    MINIMAL = "minimal"


@dataclass
class TimelineEvent:
    """时间线事件"""
    event_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    title: str = ""
    description: str = ""
    start_time: datetime = field(default_factory=datetime.now)
    end_time: Optional[datetime] = None
    concept_id: str = ""
    event_type: str = "study"  # study/break/milestone/review
    completed: bool = False
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "event_id": self.event_id,
            "title": self.title,
            "description": self.description,
            "start_time": self.start_time.isoformat(),
            "end_time": self.end_time.isoformat() if self.end_time else None,
            "concept_id": self.concept_id,
            "event_type": self.event_type,
            "completed": self.completed
        }


@dataclass
class TimelineView:
    """时间线视图"""
    view_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    path_id: str = ""
    events: List[TimelineEvent] = field(default_factory=list)
    start_date: datetime = field(default_factory=datetime.now)
    end_date: Optional[datetime] = None
    
    def add_event(self, event: TimelineEvent):
        """添加事件"""
        self.events.append(event)
        self.events.sort(key=lambda e: e.start_time)
    
    def generate_from_path(self, path: LearningPath, user_profile: UserProfile):
        """从学习路径生成时间线"""
        self.path_id = path.path_id
        self.start_date = datetime.now()
        
        current_date = self.start_date
        daily_hours = user_profile.time_preference.daily_hours
        session_duration = user_profile.time_preference.session_duration
        
        # 获取可并行学习的组
        parallel_groups = path.get_parallel_groups()
        
        for group in parallel_groups:
            # 每天的学习时间限制
            daily_time_used = 0
            
            for node in group:
                if daily_time_used >= daily_hours * 60:
                    # 进入下一天
                    current_date = current_date + timedelta(days=1)
                    daily_time_used = 0
                
                # 创建学习事件
                event = TimelineEvent(
                    title=f"学习: {node.name}",
                    description=f"预计时长: {node.estimated_duration}分钟，难度: {node.difficulty}",
                    start_time=current_date,
                    concept_id=node.concept_id,
                    event_type="study"
                )
                
                # 计算结束时间
                duration = min(node.estimated_duration, 
                              user_profile.time_preference.session_duration)
                event.end_time = event.start_time + timedelta(minutes=duration)
                
                self.add_event(event)
                daily_time_used += duration
                
                # 添加复习事件（间隔重复）
                if node.importance > 0.7:
                    review_event = TimelineEvent(
                        title=f"复习: {node.name}",
                        description="基于间隔重复算法的复习",
                        start_time=current_date + timedelta(days=1),
                        concept_id=node.concept_id,
                        event_type="review"
                    )
                    self.add_event(review_event)
            
            # 组间休息
            current_date = current_date + timedelta(days=1)
        
        if self.events:
            self.end_date = max(e.end_time or e.start_time for e in self.events)
    
    def to_html(self, theme: VisualizationTheme = VisualizationTheme.LIGHT) -> str:
        """生成HTML时间线"""
        colors = {
            VisualizationTheme.LIGHT: {
                "bg": "#ffffff",
                "text": "#333333",
                "line": "#e0e0e0",
                "study": "#4CAF50",
                "review": "#2196F3",
                "break": "#FF9800",
                "milestone": "#9C27B0"
            },
            VisualizationTheme.DARK: {
                "bg": "#1a1a1a",
                "text": "#e0e0e0",
                "line": "#333333",
                "study": "#66BB6A",
                "review": "#42A5F5",
                "break": "#FFA726",
                "milestone": "#AB47BC"
            },
            VisualizationTheme.COLORFUL: {
                "bg": "#f5f5f5",
                "text": "#333333",
                "line": "#bdbdbd",
                "study": "#8BC34A",
                "review": "#03A9F4",
                "break": "#FF5722",
                "milestone": "#E91E63"
            }
        }.get(theme, colors[VisualizationTheme.LIGHT])
        
        html = f"""
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>学习路径时间线</title>
    <style>
        body {{
            font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
            background-color: {colors["bg"]};
            color: {colors["text"]};
            margin: 0;
            padding: 20px;
        }}
        .timeline-container {{
            max-width: 800px;
            margin: 0 auto;
        }}
        .timeline-header {{
            text-align: center;
            margin-bottom: 30px;
        }}
        .timeline {{
            position: relative;
            padding: 20px 0;
        }}
        .timeline::before {{
            content: '';
            position: absolute;
            left: 50%;
            transform: translateX(-50%);
            width: 2px;
            height: 100%;
            background-color: {colors["line"]};
        }}
        .timeline-item {{
            position: relative;
            margin-bottom: 30px;
            width: 100%;
        }}
        .timeline-item:nth-child(odd) .timeline-content {{
            margin-left: 0;
            margin-right: 55%;
            text-align: right;
        }}
        .timeline-item:nth-child(even) .timeline-content {{
            margin-left: 55%;
            margin-right: 0;
            text-align: left;
        }}
        .timeline-content {{
            background-color: {colors["bg"]};
            border: 1px solid {colors["line"]};
            border-radius: 8px;
            padding: 15px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }}
        .timeline-dot {{
            position: absolute;
            left: 50%;
            transform: translateX(-50%);
            width: 16px;
            height: 16px;
            border-radius: 50%;
            border: 3px solid {colors["bg"]};
            z-index: 1;
        }}
        .timeline-dot.study {{ background-color: {colors["study"]}; }}
        .timeline-dot.review {{ background-color: {colors["review"]}; }}
        .timeline-dot.break {{ background-color: {colors["break"]}; }}
        .timeline-dot.milestone {{ background-color: {colors["milestone"]}; }}
        .timeline-date {{
            font-size: 12px;
            color: #888;
            margin-bottom: 5px;
        }}
        .timeline-title {{
            font-weight: bold;
            font-size: 16px;
            margin-bottom: 5px;
        }}
        .timeline-desc {{
            font-size: 14px;
            color: #666;
        }}
        .timeline-progress {{
            height: 4px;
            background-color: {colors["line"]};
            border-radius: 2px;
            margin-top: 10px;
        }}
        .timeline-progress-bar {{
            height: 100%;
            border-radius: 2px;
            background-color: {colors["study"]};
        }}
    </style>
</head>
<body>
    <div class="timeline-container">
        <div class="timeline-header">
            <h1>📚 个性化学习路径时间线</h1>
            <p>预计完成时间: {self.end_date.strftime('%Y年%m月%d日') if self.end_date else '待定'}</p>
        </div>
        <div class="timeline">
"""
        
        for event in self.events:
            event_type_class = event.event_type
            progress_bar = ""
            if event.event_type == "study":
                progress = 100 if event.completed else 0
                progress_bar = f'<div class="timeline-progress"><div class="timeline-progress-bar" style="width: {progress}%"></div></div>'
            
            html += f"""
            <div class="timeline-item">
                <div class="timeline-dot {event_type_class}"></div>
                <div class="timeline-content">
                    <div class="timeline-date">{event.start_time.strftime('%m月%d日 %H:%M')}</div>
                    <div class="timeline-title">{event.title}</div>
                    <div class="timeline-desc">{event.description}</div>
                    {progress_bar}
                </div>
            </div>
"""
        
        html += """
        </div>
    </div>
</body>
</html>
"""
        return html


@dataclass
class PathGraphView:
    """路径依赖图视图"""
    view_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    path_id: str = ""
    highlighted_nodes: Set[str] = field(default_factory=set)
    highlighted_edges: Set[Tuple[str, str]] = field(default_factory=set)
    node_colors: Dict[str, str] = field(default_factory=dict)
    
    def generate_from_path(self, path: LearningPath, concept_graph: ConceptGraph):
        """从学习路径生成高亮图"""
        self.path_id = path.path_id
        self.highlighted_nodes = set(path.node_order)
        
        # 计算节点颜色（基于难度）
        for node in path.nodes:
            difficulty = node.difficulty
            if difficulty <= 1:
                self.node_colors[node.concept_id] = "#4CAF50"  # 绿色
            elif difficulty <= 2:
                self.node_colors[node.concept_id] = "#8BC34A"  # 浅绿
            elif difficulty <= 3:
                self.node_colors[node.concept_id] = "#FFC107"  # 黄色
            elif difficulty <= 4:
                self.node_colors[node.concept_id] = "#FF9800"  # 橙色
            else:
                self.node_colors[node.concept_id] = "#F44336"  # 红色
        
        # 计算高亮边
        for i in range(len(path.node_order) - 1):
            current = path.node_order[i]
            next_concepts = path.node_order[i + 1:]
            
            for next_c in next_concepts:
                if concept_graph.graph.has_edge(current, next_c):
                    self.highlighted_edges.add((current, next_c))
    
    def to_mermaid(self) -> str:
        """生成Mermaid图表代码"""
        lines = ["graph TD"]
        
        # 添加节点定义
        for node_id in self.highlighted_nodes:
            color = self.node_colors.get(node_id, "#999")
            # 简化节点名
            short_name = node_id.replace('_', ' ').title()
            lines.append(f'    {node_id}["{short_name}"]')
            lines.append(f'    style {node_id} fill:{color}')
        
        # 添加边
        for source, target in self.highlighted_edges:
            lines.append(f'    {source} --> {target}')
        
        return '\n'.join(lines)
    
    def to_cytoscape_json(self) -> Dict[str, Any]:
        """生成Cytoscape.js可用的JSON"""
        elements = []
        
        # 节点
        for node_id in self.highlighted_nodes:
            elements.append({
                "data": {
                    "id": node_id,
                    "label": node_id.replace('_', ' ').title(),
                    "color": self.node_colors.get(node_id, "#999")
                }
            })
        
        # 边
        for i, (source, target) in enumerate(self.highlighted_edges):
            elements.append({
                "data": {
                    "id": f"edge_{i}",
                    "source": source,
                    "target": target
                }
            })
        
        return {"elements": elements}


@dataclass
class ProgressTracker:
    """进度追踪器"""
    tracker_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    user_id: str = ""
    path_id: str = ""
    completed_concepts: Set[str] = field(default_factory=set)
    in_progress_concepts: Set[str] = field(default_factory=set)
    mastery_levels: Dict[str, float] = field(default_factory=dict)
    
    def update_from_user_profile(self, user_profile: UserProfile, path: LearningPath):
        """从用户画像更新进度"""
        self.user_id = user_profile.user_id
        self.path_id = path.path_id
        
        for node in path.nodes:
            mastery = user_profile.get_concept_mastery(node.concept_id)
            self.mastery_levels[node.concept_id] = mastery
            
            if mastery >= 0.7:
                self.completed_concepts.add(node.concept_id)
            elif mastery > 0:
                self.in_progress_concepts.add(node.concept_id)
    
    def calculate_progress(self) -> float:
        """计算整体进度"""
        total = len(self.mastery_levels)
        if total == 0:
            return 0.0
        return sum(self.mastery_levels.values()) / total
    
    def to_dashboard_data(self) -> Dict[str, Any]:
        """生成仪表板数据"""
        progress = self.calculate_progress()
        
        return {
            "overall_progress": round(progress * 100, 1),
            "completed_count": len(self.completed_concepts),
            "in_progress_count": len(self.in_progress_concepts),
            "total_concepts": len(self.mastery_levels),
            "mastery_levels": self.mastery_levels,
            "progress_by_category": self._categorize_progress(),
            "estimated_completion": self._estimate_completion()
        }
    
    def _categorize_progress(self) -> Dict[str, int]:
        """按类别统计进度"""
        categories = {
            "mastered": 0,
            "proficient": 0,
            "learning": 0,
            "started": 0,
            "not_started": 0
        }
        
        for mastery in self.mastery_levels.values():
            if mastery >= 0.9:
                categories["mastered"] += 1
            elif mastery >= 0.7:
                categories["proficient"] += 1
            elif mastery >= 0.4:
                categories["learning"] += 1
            elif mastery > 0:
                categories["started"] += 1
            else:
                categories["not_started"] += 1
        
        return categories
    
    def _estimate_completion(self) -> Optional[str]:
        """估算完成日期"""
        remaining = 1 - self.calculate_progress()
        if remaining <= 0:
            return "已完成"
        
        # 简化的估算：假设每天进度增加2%
        days_needed = int(remaining / 0.02)
        completion_date = datetime.now() + timedelta(days=days_needed)
        return completion_date.strftime("%Y年%m月%d日")


class DashboardRenderer:
    """仪表板渲染器"""
    
    def __init__(self, theme: VisualizationTheme = VisualizationTheme.LIGHT):
        self.theme = theme
    
    def render_full_dashboard(self, user_profile: UserProfile, 
                              path: LearningPath,
                              concept_graph: ConceptGraph) -> str:
        """渲染完整仪表板"""
        # 生成时间线
        timeline = TimelineView()
        timeline.generate_from_path(path, user_profile)
        
        # 生成路径图
        path_graph = PathGraphView()
        path_graph.generate_from_path(path, concept_graph)
        
        # 生成进度追踪
        progress = ProgressTracker()
        progress.update_from_user_profile(user_profile, path)
        progress_data = progress.to_dashboard_data()
        
        # 生成仪表板HTML
        return self._generate_dashboard_html(
            user_profile, path, timeline, path_graph, progress_data
        )
    
    def _generate_dashboard_html(self, user_profile: UserProfile,
                                  path: LearningPath,
                                  timeline: TimelineView,
                                  path_graph: PathGraphView,
                                  progress_data: Dict[str, Any]) -> str:
        """生成仪表板HTML"""
        
        # 进度圆环SVG
        progress_percent = progress_data["overall_progress"]
        circumference = 2 * 3.14159 * 50
        offset = circumference - (progress_percent / 100) * circumference
        
        html = f"""
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>学习路径仪表板 - {user_profile.name}</title>
    <style>
        :root {{
            --primary: #4CAF50;
            --secondary: #2196F3;
            --accent: #FF9800;
            --success: #8BC34A;
            --warning: #FFC107;
            --danger: #F44336;
            --bg-primary: #ffffff;
            --bg-secondary: #f5f5f5;
            --text-primary: #333333;
            --text-secondary: #666666;
            --border: #e0e0e0;
        }}
        
        * {{
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }}
        
        body {{
            font-family: 'Segoe UI', -apple-system, BlinkMacSystemFont, sans-serif;
            background-color: var(--bg-secondary);
            color: var(--text-primary);
            line-height: 1.6;
        }}
        
        .dashboard {{
            max-width: 1400px;
            margin: 0 auto;
            padding: 20px;
        }}
        
        .dashboard-header {{
            background: linear-gradient(135deg, var(--primary), var(--secondary));
            color: white;
            padding: 30px;
            border-radius: 16px;
            margin-bottom: 24px;
            box-shadow: 0 4px 6px rgba(0,0,0,0.1);
        }}
        
        .dashboard-header h1 {{
            font-size: 28px;
            margin-bottom: 8px;
        }}
        
        .dashboard-header p {{
            opacity: 0.9;
        }}
        
        .dashboard-grid {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(300px, 1fr));
            gap: 20px;
            margin-bottom: 24px;
        }}
        
        .card {{
            background: var(--bg-primary);
            border-radius: 12px;
            padding: 24px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.05);
            border: 1px solid var(--border);
        }}
        
        .card-title {{
            font-size: 14px;
            color: var(--text-secondary);
            text-transform: uppercase;
            letter-spacing: 0.5px;
            margin-bottom: 12px;
        }}
        
        .card-value {{
            font-size: 36px;
            font-weight: bold;
            color: var(--text-primary);
        }}
        
        .card-subtitle {{
            font-size: 14px;
            color: var(--text-secondary);
            margin-top: 4px;
        }}
        
        .progress-ring {{
            display: flex;
            align-items: center;
            justify-content: center;
            margin: 20px 0;
        }}
        
        .progress-ring svg {{
            transform: rotate(-90deg);
        }}
        
        .progress-ring-bg {{
            fill: none;
            stroke: var(--border);
            stroke-width: 8;
        }}
        
        .progress-ring-fill {{
            fill: none;
            stroke: var(--primary);
            stroke-width: 8;
            stroke-linecap: round;
            transition: stroke-dashoffset 0.5s ease;
        }}
        
        .progress-text {{
            position: absolute;
            font-size: 24px;
            font-weight: bold;
            color: var(--text-primary);
        }}
        
        .stats-grid {{
            display: grid;
            grid-template-columns: repeat(2, 1fr);
            gap: 16px;
            margin-top: 20px;
        }}
        
        .stat-item {{
            text-align: center;
            padding: 16px;
            background: var(--bg-secondary);
            border-radius: 8px;
        }}
        
        .stat-value {{
            font-size: 24px;
            font-weight: bold;
            color: var(--primary);
        }}
        
        .stat-label {{
            font-size: 12px;
            color: var(--text-secondary);
            margin-top: 4px;
        }}
        
        .path-overview {{
            margin-top: 24px;
        }}
        
        .path-node {{
            display: flex;
            align-items: center;
            padding: 12px;
            margin-bottom: 8px;
            background: var(--bg-secondary);
            border-radius: 8px;
            border-left: 4px solid var(--primary);
        }}
        
        .path-node.completed {{
            border-left-color: var(--success);
        }}
        
        .path-node.in-progress {{
            border-left-color: var(--warning);
        }}
        
        .node-number {{
            width: 32px;
            height: 32px;
            background: var(--primary);
            color: white;
            border-radius: 50%;
            display: flex;
            align-items: center;
            justify-content: center;
            font-weight: bold;
            margin-right: 12px;
        }}
        
        .node-info {{
            flex: 1;
        }}
        
        .node-title {{
            font-weight: 600;
            margin-bottom: 2px;
        }}
        
        .node-meta {{
            font-size: 12px;
            color: var(--text-secondary);
        }}
        
        .difficulty-badge {{
            padding: 4px 8px;
            border-radius: 4px;
            font-size: 11px;
            font-weight: 600;
        }}
        
        .difficulty-1 {{ background: #C8E6C9; color: #2E7D32; }}
        .difficulty-2 {{ background: #DCEDC8; color: #558B2F; }}
        .difficulty-3 {{ background: #FFF9C4; color: #F57F17; }}
        .difficulty-4 {{ background: #FFE0B2; color: #E65100; }}
        .difficulty-5 {{ background: #FFCDD2; color: #C62828; }}
        
        .timeline-preview {{
            max-height: 300px;
            overflow-y: auto;
        }}
        
        .timeline-item {{
            display: flex;
            align-items: flex-start;
            padding: 12px 0;
            border-bottom: 1px solid var(--border);
        }}
        
        .timeline-dot {{
            width: 12px;
            height: 12px;
            border-radius: 50%;
            margin-right: 12px;
            margin-top: 4px;
            flex-shrink: 0;
        }}
        
        .timeline-content {{
            flex: 1;
        }}
        
        .timeline-title {{
            font-weight: 600;
            margin-bottom: 2px;
        }}
        
        .timeline-time {{
            font-size: 12px;
            color: var(--text-secondary);
        }}
    </style>
</head>
<body>
    <div class="dashboard">
        <div class="dashboard-header">
            <h1>📚 个性化学习路径仪表板</h1>
            <p>欢迎回来，{user_profile.name}！继续你的数学之旅</p>
        </div>
        
        <div class="dashboard-grid">
            <div class="card">
                <div class="card-title">整体进度</div>
                <div class="progress-ring">
                    <svg width="120" height="120">
                        <circle class="progress-ring-bg" cx="60" cy="60" r="50"/>
                        <circle class="progress-ring-fill" cx="60" cy="60" r="50"
                                stroke-dasharray="{circumference}"
                                stroke-dashoffset="{offset}"/>
                    </svg>
                    <div class="progress-text">{progress_percent:.0f}%</div>
                </div>
                <div class="card-subtitle" style="text-align: center;">
                    预计完成: {progress_data.get('estimated_completion', '计算中...')}
                </div>
            </div>
            
            <div class="card">
                <div class="card-title">学习统计</div>
                <div class="stats-grid">
                    <div class="stat-item">
                        <div class="stat-value">{progress_data['completed_count']}</div>
                        <div class="stat-label">已完成</div>
                    </div>
                    <div class="stat-item">
                        <div class="stat-value">{progress_data['in_progress_count']}</div>
                        <div class="stat-label">进行中</div>
                    </div>
                    <div class="stat-item">
                        <div class="stat-value">{path.total_estimated_hours:.0f}</div>
                        <div class="stat-label">总小时数</div>
                    </div>
                    <div class="stat-item">
                        <div class="stat-value">{len(path.nodes)}</div>
                        <div class="stat-label">概念总数</div>
                    </div>
                </div>
            </div>
            
            <div class="card">
                <div class="card-title">即将到来的学习</div>
                <div class="timeline-preview">
"""
        
        # 添加即将到来的学习事件
        upcoming_events = [e for e in timeline.events if e.start_time > datetime.now()][:5]
        for event in upcoming_events:
            event_type_color = {
                "study": "var(--primary)",
                "review": "var(--secondary)",
                "break": "var(--accent)"
            }.get(event.event_type, "var(--border)")
            
            html += f"""
                    <div class="timeline-item">
                        <div class="timeline-dot" style="background: {event_type_color};"></div>
                        <div class="timeline-content">
                            <div class="timeline-title">{event.title}</div>
                            <div class="timeline-time">{event.start_time.strftime('%m月%d日 %H:%M')}</div>
                        </div>
                    </div>
"""
        
        html += f"""
                </div>
            </div>
        </div>
        
        <div class="card">
            <div class="card-title">学习路径概览 - {path.name}</div>
            <div class="path-overview">
"""
        
        # 添加路径节点
        for i, node in enumerate(path.nodes[:10]):  # 只显示前10个
            status_class = ""
            if node.concept_id in progress.mastery_levels:
                mastery = progress.mastery_levels[node.concept_id]
                if mastery >= 0.7:
                    status_class = "completed"
                elif mastery > 0:
                    status_class = "in-progress"
            
            html += f"""
                <div class="path-node {status_class}">
                    <div class="node-number">{i+1}</div>
                    <div class="node-info">
                        <div class="node-title">{node.name}</div>
                        <div class="node-meta">预计 {node.estimated_duration} 分钟</div>
                    </div>
                    <span class="difficulty-badge difficulty-{node.difficulty}">难度 {node.difficulty}</span>
                </div>
"""
        
        if len(path.nodes) > 10:
            html += f"<div style='text-align: center; padding: 16px; color: var(--text-secondary);'>还有 {len(path.nodes) - 10} 个概念...</div>"
        
        html += """
            </div>
        </div>
    </div>
</body>
</html>
"""
        return html


def export_path_to_json(path: LearningPath, 
                        user_profile: UserProfile) -> Dict[str, Any]:
    """导出路径为JSON格式"""
    return {
        "path": path.to_dict(),
        "user": {
            "user_id": user_profile.user_id,
            "name": user_profile.name,
            "learning_style": user_profile.learning_preference.get_dominant_style().value,
            "daily_hours": user_profile.time_preference.daily_hours
        },
        "export_time": datetime.now().isoformat()
    }


if __name__ == "__main__":
    # 测试代码
    print("=== 可视化组件测试 ===\n")
    
    # 导入测试数据
    from recommendation_engine import create_sample_graph, RecommendationEngine, PathStrategy
    from user_profile import LearningStyle
    
    # 创建概念图
    graph = create_sample_graph()
    
    # 创建用户画像
    user = UserProfile(name="测试用户", email="test@example.com")
    user.learning_preference.style_weights = {
        LearningStyle.VISUAL: 0.4,
        LearningStyle.TEXTUAL: 0.3,
        LearningStyle.INTERACTIVE: 0.2,
        LearningStyle.MULTIMODAL: 0.1
    }
    user.time_preference.daily_hours = 2.0
    user.time_preference.weekly_days = 5
    
    # 设置已掌握的概念
    user.update_mastery("set_theory", 0.85)
    user.update_mastery("functions", 0.75)
    
    # 创建推荐引擎并生成路径
    engine = RecommendationEngine(graph)
    paths = engine.recommend(user, strategy=PathStrategy.BALANCED,
                             target_concepts=["algebraic_topology"],
                             num_alternatives=0)
    
    path = paths[0]
    print(f"生成路径: {path.name}")
    print(f"  - 概念数: {len(path.nodes)}")
    print(f"  - 总时间: {path.total_estimated_hours:.1f}小时")
    
    # 测试时间线视图
    print("\n--- 时间线视图 ---")
    timeline = TimelineView()
    timeline.generate_from_path(path, user)
    print(f"时间线事件数: {len(timeline.events)}")
    print(f"预计完成日期: {timeline.end_date}")
    
    # 测试路径图视图
    print("\n--- 路径图视图 ---")
    path_graph = PathGraphView()
    path_graph.generate_from_path(path, graph)
    print(f"高亮节点数: {len(path_graph.highlighted_nodes)}")
    print(f"高亮边数: {len(path_graph.highlighted_edges)}")
    
    # 生成Mermaid代码预览
    mermaid_code = path_graph.to_mermaid()
    print(f"\nMermaid代码预览（前500字符）:")
    print(mermaid_code[:500])
    
    # 测试进度追踪
    print("\n--- 进度追踪 ---")
    progress = ProgressTracker()
    progress.update_from_user_profile(user, path)
    progress_data = progress.to_dashboard_data()
    print(f"整体进度: {progress_data['overall_progress']:.1f}%")
    print(f"已完成: {progress_data['completed_count']}")
    print(f"进行中: {progress_data['in_progress_count']}")
    
    # 测试仪表板渲染
    print("\n--- 仪表板渲染 ---")
    renderer = DashboardRenderer()
    dashboard_html = renderer.render_full_dashboard(user, path, graph)
    print(f"仪表板HTML大小: {len(dashboard_html)} 字符")
    
    # 保存示例HTML文件
    with open("sample_dashboard.html", "w", encoding="utf-8") as f:
        f.write(dashboard_html)
    print("仪表板已保存到: sample_dashboard.html")
    
    print("\n=== 测试完成 ===")
