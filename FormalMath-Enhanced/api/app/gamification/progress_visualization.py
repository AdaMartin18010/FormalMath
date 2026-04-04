"""
进度可视化系统
里程碑管理、进度追踪、可视化数据生成
"""
import numpy as np
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from enum import Enum
from collections import defaultdict
import json


class MilestoneType(str, Enum):
    """里程碑类型"""
    KNOWLEDGE = "knowledge"          # 知识里程碑
    CONSISTENCY = "consistency"      # 坚持里程碑
    ACHIEVEMENT = "achievement"      # 成就里程碑
    SOCIAL = "social"                # 社交里程碑
    CHALLENGE = "challenge"          # 挑战里程碑


@dataclass
class Milestone:
    """里程碑"""
    milestone_id: str
    name: str
    description: str
    milestone_type: MilestoneType
    
    # 目标
    target_value: float
    current_value: float = 0
    
    # 视觉
    icon: Optional[str] = None
    color: str = '#4CAF50'
    
    # 状态
    is_reached: bool = False
    reached_at: Optional[datetime] = None
    
    # 关联
    parent_id: Optional[str] = None
    children: List[str] = field(default_factory=list)
    
    def get_progress(self) -> float:
        """获取进度"""
        if self.target_value == 0:
            return 1.0 if self.is_reached else 0.0
        return min(1.0, self.current_value / self.target_value)


@dataclass
class ProgressSnapshot:
    """进度快照"""
    timestamp: datetime
    metrics: Dict[str, float]
    milestones_reached: List[str]
    

@dataclass
class LearningPathProgress:
    """学习路径进度"""
    path_id: str
    user_id: str
    
    total_nodes: int
    completed_nodes: int
    current_node_index: int
    
    start_time: Optional[datetime] = None
    estimated_completion: Optional[datetime] = None
    
    node_progress: Dict[str, Dict] = field(default_factory=dict)
    
    def get_overall_progress(self) -> float:
        """获取整体进度"""
        if self.total_nodes == 0:
            return 0.0
        return self.completed_nodes / self.total_nodes
    
    def get_estimated_remaining_time(self) -> Optional[int]:
        """估计剩余时间（分钟）"""
        if self.completed_nodes == 0 or not self.start_time:
            return None
        
        elapsed = (datetime.utcnow() - self.start_time).total_seconds() / 60
        rate = self.completed_nodes / elapsed if elapsed > 0 else 0
        
        if rate > 0:
            remaining_nodes = self.total_nodes - self.completed_nodes
            return int(remaining_nodes / rate)
        
        return None


class MilestoneManager:
    """
    里程碑管理器
    
    管理学习里程碑的创建、更新和追踪
    """
    
    def __init__(self):
        self.milestones: Dict[str, Milestone] = {}
        self.user_milestones: Dict[str, Dict[str, Milestone]] = defaultdict(dict)
        self.milestone_relationships: Dict[str, List[str]] = defaultdict(list)
        
        # 初始化默认里程碑
        self._init_default_milestones()
    
    def _init_default_milestones(self):
        """初始化默认里程碑"""
        default_milestones = [
            # 知识里程碑
            Milestone(
                milestone_id='first_concept',
                name='初次探索',
                description='掌握第一个概念',
                milestone_type=MilestoneType.KNOWLEDGE,
                target_value=1,
                color='#81C784'
            ),
            Milestone(
                milestone_id='concept_explorer',
                name='概念探索者',
                description='掌握10个概念',
                milestone_type=MilestoneType.KNOWLEDGE,
                target_value=10,
                color='#66BB6A',
                parent_id='first_concept'
            ),
            Milestone(
                milestone_id='concept_master',
                name='概念大师',
                description='掌握50个概念',
                milestone_type=MilestoneType.KNOWLEDGE,
                target_value=50,
                color='#4CAF50',
                parent_id='concept_explorer'
            ),
            Milestone(
                milestone_id='knowledge_sage',
                name='知识贤者',
                description='掌握100个概念',
                milestone_type=MilestoneType.KNOWLEDGE,
                target_value=100,
                color='#388E3C',
                parent_id='concept_master'
            ),
            
            # 坚持里程碑
            Milestone(
                milestone_id='first_week',
                name='首周坚持',
                description='连续学习7天',
                milestone_type=MilestoneType.CONSISTENCY,
                target_value=7,
                color='#64B5F6'
            ),
            Milestone(
                milestone_id='first_month',
                name='月度成就',
                description='连续学习30天',
                milestone_type=MilestoneType.CONSISTENCY,
                target_value=30,
                color='#42A5F5',
                parent_id='first_week'
            ),
            Milestone(
                milestone_id='quarter_master',
                name='季度达人',
                description='连续学习90天',
                milestone_type=MilestoneType.CONSISTENCY,
                target_value=90,
                color='#2196F3',
                parent_id='first_month'
            ),
            
            # 时间投入里程碑
            Milestone(
                milestone_id='hour_10',
                name='初学者',
                description='累计学习10小时',
                milestone_type=MilestoneType.CONSISTENCY,
                target_value=10,
                color='#FFB74D'
            ),
            Milestone(
                milestone_id='hour_100',
                name='专注者',
                description='累计学习100小时',
                milestone_type=MilestoneType.CONSISTENCY,
                target_value=100,
                color='#FFA726',
                parent_id='hour_10'
            ),
            Milestone(
                milestone_id='hour_500',
                name='学者',
                description='累计学习500小时',
                milestone_type=MilestoneType.CONSISTENCY,
                target_value=500,
                color='#FF9800',
                parent_id='hour_100'
            ),
        ]
        
        for milestone in default_milestones:
            self.add_milestone(milestone)
    
    def add_milestone(self, milestone: Milestone):
        """添加里程碑"""
        self.milestones[milestone.milestone_id] = milestone
        
        # 建立关系
        if milestone.parent_id:
            self.milestone_relationships[milestone.parent_id].append(
                milestone.milestone_id
            )
    
    def update_user_progress(
        self,
        user_id: str,
        milestone_id: str,
        value: float,
        is_increment: bool = True
    ) -> List[Milestone]:
        """
        更新用户里程碑进度
        
        Returns:
            新达成的里程碑列表
        """
        if milestone_id not in self.milestones:
            return []
        
        # 获取或创建用户里程碑
        if milestone_id not in self.user_milestones[user_id]:
            template = self.milestones[milestone_id]
            self.user_milestones[user_id][milestone_id] = Milestone(
                milestone_id=template.milestone_id,
                name=template.name,
                description=template.description,
                milestone_type=template.milestone_type,
                target_value=template.target_value,
                icon=template.icon,
                color=template.color,
                parent_id=template.parent_id,
                children=template.children.copy()
            )
        
        user_milestone = self.user_milestones[user_id][milestone_id]
        
        # 更新进度
        if is_increment:
            user_milestone.current_value += value
        else:
            user_milestone.current_value = value
        
        # 检查是否达成
        newly_reached = []
        
        if not user_milestone.is_reached and user_milestone.current_value >= user_milestone.target_value:
            user_milestone.is_reached = True
            user_milestone.reached_at = datetime.utcnow()
            newly_reached.append(user_milestone)
        
        return newly_reached
    
    def get_user_milestones(
        self,
        user_id: str,
        milestone_type: Optional[MilestoneType] = None
    ) -> Dict[str, Any]:
        """获取用户里程碑"""
        user_milestone_dict = self.user_milestones[user_id]
        
        milestones_list = []
        for milestone_id, milestone in user_milestone_dict.items():
            if milestone_type and milestone.milestone_type != milestone_type:
                continue
            
            milestones_list.append({
                'milestone_id': milestone_id,
                'name': milestone.name,
                'description': milestone.description,
                'type': milestone.milestone_type.value,
                'progress': milestone.get_progress(),
                'current': milestone.current_value,
                'target': milestone.target_value,
                'is_reached': milestone.is_reached,
                'reached_at': milestone.reached_at.isoformat() if milestone.reached_at else None,
                'color': milestone.color
            })
        
        # 按进度排序
        milestones_list.sort(key=lambda x: x['progress'], reverse=True)
        
        # 统计
        reached_count = sum(1 for m in milestones_list if m['is_reached'])
        
        return {
            'user_id': user_id,
            'total_milestones': len(milestones_list),
            'reached_count': reached_count,
            'in_progress_count': len(milestones_list) - reached_count,
            'milestones': milestones_list
        }
    
    def get_milestone_tree(self, user_id: str) -> Dict[str, Any]:
        """获取里程碑树（层次结构）"""
        # 找出根里程碑（无父节点）
        roots = [
            m for m in self.milestones.values()
            if m.parent_id is None
        ]
        
        def build_tree(milestone: Milestone) -> Dict:
            user_milestone = self.user_milestones[user_id].get(
                milestone.milestone_id,
                milestone
            )
            
            node = {
                'milestone_id': milestone.milestone_id,
                'name': milestone.name,
                'progress': user_milestone.get_progress(),
                'is_reached': user_milestone.is_reached,
                'color': milestone.color,
                'children': []
            }
            
            # 递归添加子节点
            for child_id in self.milestone_relationships.get(milestone.milestone_id, []):
                if child_id in self.milestones:
                    node['children'].append(build_tree(self.milestones[child_id]))
            
            return node
        
        return {
            'trees': [build_tree(root) for root in roots]
        }


class ProgressTracker:
    """
    进度追踪器
    
    追踪和可视化学习进度
    """
    
    def __init__(self):
        self.path_progress: Dict[str, LearningPathProgress] = {}
        self.progress_history: Dict[str, List[ProgressSnapshot]] = defaultdict(list)
        self.daily_stats: Dict[str, Dict[str, Any]] = defaultdict(lambda: defaultdict(int))
    
    def start_path(
        self,
        path_id: str,
        user_id: str,
        total_nodes: int,
        estimated_minutes_per_node: int = 30
    ) -> LearningPathProgress:
        """开始学习路径"""
        progress = LearningPathProgress(
            path_id=path_id,
            user_id=user_id,
            total_nodes=total_nodes,
            completed_nodes=0,
            current_node_index=0,
            start_time=datetime.utcnow(),
            estimated_completion=datetime.utcnow() + timedelta(
                minutes=total_nodes * estimated_minutes_per_node
            )
        )
        
        self.path_progress[path_id] = progress
        return progress
    
    def update_node_progress(
        self,
        path_id: str,
        node_id: str,
        status: str,  # not_started, in_progress, completed
        progress_percentage: float = 0
    ) -> Dict[str, Any]:
        """更新节点进度"""
        if path_id not in self.path_progress:
            return {'error': 'Path not found'}
        
        path_progress = self.path_progress[path_id]
        
        path_progress.node_progress[node_id] = {
            'status': status,
            'progress': progress_percentage,
            'updated_at': datetime.utcnow().isoformat()
        }
        
        # 更新整体进度
        if status == 'completed':
            path_progress.completed_nodes += 1
        
        # 保存历史快照
        self._save_snapshot(path_progress)
        
        return {
            'path_id': path_id,
            'node_id': node_id,
            'overall_progress': path_progress.get_overall_progress(),
            'completed_nodes': path_progress.completed_nodes,
            'remaining_nodes': path_progress.total_nodes - path_progress.completed_nodes
        }
    
    def _save_snapshot(self, path_progress: LearningPathProgress):
        """保存进度快照"""
        snapshot = ProgressSnapshot(
            timestamp=datetime.utcnow(),
            metrics={
                'overall_progress': path_progress.get_overall_progress(),
                'completed_nodes': path_progress.completed_nodes
            },
            milestones_reached=[]
        )
        
        self.progress_history[path_progress.user_id].append(snapshot)
    
    def get_path_progress(self, path_id: str) -> Optional[Dict]:
        """获取路径进度"""
        if path_id not in self.path_progress:
            return None
        
        progress = self.path_progress[path_id]
        
        return {
            'path_id': path_id,
            'user_id': progress.user_id,
            'total_nodes': progress.total_nodes,
            'completed_nodes': progress.completed_nodes,
            'current_node_index': progress.current_node_index,
            'overall_progress': progress.get_overall_progress(),
            'start_time': progress.start_time.isoformat() if progress.start_time else None,
            'estimated_completion': progress.estimated_completion.isoformat() if progress.estimated_completion else None,
            'estimated_remaining_minutes': progress.get_estimated_remaining_time(),
            'node_details': progress.node_progress
        }
    
    def get_progress_visualization_data(
        self,
        user_id: str,
        days: int = 30
    ) -> Dict[str, Any]:
        """
        获取进度可视化数据
        
        生成适合图表展示的数据格式
        """
        # 学习活动数据
        daily_activity = []
        today = datetime.utcnow().date()
        
        for i in range(days):
            date = today - timedelta(days=i)
            date_str = date.isoformat()
            
            stats = self.daily_stats[user_id].get(date_str, {})
            
            daily_activity.append({
                'date': date_str,
                'concepts_studied': stats.get('concepts', 0),
                'exercises_completed': stats.get('exercises', 0),
                'minutes_spent': stats.get('minutes', 0),
                'day_of_week': date.strftime('%A')
            })
        
        daily_activity.reverse()
        
        # 计算统计数据
        total_minutes = sum(d['minutes_spent'] for d in daily_activity)
        active_days = sum(1 for d in daily_activity if d['minutes_spent'] > 0)
        
        # 周趋势
        weekly_trend = self._calculate_weekly_trend(daily_activity)
        
        return {
            'user_id': user_id,
            'period_days': days,
            'daily_activity': daily_activity,
            'summary': {
                'total_minutes': total_minutes,
                'active_days': active_days,
                'average_daily_minutes': total_minutes / days if days > 0 else 0,
                'current_streak': self._calculate_streak(user_id),
                'longest_streak': self._get_longest_streak(user_id)
            },
            'weekly_trend': weekly_trend
        }
    
    def _calculate_weekly_trend(
        self,
        daily_activity: List[Dict]
    ) -> List[Dict]:
        """计算周趋势"""
        weekly_data = defaultdict(lambda: {'minutes': 0, 'concepts': 0})
        
        for day in daily_activity:
            date = datetime.fromisoformat(day['date'])
            week_key = date.strftime('%Y-W%U')
            
            weekly_data[week_key]['minutes'] += day['minutes_spent']
            weekly_data[week_key]['concepts'] += day['concepts_studied']
        
        return [
            {
                'week': week,
                'total_minutes': data['minutes'],
                'total_concepts': data['concepts']
            }
            for week, data in sorted(weekly_data.items())
        ]
    
    def _calculate_streak(self, user_id: str) -> int:
        """计算当前连续天数"""
        today = datetime.utcnow().date()
        streak = 0
        
        for i in range(365):  # 最多查一年
            date = today - timedelta(days=i)
            date_str = date.isoformat()
            
            stats = self.daily_stats[user_id].get(date_str, {})
            
            if stats.get('minutes', 0) > 0:
                streak += 1
            else:
                if i > 0:  # 今天可以是0，但如果不是今天则中断
                    break
        
        return streak
    
    def _get_longest_streak(self, user_id: str) -> int:
        """获取最长连续天数"""
        max_streak = 0
        current_streak = 0
        
        # 获取所有有记录的日期
        dates_with_activity = [
            datetime.fromisoformat(d).date()
            for d in self.daily_stats[user_id].keys()
            if self.daily_stats[user_id][d].get('minutes', 0) > 0
        ]
        
        if not dates_with_activity:
            return 0
        
        dates_with_activity.sort()
        
        for i, date in enumerate(dates_with_activity):
            if i == 0:
                current_streak = 1
            elif (date - dates_with_activity[i-1]).days == 1:
                current_streak += 1
            else:
                max_streak = max(max_streak, current_streak)
                current_streak = 1
        
        return max(max_streak, current_streak)
    
    def record_daily_activity(
        self,
        user_id: str,
        date: Optional[datetime] = None,
        concepts: int = 0,
        exercises: int = 0,
        minutes: int = 0
    ):
        """记录每日活动"""
        if date is None:
            date = datetime.utcnow()
        
        date_str = date.date().isoformat()
        
        self.daily_stats[user_id][date_str]['concepts'] += concepts
        self.daily_stats[user_id][date_str]['exercises'] += exercises
        self.daily_stats[user_id][date_str]['minutes'] += minutes
    
    def generate_heatmap_data(
        self,
        user_id: str,
        year: Optional[int] = None
    ) -> List[Dict]:
        """
        生成热力图数据（类似GitHub贡献图）
        """
        if year is None:
            year = datetime.utcnow().year
        
        start_date = datetime(year, 1, 1).date()
        end_date = datetime(year, 12, 31).date()
        
        heatmap_data = []
        current_date = start_date
        
        while current_date <= end_date:
            date_str = current_date.isoformat()
            stats = self.daily_stats[user_id].get(date_str, {})
            minutes = stats.get('minutes', 0)
            
            # 计算活跃度等级
            if minutes == 0:
                level = 0
            elif minutes < 15:
                level = 1
            elif minutes < 30:
                level = 2
            elif minutes < 60:
                level = 3
            else:
                level = 4
            
            heatmap_data.append({
                'date': date_str,
                'level': level,
                'minutes': minutes,
                'week': current_date.isocalendar()[1],
                'day_of_week': current_date.weekday()
            })
            
            current_date += timedelta(days=1)
        
        return heatmap_data
    
    def get_skill_tree_data(
        self,
        user_id: str,
        knowledge_graph=None
    ) -> Dict[str, Any]:
        """
        获取技能树数据
        
        用于可视化展示知识掌握情况
        """
        # 简化的技能树结构
        # 实际应用中应该从知识图谱构建
        
        skill_tree = {
            'root': {
                'name': '数学基础',
                'id': 'math_foundation',
                'progress': 0,
                'children': [
                    {
                        'name': '代数',
                        'id': 'algebra',
                        'progress': 0.3,
                        'children': [
                            {'name': '线性代数', 'id': 'linear_algebra', 'progress': 0.2},
                            {'name': '抽象代数', 'id': 'abstract_algebra', 'progress': 0}
                        ]
                    },
                    {
                        'name': '分析',
                        'id': 'analysis',
                        'progress': 0.4,
                        'children': [
                            {'name': '微积分', 'id': 'calculus', 'progress': 0.5},
                            {'name': '实分析', 'id': 'real_analysis', 'progress': 0.1}
                        ]
                    },
                    {
                        'name': '几何',
                        'id': 'geometry',
                        'progress': 0.2,
                        'children': [
                            {'name': '欧几里得几何', 'id': 'euclidean', 'progress': 0.3},
                            {'name': '拓扑学', 'id': 'topology', 'progress': 0}
                        ]
                    }
                ]
            }
        }
        
        return skill_tree


def generate_progress_report(
    user_id: str,
    tracker: ProgressTracker,
    milestone_manager: MilestoneManager,
    days: int = 30
) -> Dict[str, Any]:
    """
    生成进度报告
    
    整合所有进度数据生成综合报告
    """
    # 获取各项数据
    visualization_data = tracker.get_progress_visualization_data(user_id, days)
    milestones = milestone_manager.get_user_milestones(user_id)
    heatmap = tracker.generate_heatmap_data(user_id)
    skill_tree = tracker.get_skill_tree_data(user_id)
    
    # 生成洞察
    insights = []
    
    if visualization_data['summary']['current_streak'] >= 7:
        insights.append({
            'type': 'positive',
            'message': f'您已连续学习{visualization_data["summary"]["current_streak"]}天，保持这个势头！'
        })
    
    if visualization_data['summary']['active_days'] < days * 0.3:
        insights.append({
            'type': 'suggestion',
            'message': '建议增加学习频率，每天哪怕15分钟也能取得显著进步'
        })
    
    # 计算效率
    total_minutes = visualization_data['summary']['total_minutes']
    active_days = visualization_data['summary']['active_days']
    avg_efficiency = total_minutes / active_days if active_days > 0 else 0
    
    return {
        'user_id': user_id,
        'report_period_days': days,
        'generated_at': datetime.utcnow().isoformat(),
        'summary': visualization_data['summary'],
        'insights': insights,
        'detailed_data': {
            'daily_activity': visualization_data['daily_activity'],
            'heatmap': heatmap,
            'milestones': milestones,
            'skill_tree': skill_tree
        },
        'recommendations': generate_recommendations(visualization_data, milestones)
    }


def generate_recommendations(
    visualization_data: Dict,
    milestones: Dict
) -> List[str]:
    """生成个性化建议"""
    recommendations = []
    
    summary = visualization_data['summary']
    
    # 基于活跃度
    if summary['active_days'] < 10:
        recommendations.append('建议设定每日学习提醒，培养学习习惯')
    
    # 基于时长
    if summary['average_daily_minutes'] < 20:
        recommendations.append('可以尝试增加每次学习的时长，深度理解需要持续投入')
    elif summary['average_daily_minutes'] > 90:
        recommendations.append('学习效率很高，注意适当休息避免疲劳')
    
    # 基于里程碑
    in_progress = milestones.get('in_progress_count', 0)
    if in_progress > 0:
        recommendations.append(f'您有{in_progress}个里程碑正在进行中，加油！')
    
    return recommendations
