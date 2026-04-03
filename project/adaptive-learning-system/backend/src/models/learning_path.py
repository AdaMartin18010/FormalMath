"""
学习路径模型
定义学习路径、路径节点、学习计划等数据结构
"""

from datetime import datetime, timedelta
from typing import Dict, List, Optional, Any, Tuple
from dataclasses import dataclass, field
from enum import Enum
import uuid


class PathStatus(Enum):
    """路径状态"""
    PENDING = "pending"      # 待开始
    ACTIVE = "active"        # 进行中
    PAUSED = "paused"        # 暂停
    COMPLETED = "completed"  # 已完成
    ABANDONED = "abandoned"  # 已放弃


class NodeStatus(Enum):
    """节点状态"""
    LOCKED = "locked"        # 未解锁
    AVAILABLE = "available"  # 可学习
    IN_PROGRESS = "in_progress"  # 学习中
    COMPLETED = "completed"  # 已完成
    REVIEW = "review"        # 需复习


@dataclass
class PathNode:
    """路径节点"""
    node_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    concept_id: str = ""  # 对应概念ID
    sequence_number: int = 0  # 学习顺序
    
    # 状态
    status: NodeStatus = NodeStatus.LOCKED
    
    # 时间规划
    planned_start: Optional[datetime] = None
    planned_end: Optional[datetime] = None
    actual_start: Optional[datetime] = None
    actual_end: Optional[datetime] = None
    estimated_duration: int = 60  # 预计学习时长（分钟）
    
    # 学习要求
    prerequisites: List[str] = field(default_factory=list)  # 先修节点
    mastery_threshold: float = 0.7  # 掌握度阈值
    
    # 推荐资源
    recommended_resources: List[str] = field(default_factory=list)
    alternative_resources: List[str] = field(default_factory=list)
    
    # 进度
    completion_percentage: float = 0.0  # 完成百分比
    mastery_level: float = 0.0  # 掌握水平
    
    # 元数据
    difficulty: float = 1.0  # 难度系数
    importance: float = 1.0  # 重要程度
    
    def is_available(self, completed_nodes: List[str]) -> bool:
        """检查节点是否可学习"""
        if not self.prerequisites:
            return True
        return all(prereq in completed_nodes for prereq in self.prerequisites)
    
    def calculate_progress(self) -> float:
        """计算学习进度"""
        return self.completion_percentage
    
    def is_completed(self) -> bool:
        """检查是否完成"""
        return self.status == NodeStatus.COMPLETED or self.mastery_level >= self.mastery_threshold


@dataclass
class LearningPath:
    """学习路径"""
    path_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    learner_id: str = ""
    
    # 基本信息
    name: str = ""  # 路径名称
    description: str = ""  # 路径描述
    goal: str = ""  # 学习目标
    
    # 路径节点
    nodes: Dict[str, PathNode] = field(default_factory=dict)  # 节点字典
    node_order: List[str] = field(default_factory=list)  # 节点顺序
    
    # 状态
    status: PathStatus = PathStatus.PENDING
    
    # 时间规划
    created_at: datetime = field(default_factory=datetime.now)
    started_at: Optional[datetime] = None
    target_completion: Optional[datetime] = None
    completed_at: Optional[datetime] = None
    
    # 路径特性
    total_estimated_hours: float = 0.0  # 预计总时长（小时）
    difficulty_curve: List[float] = field(default_factory=list)  # 难度曲线
    diversity_score: float = 0.0  # 路径多样性得分
    
    # 元数据
    algorithm_used: str = ""  # 使用的算法
    constraints: Dict[str, Any] = field(default_factory=dict)  # 约束条件
    
    def get_current_node(self) -> Optional[PathNode]:
        """获取当前学习节点"""
        for node_id in self.node_order:
            node = self.nodes.get(node_id)
            if node and node.status in [NodeStatus.IN_PROGRESS, NodeStatus.AVAILABLE]:
                return node
        return None
    
    def get_completed_nodes(self) -> List[str]:
        """获取已完成节点"""
        return [
            node_id for node_id in self.node_order
            if self.nodes[node_id].status == NodeStatus.COMPLETED
        ]
    
    def get_available_nodes(self) -> List[PathNode]:
        """获取可学习节点"""
        completed = self.get_completed_nodes()
        available = []
        for node_id in self.node_order:
            node = self.nodes[node_id]
            if node.is_available(completed) and node.status == NodeStatus.LOCKED:
                node.status = NodeStatus.AVAILABLE
            if node.status == NodeStatus.AVAILABLE:
                available.append(node)
        return available
    
    def update_progress(self, node_id: str, progress: float, mastery: float):
        """更新节点进度"""
        if node_id in self.nodes:
            node = self.nodes[node_id]
            node.completion_percentage = progress
            node.mastery_level = mastery
            
            if mastery >= node.mastery_threshold:
                node.status = NodeStatus.COMPLETED
                node.actual_end = datetime.now()
                self._update_available_nodes()
    
    def _update_available_nodes(self):
        """更新可用节点状态"""
        completed = self.get_completed_nodes()
        for node_id in self.node_order:
            node = self.nodes[node_id]
            if node.status == NodeStatus.LOCKED and node.is_available(completed):
                node.status = NodeStatus.AVAILABLE
    
    def calculate_overall_progress(self) -> float:
        """计算整体进度"""
        if not self.nodes:
            return 0.0
        total_progress = sum(node.completion_percentage for node in self.nodes.values())
        return total_progress / len(self.nodes)
    
    def get_remaining_time(self) -> float:
        """获取剩余学习时长（小时）"""
        remaining = 0.0
        for node_id in self.node_order:
            node = self.nodes[node_id]
            if node.status != NodeStatus.COMPLETED:
                remaining += node.estimated_duration / 60
        return remaining
    
    def get_estimated_completion(self) -> Optional[datetime]:
        """获取预计完成时间"""
        remaining_hours = self.get_remaining_time()
        if remaining_hours <= 0:
            return datetime.now()
        return datetime.now() + timedelta(hours=remaining_hours)
    
    def to_dict(self) -> Dict[str, Any]:
        """转换为字典"""
        return {
            "path_id": self.path_id,
            "learner_id": self.learner_id,
            "name": self.name,
            "description": self.description,
            "goal": self.goal,
            "status": self.status.value,
            "progress": self.calculate_overall_progress(),
            "total_nodes": len(self.nodes),
            "completed_nodes": len(self.get_completed_nodes()),
            "remaining_hours": self.get_remaining_time(),
            "created_at": self.created_at.isoformat(),
            "node_order": self.node_order
        }


@dataclass
class PathAdjustment:
    """路径调整记录"""
    adjustment_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    path_id: str = ""
    
    # 调整原因
    reason: str = ""
    trigger_type: str = ""  # 触发类型 (progress/difficulty/feedback/time)
    
    # 调整内容
    adjustments_made: Dict[str, Any] = field(default_factory=dict)
    nodes_added: List[str] = field(default_factory=list)
    nodes_removed: List[str] = field(default_factory=list)
    nodes_reordered: Dict[str, int] = field(default_factory=dict)
    
    # 时间戳
    created_at: datetime = field(default_factory=datetime.now)
    
    # 效果评估
    expected_improvement: float = 0.0  # 预期改进
    actual_improvement: Optional[float] = None  # 实际改进


@dataclass
class LearningSchedule:
    """学习计划"""
    schedule_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    path_id: str = ""
    learner_id: str = ""
    
    # 日程安排
    daily_plans: Dict[str, List[Dict[str, Any]]] = field(default_factory=dict)
    # 格式: {"2026-04-03": [{"node_id": "...", "duration": 60, "time_slot": "09:00"}]}
    
    # 提醒设置
    review_reminders: List[Dict[str, Any]] = field(default_factory=list)
    # 格式: [{"node_id": "...", "review_date": "...", "reminder_type": "spaced_repetition"}]
    
    # 缓冲时间
    buffer_days: int = 2  # 缓冲天数
    
    def create_schedule(self, path: LearningPath, daily_hours: float, start_date: Optional[datetime] = None):
        """根据路径创建学习计划"""
        if start_date is None:
            start_date = datetime.now()
        
        current_date = start_date
        remaining_hours_today = daily_hours
        
        for node_id in path.node_order:
            node = path.nodes[node_id]
            if node.status == NodeStatus.COMPLETED:
                continue
            
            node_hours = node.estimated_duration / 60
            
            while node_hours > 0:
                date_key = current_date.strftime("%Y-%m-%d")
                if date_key not in self.daily_plans:
                    self.daily_plans[date_key] = []
                
                hours_to_schedule = min(node_hours, remaining_hours_today)
                self.daily_plans[date_key].append({
                    "node_id": node_id,
                    "duration": int(hours_to_schedule * 60),
                    "node_name": node.concept_id
                })
                
                node_hours -= hours_to_schedule
                remaining_hours_today -= hours_to_schedule
                
                if remaining_hours_today <= 0:
                    current_date += timedelta(days=1)
                    remaining_hours_today = daily_hours
    
    def add_review_reminder(self, node_id: str, last_study_date: datetime, mastery_level: float):
        """基于遗忘曲线添加复习提醒"""
        # 简单的间隔重复算法
        if mastery_level < 0.5:
            intervals = [1, 3, 7, 14, 30]  # 天数
        elif mastery_level < 0.8:
            intervals = [3, 7, 14, 30, 60]
        else:
            intervals = [7, 14, 30, 60, 120]
        
        for interval in intervals:
            review_date = last_study_date + timedelta(days=interval)
            self.review_reminders.append({
                "node_id": node_id,
                "review_date": review_date.isoformat(),
                "reminder_type": "spaced_repetition",
                "interval_days": interval
            })
    
    def get_today_plan(self) -> List[Dict[str, Any]]:
        """获取今日计划"""
        today_key = datetime.now().strftime("%Y-%m-%d")
        return self.daily_plans.get(today_key, [])
    
    def get_upcoming_reviews(self, days: int = 7) -> List[Dict[str, Any]]:
        """获取即将到来的复习"""
        today = datetime.now()
        upcoming = []
        for reminder in self.review_reminders:
            review_date = datetime.fromisoformat(reminder["review_date"])
            if 0 <= (review_date - today).days <= days:
                upcoming.append(reminder)
        return upcoming


@dataclass
class PathRecommendation:
    """路径推荐结果"""
    recommendation_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    learner_id: str = ""
    
    # 推荐路径
    paths: List[LearningPath] = field(default_factory=list)
    
    # 推荐理由
    reasons: Dict[str, str] = field(default_factory=dict)
    # 格式: {path_id: "推荐原因"}
    
    # 匹配分数
    match_scores: Dict[str, float] = field(default_factory=dict)
    # 格式: {path_id: 匹配分数}
    
    # 多样性保证
    diversity_metrics: Dict[str, Any] = field(default_factory=dict)
    
    def get_best_path(self) -> Optional[LearningPath]:
        """获取最佳路径"""
        if not self.paths:
            return None
        return max(self.paths, key=lambda p: self.match_scores.get(p.path_id, 0))
    
    def get_alternative_paths(self, n: int = 2) -> List[Tuple[LearningPath, float]]:
        """获取备选路径"""
        scored_paths = [(p, self.match_scores.get(p.path_id, 0)) for p in self.paths]
        scored_paths.sort(key=lambda x: x[1], reverse=True)
        return scored_paths[1:n+1]


# 学习路径评估指标
class PathMetrics:
    """路径评估指标"""
    
    @staticmethod
    def calculate_smoothness(path: LearningPath) -> float:
        """计算难度曲线平滑度"""
        if len(path.difficulty_curve) < 2:
            return 1.0
        
        diffs = [
            abs(path.difficulty_curve[i] - path.difficulty_curve[i-1])
            for i in range(1, len(path.difficulty_curve))
        ]
        avg_diff = sum(diffs) / len(diffs)
        return max(0, 1 - avg_diff)
    
    @staticmethod
    def calculate_coverage(path: LearningPath, target_concepts: List[str]) -> float:
        """计算目标概念覆盖率"""
        if not target_concepts:
            return 0.0
        path_concepts = set(node.concept_id for node in path.nodes.values())
        covered = sum(1 for c in target_concepts if c in path_concepts)
        return covered / len(target_concepts)
    
    @staticmethod
    def calculate_efficiency(path: LearningPath) -> float:
        """计算学习效率"""
        if not path.nodes:
            return 0.0
        completed = len(path.get_completed_nodes())
        total_time = sum(
            node.estimated_duration for node in path.nodes.values()
        ) / 60  # 小时
        return completed / max(total_time, 0.1)
