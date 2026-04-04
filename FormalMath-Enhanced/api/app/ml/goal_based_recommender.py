"""
目标导向推荐系统
基于学习目标生成个性化学习路径
"""
import numpy as np
from typing import Dict, List, Optional, Tuple, Any, Set
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from enum import Enum
import json


class GoalType(Enum):
    """目标类型"""
    EXAM_PREP = "exam_preparation"       # 考试准备
    SKILL_MASTERY = "skill_mastery"      # 技能掌握
    CAREER = "career"                    # 职业发展
    PROJECT = "project"                  # 项目需求
    GENERAL = "general"                  # 一般学习


@dataclass
class LearningGoal:
    """学习目标"""
    goal_id: str
    user_id: str
    goal_type: GoalType
    title: str
    description: str = ""
    
    # 目标参数
    target_concepts: List[str] = field(default_factory=list)
    target_mastery: float = 0.8
    deadline: Optional[datetime] = None
    priority: int = 1  # 1-5
    
    # 约束
    max_daily_time: int = 120  # 分钟
    preferred_learning_days: List[int] = field(default_factory=lambda: [0, 1, 2, 3, 4, 5, 6])
    
    created_at: datetime = field(default_factory=datetime.utcnow)
    
    def to_dict(self) -> Dict:
        return {
            'goal_id': self.goal_id,
            'user_id': self.user_id,
            'goal_type': self.goal_type.value,
            'title': self.title,
            'description': self.description,
            'target_concepts': self.target_concepts,
            'target_mastery': self.target_mastery,
            'deadline': self.deadline.isoformat() if self.deadline else None,
            'priority': self.priority,
            'max_daily_time': self.max_daily_time,
            'preferred_learning_days': self.preferred_learning_days,
            'created_at': self.created_at.isoformat()
        }


@dataclass
class GoalProgress:
    """目标进度"""
    goal_id: str
    user_id: str
    
    completed_concepts: List[str] = field(default_factory=list)
    concept_mastery: Dict[str, float] = field(default_factory=dict)
    time_spent: int = 0  # 分钟
    
    # 进度指标
    completion_rate: float = 0.0
    estimated_completion: Optional[datetime] = None
    
    updated_at: datetime = field(default_factory=datetime.utcnow)
    
    def to_dict(self) -> Dict:
        return {
            'goal_id': self.goal_id,
            'user_id': self.user_id,
            'completed_concepts': self.completed_concepts,
            'concept_mastery': self.concept_mastery,
            'time_spent': self.time_spent,
            'completion_rate': self.completion_rate,
            'estimated_completion': self.estimated_completion.isoformat() if self.estimated_completion else None,
            'updated_at': self.updated_at.isoformat()
        }


class GoalAnalyzer:
    """目标分析器"""
    
    def __init__(self, knowledge_graph: Any):
        self.knowledge_graph = knowledge_graph
        
    def analyze_goal(self, goal: LearningGoal, user_profile: Dict) -> Dict[str, Any]:
        """
        分析目标可行性
        
        Returns:
            {
                'feasible': bool,
                'estimated_days': int,
                'required_concepts': List[str],
                'gaps': List[str],
                'recommendations': List[str]
            }
        """
        # 获取所有需要学习的概念
        all_required = set()
        for target in goal.target_concepts:
            prereqs = self.knowledge_graph.graph.get_all_prerequisites(target)
            all_required.update(prereqs)
        
        # 排除已掌握的
        known_concepts = set(user_profile.get('known_concepts', []))
        to_learn = all_required - known_concepts
        
        # 估计学习时间
        total_time = 0
        for concept in to_learn:
            node = self.knowledge_graph.graph.nodes.get(concept)
            if node:
                total_time += 20 + node.difficulty * 40  # 20-60分钟
        
        # 计算所需天数
        daily_available = goal.max_daily_time
        estimated_days = int(np.ceil(total_time / daily_available))
        
        # 检查可行性
        feasible = True
        recommendations = []
        
        if goal.deadline:
            days_until_deadline = (goal.deadline - datetime.utcnow()).days
            if estimated_days > days_until_deadline:
                feasible = False
                recommendations.append(
                    f"估计需要{estimated_days}天，但只剩{days_until_deadline}天。建议减少目标范围或增加每日学习时间。"
                )
        
        # 识别知识缺口
        gaps = []
        for concept in to_learn:
            node = self.knowledge_graph.graph.nodes.get(concept)
            if node and node.difficulty > 0.7:
                gaps.append(concept)
        
        if len(gaps) > len(to_learn) * 0.5:
            recommendations.append("前置知识缺口较多，建议先学习基础概念。")
        
        return {
            'feasible': feasible,
            'estimated_days': estimated_days,
            'total_concepts': len(to_learn),
            'required_concepts': list(to_learn),
            'gaps': gaps,
            'recommendations': recommendations
        }
    
    def decompose_goal(self, goal: LearningGoal) -> List[Dict]:
        """将目标分解为子目标"""
        subgoals = []
        
        # 按前置依赖分组
        concept_groups = self._group_by_prerequisites(goal.target_concepts)
        
        for i, group in enumerate(concept_groups):
            subgoal = {
                'subgoal_id': f"{goal.goal_id}_sub_{i}",
                'title': f"阶段 {i+1}: {self._get_group_name(group)}",
                'concepts': group,
                'estimated_days': self._estimate_group_time(group) // goal.max_daily_time + 1,
                'dependencies': subgoals[-1]['subgoal_id'] if subgoals else None
            }
            subgoals.append(subgoal)
        
        return subgoals
    
    def _group_by_prerequisites(self, target_concepts: List[str]) -> List[List[str]]:
        """按前置依赖分组概念"""
        # 获取所有概念及其层级
        levels = {}
        
        for target in target_concepts:
            self._compute_concept_level(target, levels, 0)
        
        # 按层级分组
        max_level = max(levels.values()) if levels else 0
        groups = [[] for _ in range(max_level + 1)]
        
        for concept, level in levels.items():
            groups[level].append(concept)
        
        # 过滤空组
        return [g for g in groups if g]
    
    def _compute_concept_level(self, concept: str, levels: Dict, current_level: int):
        """递归计算概念层级"""
        if concept in levels and levels[concept] >= current_level:
            return
        
        levels[concept] = current_level
        
        # 查找依赖当前概念的概念
        for neighbor, _ in self.knowledge_graph.graph.get_neighbors(concept, 'prerequisite'):
            self._compute_concept_level(neighbor, levels, current_level + 1)
    
    def _get_group_name(self, group: List[str]) -> str:
        """获取组名"""
        if not group:
            return ""
        
        # 使用第一个概念名
        node = self.knowledge_graph.graph.nodes.get(group[0])
        return node.name if node else group[0]
    
    def _estimate_group_time(self, group: List[str]) -> int:
        """估计组学习时间"""
        total = 0
        for concept in group:
            node = self.knowledge_graph.graph.nodes.get(concept)
            if node:
                total += 20 + node.difficulty * 40
        return total


class GoalBasedRecommender:
    """
    目标导向推荐器
    基于学习目标推荐学习内容和顺序
    """
    
    def __init__(
        self,
        knowledge_graph: Any,
        path_planner: Any
    ):
        self.knowledge_graph = knowledge_graph
        self.path_planner = path_planner
        self.goal_analyzer = GoalAnalyzer(knowledge_graph)
        
        # 存储
        self.active_goals: Dict[str, LearningGoal] = {}
        self.goal_progress: Dict[str, GoalProgress] = {}
        self.goal_history: Dict[str, List[Dict]] = {}
    
    def create_goal(
        self,
        user_id: str,
        goal_data: Dict[str, Any]
    ) -> LearningGoal:
        """创建学习目标"""
        goal = LearningGoal(
            goal_id=f"goal_{user_id}_{int(datetime.utcnow().timestamp())}",
            user_id=user_id,
            goal_type=GoalType(goal_data.get('goal_type', 'general')),
            title=goal_data['title'],
            description=goal_data.get('description', ''),
            target_concepts=goal_data.get('target_concepts', []),
            target_mastery=goal_data.get('target_mastery', 0.8),
            deadline=datetime.fromisoformat(goal_data['deadline']) if 'deadline' in goal_data else None,
            priority=goal_data.get('priority', 1),
            max_daily_time=goal_data.get('max_daily_time', 120)
        )
        
        self.active_goals[goal.goal_id] = goal
        self.goal_progress[goal.goal_id] = GoalProgress(
            goal_id=goal.goal_id,
            user_id=user_id
        )
        
        return goal
    
    def get_recommendations(
        self,
        user_id: str,
        goal_id: Optional[str] = None,
        current_context: Optional[Dict] = None
    ) -> Dict[str, Any]:
        """
        获取目标导向推荐
        
        Returns:
            {
                'goal': LearningGoal,
                'progress': GoalProgress,
                'next_steps': List[Dict],
                'recommended_content': List[Dict],
                'schedule': Dict
            }
        """
        # 如果没有指定目标，使用最高优先级的活跃目标
        if goal_id is None:
            goal_id = self._get_highest_priority_goal(user_id)
        
        if goal_id is None or goal_id not in self.active_goals:
            return self._get_default_recommendations(user_id)
        
        goal = self.active_goals[goal_id]
        progress = self.goal_progress[goal_id]
        
        # 更新进度
        self._update_progress(goal, progress, current_context)
        
        # 生成下一步建议
        next_steps = self._generate_next_steps(goal, progress)
        
        # 推荐内容
        recommended_content = self._recommend_content(goal, progress, next_steps)
        
        # 生成学习计划
        schedule = self._generate_schedule(goal, progress)
        
        return {
            'goal': goal.to_dict(),
            'progress': progress.to_dict(),
            'next_steps': next_steps,
            'recommended_content': recommended_content,
            'schedule': schedule,
            'estimated_completion': progress.estimated_completion.isoformat() if progress.estimated_completion else None
        }
    
    def _get_highest_priority_goal(self, user_id: str) -> Optional[str]:
        """获取用户最高优先级的目标"""
        user_goals = [
            (gid, goal) for gid, goal in self.active_goals.items()
            if goal.user_id == user_id
        ]
        
        if not user_goals:
            return None
        
        # 按优先级和截止日期排序
        user_goals.sort(key=lambda x: (-x[1].priority, x[1].deadline or datetime.max))
        return user_goals[0][0]
    
    def _get_default_recommendations(self, user_id: str) -> Dict[str, Any]:
        """获取默认推荐（无活跃目标时）"""
        return {
            'goal': None,
            'progress': None,
            'next_steps': [],
            'recommended_content': [],
            'schedule': {},
            'message': '没有活跃的学习目标。建议创建一个学习目标以获得个性化推荐。'
        }
    
    def _update_progress(
        self,
        goal: LearningGoal,
        progress: GoalProgress,
        context: Optional[Dict]
    ):
        """更新目标进度"""
        if context is None:
            return
        
        # 更新已完成的
        completed = context.get('completed_concepts', [])
        for concept in completed:
            if concept not in progress.completed_concepts:
                progress.completed_concepts.append(concept)
        
        # 更新掌握度
        mastery = context.get('concept_mastery', {})
        progress.concept_mastery.update(mastery)
        
        # 更新时间
        progress.time_spent += context.get('session_time', 0)
        
        # 计算完成率
        total_concepts = len(goal.target_concepts)
        if total_concepts > 0:
            progress.completion_rate = len(progress.completed_concepts) / total_concepts
        
        # 估计完成时间
        if progress.completion_rate > 0:
            elapsed_time = (datetime.utcnow() - goal.created_at).total_seconds() / 3600  # 小时
            estimated_total = elapsed_time / progress.completion_rate
            remaining_hours = estimated_total * (1 - progress.completion_rate)
            progress.estimated_completion = datetime.utcnow() + timedelta(hours=remaining_hours)
        
        progress.updated_at = datetime.utcnow()
    
    def _generate_next_steps(
        self,
        goal: LearningGoal,
        progress: GoalProgress
    ) -> List[Dict]:
        """生成下一步学习建议"""
        # 获取剩余概念
        remaining = set(goal.target_concepts) - set(progress.completed_concepts)
        
        if not remaining:
            return [{'type': 'goal_complete', 'message': '恭喜！目标已完成'}]
        
        # 获取已掌握的概念
        known = set(progress.completed_concepts)
        known.update([c for c, m in progress.concept_mastery.items() if m >= 0.6])
        
        # 使用知识图谱推荐
        recommendations = self.knowledge_graph.recommend_next_concepts(
            current_concepts=known,
            target_concepts=remaining,
            top_k=5
        )
        
        steps = []
        for rec in recommendations:
            concept_id = rec['concept_id']
            node = self.knowledge_graph.graph.nodes.get(concept_id)
            
            steps.append({
                'type': 'learn_concept',
                'concept_id': concept_id,
                'concept_name': node.name if node else concept_id,
                'priority': rec['priority_score'],
                'estimated_time': 20 + (node.difficulty * 40 if node else 30),
                'rationale': f'学习目标"{goal.title}"所需的前置知识'
            })
        
        return steps
    
    def _recommend_content(
        self,
        goal: LearningGoal,
        progress: GoalProgress,
        next_steps: List[Dict]
    ) -> List[Dict]:
        """推荐学习内容"""
        content = []
        
        for step in next_steps[:3]:  # 为前3个步骤推荐内容
            if step['type'] != 'learn_concept':
                continue
            
            concept_id = step['concept_id']
            node = self.knowledge_graph.graph.nodes.get(concept_id)
            
            # 根据目标类型调整内容推荐
            if goal.goal_type == GoalType.EXAM_PREP:
                content_types = ['practice_exam', 'summary', 'quiz']
            elif goal.goal_type == GoalType.SKILL_MASTERY:
                content_types = ['exercise', 'project', 'tutorial']
            else:
                content_types = ['video', 'reading', 'exercise']
            
            content.append({
                'concept_id': concept_id,
                'concept_name': step['concept_name'],
                'content_types': content_types,
                'difficulty': node.difficulty if node else 0.5,
                'estimated_time': step['estimated_time'],
                'goal_alignment': 'high'
            })
        
        return content
    
    def _generate_schedule(
        self,
        goal: LearningGoal,
        progress: GoalProgress
    ) -> Dict:
        """生成学习计划"""
        remaining = set(goal.target_concepts) - set(progress.completed_concepts)
        
        if not remaining or not goal.deadline:
            return {}
        
        days_until_deadline = (goal.deadline - datetime.utcnow()).days
        
        # 估计每天需要学习的概念数
        concepts_per_day = len(remaining) / max(days_until_deadline, 1)
        
        # 生成每日计划
        schedule = []
        remaining_list = list(remaining)
        
        for day in range(min(days_until_deadline, 14)):  # 最多14天
            daily_concepts = remaining_list[
                int(day * concepts_per_day):int((day + 1) * concepts_per_day)
            ]
            
            daily_time = sum(
                20 + self.knowledge_graph.graph.nodes.get(c, ConceptNode(c, c)).difficulty * 40
                for c in daily_concepts
            ) if daily_concepts else 0
            
            schedule.append({
                'day': day + 1,
                'date': (datetime.utcnow() + timedelta(days=day)).strftime('%Y-%m-%d'),
                'concepts': daily_concepts,
                'estimated_time': int(daily_time),
                'feasible': daily_time <= goal.max_daily_time
            })
        
        return {
            'days_until_deadline': days_until_deadline,
            'concepts_remaining': len(remaining),
            'daily_plan': schedule,
            'warnings': self._generate_schedule_warnings(schedule, goal)
        }
    
    def _generate_schedule_warnings(self, schedule: List[Dict], goal: LearningGoal) -> List[str]:
        """生成计划警告"""
        warnings = []
        
        overloaded_days = [s['day'] for s in schedule if not s['feasible']]
        if overloaded_days:
            warnings.append(f"第{overloaded_days}天学习负荷过重，建议调整计划")
        
        return warnings
    
    def complete_goal(self, goal_id: str, success: bool = True):
        """完成目标"""
        if goal_id not in self.active_goals:
            return
        
        goal = self.active_goals[goal_id]
        progress = self.goal_progress[goal_id]
        
        # 记录历史
        if goal.user_id not in self.goal_history:
            self.goal_history[goal.user_id] = []
        
        self.goal_history[goal.user_id].append({
            'goal': goal.to_dict(),
            'progress': progress.to_dict(),
            'completed_at': datetime.utcnow().isoformat(),
            'success': success
        })
        
        # 从活跃目标中移除
        del self.active_goals[goal_id]
        del self.goal_progress[goal_id]
    
    def get_goal_statistics(self, user_id: str) -> Dict:
        """获取目标统计"""
        user_goals = [
            (gid, g) for gid, g in self.active_goals.items()
            if g.user_id == user_id
        ]
        
        history = self.goal_history.get(user_id, [])
        
        completed_goals = [h for h in history if h['success']]
        failed_goals = [h for h in history if not h['success']]
        
        return {
            'active_goals': len(user_goals),
            'completed_goals': len(completed_goals),
            'failed_goals': len(failed_goals),
            'completion_rate': len(completed_goals) / len(history) if history else 0,
            'average_completion_time': np.mean([
                (datetime.fromisoformat(h['completed_at']) - 
                 datetime.fromisoformat(h['goal']['created_at'])).days
                for h in completed_goals
            ]) if completed_goals else 0
        }


# Helper dataclass for default concept node
@dataclass
class _DefaultConceptNode:
    concept_id: str
    name: str = ""
    difficulty: float = 0.5
    importance: float = 0.5
    category: str = ""
    embedding: Any = None

# ConceptNode will be imported from knowledge_graph_embedding when available
try:
    from .knowledge_graph_embedding import ConceptNode
except ImportError:
    ConceptNode = _DefaultConceptNode
