"""
学习小组推荐系统
智能组队、小组优化、协同学习
"""
import numpy as np
from typing import Dict, List, Optional, Tuple, Set
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from collections import defaultdict
import random


@dataclass
class StudyGroup:
    """学习小组"""
    group_id: str
    name: str
    description: str
    
    # 成员
    members: List[str] = field(default_factory=list)
    max_members: int = 6
    
    # 学习目标
    target_concepts: List[str] = field(default_factory=list)
    difficulty_level: float = 0.5
    
    # 小组属性
    created_at: datetime = field(default_factory=datetime.utcnow)
    activity_level: float = 0.0  # 活跃度
    completion_rate: float = 0.0
    
    # 元数据
    tags: List[str] = field(default_factory=list)
    meeting_schedule: Dict = field(default_factory=dict)
    
    def is_full(self) -> bool:
        return len(self.members) >= self.max_members
    
    def can_join(self) -> bool:
        return not self.is_full()


@dataclass
class GroupMatchScore:
    """小组匹配分数"""
    group_id: str
    user_id: str
    overall_score: float
    fit_scores: Dict[str, float]
    reasons: List[str]
    concerns: List[str]


class GroupRecommender:
    """
    小组推荐器
    
    为用户推荐合适的学习小组，或创建最优小组
    """
    
    def __init__(self):
        self.groups: Dict[str, StudyGroup] = {}
        self.user_profiles: Dict[str, Dict] = {}
        self.group_interactions: Dict[str, List[Dict]] = defaultdict(list)
        
        # 匹配权重
        self.weights = {
            'goal_alignment': 0.25,
            'level_compatibility': 0.20,
            'diversity': 0.15,
            'schedule_fit': 0.15,
            'social_dynamics': 0.15,
            'activity_match': 0.10
        }
    
    def add_group(self, group: StudyGroup):
        """添加小组"""
        self.groups[group.group_id] = group
    
    def add_user_profile(self, user_id: str, profile: Dict):
        """添加用户档案"""
        self.user_profiles[user_id] = profile
    
    def recommend_groups(
        self,
        user_id: str,
        top_k: int = 5,
        include_full: bool = False
    ) -> List[GroupMatchScore]:
        """
        为用户推荐小组
        
        Args:
            user_id: 用户ID
            top_k: 返回数量
            include_full: 是否包含已满的小组
        
        Returns:
            小组匹配分数列表
        """
        if user_id not in self.user_profiles:
            return []
        
        user_profile = self.user_profiles[user_id]
        
        scores = []
        for group in self.groups.values():
            if not include_full and group.is_full():
                continue
            
            if user_id in group.members:
                continue
            
            score = self._calculate_group_match(user_id, user_profile, group)
            scores.append(score)
        
        scores.sort(key=lambda x: x.overall_score, reverse=True)
        return scores[:top_k]
    
    def _calculate_group_match(
        self,
        user_id: str,
        user_profile: Dict,
        group: StudyGroup
    ) -> GroupMatchScore:
        """计算用户与小组的匹配度"""
        fit_scores = {}
        reasons = []
        concerns = []
        
        # 1. 目标对齐
        goal_score = self._calculate_goal_alignment(user_profile, group)
        fit_scores['goal_alignment'] = goal_score
        
        if goal_score > 0.7:
            reasons.append('学习目标高度契合')
        elif goal_score < 0.3:
            concerns.append('学习目标差异较大')
        
        # 2. 水平兼容性
        level_score = self._calculate_level_compatibility(user_profile, group)
        fit_scores['level_compatibility'] = level_score
        
        if level_score > 0.7:
            reasons.append('知识水平相近')
        elif level_score < 0.3:
            concerns.append('知识水平差异较大')
        
        # 3. 多样性贡献
        diversity_score = self._calculate_diversity_contribution(user_id, group)
        fit_scores['diversity'] = diversity_score
        
        if diversity_score > 0.7:
            reasons.append('能为小组带来多样性视角')
        
        # 4. 时间安排
        schedule_score = self._calculate_schedule_fit(user_profile, group)
        fit_scores['schedule_fit'] = schedule_score
        
        if schedule_score > 0.6:
            reasons.append('时间安排较为匹配')
        else:
            concerns.append('时间安排可能有冲突')
        
        # 5. 社交动态
        social_score = self._calculate_social_dynamics(user_id, group)
        fit_scores['social_dynamics'] = social_score
        
        # 6. 活跃度匹配
        activity_score = self._calculate_activity_match(user_profile, group)
        fit_scores['activity_match'] = activity_score
        
        # 综合分数
        overall = sum(
            fit_scores.get(key, 0) * weight
            for key, weight in self.weights.items()
        )
        
        # 考虑小组满员程度（略微惩罚快满的）
        if len(group.members) >= group.max_members - 1:
            overall *= 0.95
        
        return GroupMatchScore(
            group_id=group.group_id,
            user_id=user_id,
            overall_score=overall,
            fit_scores=fit_scores,
            reasons=reasons,
            concerns=concerns
        )
    
    def _calculate_goal_alignment(
        self,
        user_profile: Dict,
        group: StudyGroup
    ) -> float:
        """计算目标对齐度"""
        user_goals = set(user_profile.get('learning_goals', []))
        group_goals = set(group.target_concepts)
        
        if not user_goals or not group_goals:
            return 0.5
        
        # Jaccard相似度
        intersection = len(user_goals & group_goals)
        union = len(user_goals | group_goals)
        
        return intersection / union if union > 0 else 0
    
    def _calculate_level_compatibility(
        self,
        user_profile: Dict,
        group: StudyGroup
    ) -> float:
        """计算水平兼容性"""
        user_level = user_profile.get('knowledge_level', 0.5)
        group_level = group.difficulty_level
        
        # 接近最好
        diff = abs(user_level - group_level)
        return 1 - min(diff, 1.0)
    
    def _calculate_diversity_contribution(
        self,
        user_id: str,
        group: StudyGroup
    ) -> float:
        """计算多样性贡献"""
        if not group.members:
            return 0.5
        
        # 获取用户特征
        user_profile = self.user_profiles.get(user_id, {})
        user_style = user_profile.get('learning_style', {})
        user_knowledge = set(user_profile.get('strengths', []))
        
        # 计算与现有成员的差异
        total_diversity = 0
        for member_id in group.members:
            member_profile = self.user_profiles.get(member_id, {})
            member_style = member_profile.get('learning_style', {})
            member_knowledge = set(member_profile.get('strengths', []))
            
            # 风格差异
            style_diff = 0
            for dim in ['visual', 'active', 'sequential']:
                diff = abs(
                    user_style.get(dim, 0.5) - member_style.get(dim, 0.5)
                )
                style_diff += diff
            style_diff /= 3
            
            # 知识差异
            knowledge_diff = 1 - len(user_knowledge & member_knowledge) / max(
                len(user_knowledge | member_knowledge), 1
            )
            
            total_diversity += (style_diff + knowledge_diff) / 2
        
        avg_diversity = total_diversity / len(group.members)
        
        # 适度多样性最好
        optimal_diversity = 0.4
        return 1 - abs(avg_diversity - optimal_diversity) / optimal_diversity
    
    def _calculate_schedule_fit(
        self,
        user_profile: Dict,
        group: StudyGroup
    ) -> float:
        """计算时间安排匹配"""
        user_schedule = user_profile.get('study_schedule', {})
        group_schedule = group.meeting_schedule
        
        if not user_schedule or not group_schedule:
            return 0.5
        
        # 简单的时间重叠计算
        overlap_count = 0
        for day, hours in group_schedule.get('weekly_meetings', {}).items():
            user_available = user_schedule.get(day, [])
            for hour in hours:
                if hour in user_available:
                    overlap_count += 1
        
        total_group_hours = sum(
            len(h) for h in group_schedule.get('weekly_meetings', {}).values()
        )
        
        if total_group_hours == 0:
            return 0.5
        
        return min(1.0, overlap_count / total_group_hours)
    
    def _calculate_social_dynamics(
        self,
        user_id: str,
        group: StudyGroup
    ) -> float:
        """计算社交动态"""
        # 检查是否与现有成员有历史互动
        positive_interactions = 0
        total_interactions = 0
        
        for member_id in group.members:
            # 这里应该查询历史互动数据
            # 简化处理
            pass
        
        if total_interactions == 0:
            return 0.5
        
        return positive_interactions / total_interactions
    
    def _calculate_activity_match(
        self,
        user_profile: Dict,
        group: StudyGroup
    ) -> float:
        """计算活跃度匹配"""
        user_activity = user_profile.get('activity_level', 0.5)
        group_activity = group.activity_level
        
        # 相似最好
        return 1 - abs(user_activity - group_activity)
    
    def create_optimal_group(
        self,
        candidate_users: List[str],
        group_goal: str,
        target_size: int = 4,
        optimization_objective: str = 'balanced'
    ) -> Dict[str, Any]:
        """
        创建最优学习小组
        
        Args:
            candidate_users: 候选用户
            group_goal: 小组目标
            target_size: 目标人数
            optimization_objective: 优化目标
        
        Returns:
            小组配置建议
        """
        if len(candidate_users) < target_size:
            return {'error': 'Not enough candidates'}
        
        # 收集用户特征
        profiles = []
        for user_id in candidate_users:
            if user_id in self.user_profiles:
                profiles.append((user_id, self.user_profiles[user_id]))
        
        if len(profiles) < target_size:
            return {'error': 'Not enough valid profiles'}
        
        # 使用遗传算法或贪心算法选择最优组合
        best_combination = self._optimize_group_composition(
            profiles, target_size, optimization_objective
        )
        
        if not best_combination:
            return {'error': 'Failed to find valid combination'}
        
        # 生成小组配置
        group_config = self._generate_group_config(
            best_combination, group_goal
        )
        
        return group_config
    
    def _optimize_group_composition(
        self,
        profiles: List[Tuple[str, Dict]],
        target_size: int,
        objective: str
    ) -> List[Tuple[str, Dict]]:
        """优化小组构成"""
        n = len(profiles)
        
        if n <= target_size:
            return profiles
        
        # 贪心算法选择
        selected = [profiles[0]]  # 从第一个开始
        remaining = profiles[1:]
        
        while len(selected) < target_size and remaining:
            best_candidate = None
            best_score = -float('inf')
            
            for candidate in remaining:
                # 计算加入该候选人对小组的增益
                score = self._evaluate_addition(selected, candidate, objective)
                
                if score > best_score:
                    best_score = score
                    best_candidate = candidate
            
            if best_candidate:
                selected.append(best_candidate)
                remaining.remove(best_candidate)
        
        return selected
    
    def _evaluate_addition(
        self,
        current_group: List[Tuple[str, Dict]],
        candidate: Tuple[str, Dict],
        objective: str
    ) -> float:
        """评估添加候选人的价值"""
        if objective == 'diverse':
            # 最大化多样性
            diversity_sum = 0
            for _, member_profile in current_group:
                diversity = self._calculate_profile_diversity(
                    member_profile, candidate[1]
                )
                diversity_sum += diversity
            return diversity_sum / len(current_group) if current_group else 0.5
        
        elif objective == 'homogeneous':
            # 最小化差异（相似成员）
            similarity_sum = 0
            for _, member_profile in current_group:
                similarity = 1 - self._calculate_profile_diversity(
                    member_profile, candidate[1]
                )
                similarity_sum += similarity
            return similarity_sum / len(current_group) if current_group else 0.5
        
        else:  # balanced
            # 平衡：既有一定相似性，又有一定多样性
            diversity_scores = []
            for _, member_profile in current_group:
                div = self._calculate_profile_diversity(
                    member_profile, candidate[1]
                )
                diversity_scores.append(div)
            
            avg_diversity = np.mean(diversity_scores) if diversity_scores else 0
            # 适度多样性最好
            return 1 - abs(avg_diversity - 0.4)
    
    def _calculate_profile_diversity(
        self,
        profile_a: Dict,
        profile_b: Dict
    ) -> float:
        """计算两个档案的多样性"""
        # 学习风格差异
        style_a = profile_a.get('learning_style', {})
        style_b = profile_b.get('learning_style', {})
        
        style_diff = np.mean([
            abs(style_a.get(k, 0.5) - style_b.get(k, 0.5))
            for k in set(style_a.keys()) | set(style_b.keys())
        ]) if style_a or style_b else 0
        
        # 知识水平差异
        level_a = profile_a.get('knowledge_level', 0.5)
        level_b = profile_b.get('knowledge_level', 0.5)
        level_diff = abs(level_a - level_b)
        
        return (style_diff + level_diff) / 2
    
    def _generate_group_config(
        self,
        members: List[Tuple[str, Dict]],
        goal: str
    ) -> Dict[str, Any]:
        """生成小组配置"""
        member_ids = [m[0] for m in members]
        
        # 计算小组特征
        avg_knowledge = np.mean([
            m[1].get('knowledge_level', 0.5) for m in members
        ])
        
        # 找出共同目标
        common_goals = set()
        for _, profile in members:
            goals = set(profile.get('learning_goals', []))
            if not common_goals:
                common_goals = goals
            else:
                common_goals &= goals
        
        # 分析角色分配
        roles = self._assign_roles(members)
        
        return {
            'suggested_name': f"学习小组 - {goal}",
            'members': member_ids,
            'member_count': len(members),
            'average_knowledge_level': avg_knowledge,
            'common_goals': list(common_goals),
            'role_assignments': roles,
            'suggested_schedule': self._suggest_group_schedule(members),
            'diversity_score': self._calculate_group_diversity(members),
            'estimated_synergy': self._estimate_synergy(members)
        }
    
    def _assign_roles(
        self,
        members: List[Tuple[str, Dict]]
    ) -> Dict[str, str]:
        """分配小组角色"""
        roles = {}
        
        # 简单角色分配逻辑
        for user_id, profile in members:
            strengths = profile.get('strengths', [])
            style = profile.get('learning_style', {})
            
            if 'leadership' in strengths or style.get('extraversion', 0.5) > 0.7:
                roles[user_id] = 'coordinator'
            elif 'explanation' in strengths or style.get('verbal', 0.5) > 0.7:
                roles[user_id] = 'explainer'
            elif 'organization' in strengths:
                roles[user_id] = 'organizer'
            else:
                roles[user_id] = 'contributor'
        
        return roles
    
    def _suggest_group_schedule(
        self,
        members: List[Tuple[str, Dict]]
    ) -> Dict[str, Any]:
        """建议小组时间表"""
        # 找出共同可用时间
        common_hours = set(range(24))
        
        for _, profile in members:
            schedule = profile.get('study_schedule', {})
            user_hours = set()
            for day, hours in schedule.items():
                user_hours.update(hours)
            common_hours &= user_hours
        
        return {
            'common_available_hours': sorted(list(common_hours))[:5],
            'recommended_meeting_frequency': '每周2次',
            'recommended_session_duration': 90  # 分钟
        }
    
    def _calculate_group_diversity(
        self,
        members: List[Tuple[str, Dict]]
    ) -> float:
        """计算小组多样性"""
        if len(members) < 2:
            return 0
        
        diversity_scores = []
        for i in range(len(members)):
            for j in range(i + 1, len(members)):
                div = self._calculate_profile_diversity(members[i][1], members[j][1])
                diversity_scores.append(div)
        
        return np.mean(diversity_scores) if diversity_scores else 0
    
    def _estimate_synergy(
        self,
        members: List[Tuple[str, Dict]]
    ) -> float:
        """估计协同效应"""
        # 基于多样性和共同目标的协同估计
        diversity = self._calculate_group_diversity(members)
        
        # 适度多样性产生最佳协同
        optimal_diversity = 0.4
        synergy = 1 - abs(diversity - optimal_diversity) / optimal_diversity
        
        return max(0, min(1, synergy))
    
    def analyze_group_health(self, group_id: str) -> Dict[str, Any]:
        """
        分析小组健康度
        
        Returns:
            健康度分析报告
        """
        if group_id not in self.groups:
            return {'error': 'Group not found'}
        
        group = self.groups[group_id]
        interactions = self.group_interactions[group_id]
        
        # 计算各项指标
        participation = len(interactions) / max(len(group.members), 1)
        
        # 互动均衡性
        member_contributions = defaultdict(int)
        for interaction in interactions:
            member_contributions[interaction.get('user_id')] += 1
        
        if member_contributions:
            contributions = list(member_contributions.values())
            balance = 1 - np.std(contributions) / (np.mean(contributions) + 1e-8)
        else:
            balance = 0
        
        return {
            'group_id': group_id,
            'member_count': len(group.members),
            'activity_level': group.activity_level,
            'completion_rate': group.completion_rate,
            'participation_rate': participation,
            'contribution_balance': balance,
            'health_score': (
                group.activity_level * 0.3 +
                group.completion_rate * 0.3 +
                min(1, participation / 10) * 0.2 +
                balance * 0.2
            ),
            'recommendations': self._generate_group_recommendations(group, balance)
        }
    
    def _generate_group_recommendations(
        self,
        group: StudyGroup,
        balance: float
    ) -> List[str]:
        """生成小组改进建议"""
        recommendations = []
        
        if group.activity_level < 0.3:
            recommendations.append('小组活跃度较低，建议增加互动活动')
        
        if group.completion_rate < 0.5:
            recommendations.append('完成率有待提升，建议分解目标')
        
        if balance < 0.5:
            recommendations.append('成员参与度不均衡，鼓励 quieter 成员发言')
        
        if not recommendations:
            recommendations.append('小组运行良好，继续保持')
        
        return recommendations
