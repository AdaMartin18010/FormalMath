"""
同伴匹配系统
学习伙伴推荐、互补匹配、协同学习优化
"""
import numpy as np
from typing import Dict, List, Optional, Tuple, Set
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from collections import defaultdict
import heapq


@dataclass
class StudyPartnerProfile:
    """学习伙伴档案"""
    user_id: str
    
    # 学习属性
    knowledge_level: Dict[str, float] = field(default_factory=dict)
    learning_style: Dict[str, float] = field(default_factory=dict)
    study_hours: Dict[int, float] = field(default_factory=dict)  # 时段偏好
    
    # 社交属性
    collaboration_preference: float = 0.5  # 协作偏好
    communication_style: str = 'text'  # text, voice, video
    help_availability: float = 0.5  # 帮助意愿
    
    # 历史数据
    past_partners: List[str] = field(default_factory=list)
    ratings_given: Dict[str, float] = field(default_factory=dict)
    ratings_received: Dict[str, float] = field(default_factory=dict)
    
    def to_feature_vector(self) -> np.ndarray:
        """转换为特征向量"""
        # 知识水平平均
        avg_knowledge = np.mean(list(self.knowledge_level.values())) if self.knowledge_level else 0.5
        
        # 学习风格
        style_values = [
            self.learning_style.get('visual', 0.5),
            self.learning_style.get('active', 0.5),
            self.learning_style.get('sequential', 0.5)
        ]
        
        # 社交属性
        social = [
            self.collaboration_preference,
            self.help_availability
        ]
        
        return np.array([avg_knowledge] + style_values + social)


@dataclass
class MatchScore:
    """匹配分数"""
    user_a: str
    user_b: str
    overall_score: float
    component_scores: Dict[str, float]
    match_reasons: List[str]
    potential_challenges: List[str]


class PeerMatcher:
    """
    同伴匹配器
    
    基于多维度相似性和互补性进行匹配
    """
    
    def __init__(self):
        self.profiles: Dict[str, StudyPartnerProfile] = {}
        self.interaction_history: Dict[str, List[Dict]] = defaultdict(list)
        
        # 匹配权重配置
        self.weights = {
            'knowledge_complementarity': 0.25,
            'schedule_overlap': 0.20,
            'learning_style_compatibility': 0.20,
            'collaboration_fit': 0.15,
            'communication_match': 0.10,
            'historical_rating': 0.10
        }
    
    def add_profile(self, profile: StudyPartnerProfile):
        """添加用户档案"""
        self.profiles[profile.user_id] = profile
    
    def find_matches(
        self,
        user_id: str,
        purpose: str = 'study',  # study, project, mentorship
        top_k: int = 5,
        exclude_past: bool = True
    ) -> List[MatchScore]:
        """
        为指定用户寻找最佳匹配
        
        Args:
            user_id: 用户ID
            purpose: 匹配目的
            top_k: 返回数量
            exclude_past: 是否排除过去的伙伴
        
        Returns:
            匹配分数列表
        """
        if user_id not in self.profiles:
            return []
        
        user_profile = self.profiles[user_id]
        
        # 确定排除列表
        exclude_set = set()
        if exclude_past:
            exclude_set = set(user_profile.past_partners)
        exclude_set.add(user_id)
        
        # 计算与所有候选人的匹配分数
        scores = []
        for candidate_id, candidate_profile in self.profiles.items():
            if candidate_id in exclude_set:
                continue
            
            score = self._calculate_match_score(
                user_profile, candidate_profile, purpose
            )
            scores.append(score)
        
        # 排序并返回top-k
        scores.sort(key=lambda x: x.overall_score, reverse=True)
        return scores[:top_k]
    
    def _calculate_match_score(
        self,
        profile_a: StudyPartnerProfile,
        profile_b: StudyPartnerProfile,
        purpose: str
    ) -> MatchScore:
        """计算两个用户之间的匹配分数"""
        component_scores = {}
        reasons = []
        challenges = []
        
        # 1. 知识互补性
        knowledge_score = self._calculate_knowledge_complementarity(
            profile_a, profile_b
        )
        component_scores['knowledge_complementarity'] = knowledge_score
        
        if knowledge_score > 0.7:
            reasons.append('知识技能互补，可以互相学习')
        elif knowledge_score < 0.3:
            challenges.append('知识水平差异较大，可能需要协调进度')
        
        # 2. 时间重叠
        schedule_score = self._calculate_schedule_overlap(
            profile_a, profile_b
        )
        component_scores['schedule_overlap'] = schedule_score
        
        if schedule_score > 0.6:
            reasons.append('学习时间有较大重叠')
        else:
            challenges.append('时间安排差异较大')
        
        # 3. 学习风格兼容性
        style_score = self._calculate_learning_style_compatibility(
            profile_a, profile_b
        )
        component_scores['learning_style_compatibility'] = style_score
        
        if style_score > 0.7:
            reasons.append('学习风格相容')
        
        # 4. 协作适配
        collab_score = self._calculate_collaboration_fit(
            profile_a, profile_b
        )
        component_scores['collaboration_fit'] = collab_score
        
        # 5. 沟通方式匹配
        comm_score = self._calculate_communication_match(
            profile_a, profile_b
        )
        component_scores['communication_match'] = comm_score
        
        if comm_score > 0.7:
            reasons.append('沟通偏好一致')
        
        # 6. 历史评分
        historical_score = self._calculate_historical_rating(
            profile_a, profile_b
        )
        component_scores['historical_rating'] = historical_score
        
        # 根据目的调整权重
        purpose_weights = self._get_purpose_weights(purpose)
        
        # 计算综合分数
        overall = sum(
            component_scores.get(key, 0) * purpose_weights.get(key, weight)
            for key, weight in self.weights.items()
        )
        
        return MatchScore(
            user_a=profile_a.user_id,
            user_b=profile_b.user_id,
            overall_score=overall,
            component_scores=component_scores,
            match_reasons=reasons,
            potential_challenges=challenges
        )
    
    def _calculate_knowledge_complementarity(
        self,
        a: StudyPartnerProfile,
        b: StudyPartnerProfile
    ) -> float:
        """计算知识互补性"""
        # 获取共同的概念
        common_concepts = set(a.knowledge_level.keys()) & set(b.knowledge_level.keys())
        
        if not common_concepts:
            # 无共同知识领域，使用总体水平
            a_avg = np.mean(list(a.knowledge_level.values())) if a.knowledge_level else 0.5
            b_avg = np.mean(list(b.knowledge_level.values())) if b.knowledge_level else 0.5
            # 适度差异产生互补
            diff = abs(a_avg - b_avg)
            return 1 - abs(diff - 0.3)  # 最佳差异约0.3
        
        # 计算互补性：一个人强的地方另一个人弱，反之亦然
        complementarity_scores = []
        for concept in common_concepts:
            a_level = a.knowledge_level[concept]
            b_level = b.knowledge_level[concept]
            
            # 差异适中最佳
            diff = abs(a_level - b_level)
            score = 1 - abs(diff - 0.3)  # 最佳差异0.3
            complementarity_scores.append(score)
        
        return np.mean(complementarity_scores) if complementarity_scores else 0.5
    
    def _calculate_schedule_overlap(
        self,
        a: StudyPartnerProfile,
        b: StudyPartnerProfile
    ) -> float:
        """计算学习时间重叠"""
        if not a.study_hours or not b.study_hours:
            return 0.5
        
        # 计算小时级别的重叠
        overlap_sum = 0
        a_sum = 0
        b_sum = 0
        
        for hour in range(24):
            a_avail = a.study_hours.get(hour, 0)
            b_avail = b.study_hours.get(hour, 0)
            
            overlap_sum += min(a_avail, b_avail)
            a_sum += a_avail
            b_sum += b_avail
        
        # Jaccard-like overlap
        if a_sum + b_sum == 0:
            return 0.5
        
        return 2 * overlap_sum / (a_sum + b_sum)
    
    def _calculate_learning_style_compatibility(
        self,
        a: StudyPartnerProfile,
        b: StudyPartnerProfile
    ) -> float:
        """计算学习风格兼容性"""
        if not a.learning_style or not b.learning_style:
            return 0.5
        
        # 计算各维度相似度
        dimensions = ['visual', 'verbal', 'active', 'reflective', 'sequential', 'global']
        similarities = []
        
        for dim in dimensions:
            a_val = a.learning_style.get(dim, 0.5)
            b_val = b.learning_style.get(dim, 0.5)
            similarities.append(1 - abs(a_val - b_val))
        
        return np.mean(similarities)
    
    def _calculate_collaboration_fit(
        self,
        a: StudyPartnerProfile,
        b: StudyPartnerProfile
    ) -> float:
        """计算协作适配度"""
        # 双方都有协作意愿才好
        min_collab = min(a.collaboration_preference, b.collaboration_preference)
        max_collab = max(a.collaboration_preference, b.collaboration_preference)
        
        # 偏好接近且都高最好
        similarity = 1 - abs(a.collaboration_preference - b.collaboration_preference)
        
        return 0.6 * min_collab + 0.4 * similarity
    
    def _calculate_communication_match(
        self,
        a: StudyPartnerProfile,
        b: StudyPartnerProfile
    ) -> float:
        """计算沟通方式匹配"""
        # 定义沟通方式的亲密度等级
        levels = {'text': 1, 'voice': 2, 'video': 3}
        
        a_level = levels.get(a.communication_style, 1)
        b_level = levels.get(b.communication_style, 1)
        
        # 相同最好，差异小也能接受
        diff = abs(a_level - b_level)
        return max(0, 1 - diff * 0.3)
    
    def _calculate_historical_rating(
        self,
        a: StudyPartnerProfile,
        b: StudyPartnerProfile
    ) -> float:
        """计算历史评分"""
        # 检查双方是否合作过
        if b.user_id in a.ratings_given:
            return a.ratings_given[b.user_id]
        
        # 检查间接评价（共同伙伴的评价）
        common_partners = set(a.past_partners) & set(b.past_partners)
        if common_partners:
            ratings = []
            for partner in common_partners:
                if partner in a.ratings_given and partner in b.ratings_received:
                    ratings.append(a.ratings_given[partner])
                if partner in b.ratings_given and partner in a.ratings_received:
                    ratings.append(b.ratings_given[partner])
            
            if ratings:
                return np.mean(ratings)
        
        return 0.5  # 默认中性
    
    def _get_purpose_weights(self, purpose: str) -> Dict[str, float]:
        """根据匹配目的获取权重"""
        weights = {
            'study': {
                'knowledge_complementarity': 0.30,
                'schedule_overlap': 0.25,
                'learning_style_compatibility': 0.20,
                'collaboration_fit': 0.15,
                'communication_match': 0.05,
                'historical_rating': 0.05
            },
            'project': {
                'knowledge_complementarity': 0.35,
                'schedule_overlap': 0.20,
                'learning_style_compatibility': 0.10,
                'collaboration_fit': 0.25,
                'communication_match': 0.05,
                'historical_rating': 0.05
            },
            'mentorship': {
                'knowledge_complementarity': 0.40,
                'schedule_overlap': 0.15,
                'learning_style_compatibility': 0.15,
                'collaboration_fit': 0.10,
                'communication_match': 0.10,
                'historical_rating': 0.10
            }
        }
        
        return weights.get(purpose, self.weights)
    
    def create_study_pair(
        self,
        user_a: str,
        user_b: str,
        study_goal: str,
        duration_weeks: int = 4
    ) -> Dict[str, Any]:
        """
        创建学习对
        
        Args:
            user_a: 用户A
            user_b: 用户B
            study_goal: 学习目标
            duration_weeks: 持续周数
        
        Returns:
            学习对配置
        """
        if user_a not in self.profiles or user_b not in self.profiles:
            return {'error': 'User profiles not found'}
        
        profile_a = self.profiles[user_a]
        profile_b = self.profiles[user_b]
        
        # 分析匹配特点
        match_analysis = self._analyze_pair_strengths(profile_a, profile_b)
        
        # 生成建议
        recommendations = self._generate_pair_recommendations(
            profile_a, profile_b, study_goal
        )
        
        return {
            'pair_id': f'{user_a}_{user_b}_{int(datetime.utcnow().timestamp())}',
            'members': [user_a, user_b],
            'study_goal': study_goal,
            'duration_weeks': duration_weeks,
            'match_analysis': match_analysis,
            'recommendations': recommendations,
            'suggested_schedule': self._suggest_pair_schedule(profile_a, profile_b),
            'created_at': datetime.utcnow().isoformat()
        }
    
    def _analyze_pair_strengths(
        self,
        a: StudyPartnerProfile,
        b: StudyPartnerProfile
    ) -> Dict[str, Any]:
        """分析配对优势"""
        strengths = []
        
        # 知识互补
        a_stronger = []
        b_stronger = []
        
        for concept in set(a.knowledge_level.keys()) | set(b.knowledge_level.keys()):
            a_level = a.knowledge_level.get(concept, 0)
            b_level = b.knowledge_level.get(concept, 0)
            
            if a_level > b_level + 0.2:
                a_stronger.append(concept)
            elif b_level > a_level + 0.2:
                b_stronger.append(concept)
        
        if a_stronger or b_stronger:
            strengths.append({
                'type': 'knowledge_complementarity',
                'description': f'{a.user_id} 擅长: {a_stronger}, {b.user_id} 擅长: {b_stronger}'
            })
        
        # 学习风格互补
        if a.learning_style and b.learning_style:
            if a.learning_style.get('active', 0.5) > 0.6 and b.learning_style.get('reflective', 0.5) > 0.6:
                strengths.append({
                    'type': 'style_complementarity',
                    'description': f'{a.user_id} 更主动，{b.user_id} 更反思，可形成良好互补'
                })
        
        return {
            'strengths': strengths,
            'a_can_help': b_stronger,
            'b_can_help': a_stronger
        }
    
    def _generate_pair_recommendations(
        self,
        a: StudyPartnerProfile,
        b: StudyPartnerProfile,
        goal: str
    ) -> List[str]:
        """生成配对建议"""
        recommendations = []
        
        # 基于目标的建议
        if goal == 'exam_preparation':
            recommendations.extend([
                '制定共同的复习计划',
                '互相出题测试',
                '分享错题和易错点'
            ])
        elif goal == 'project_based':
            recommendations.extend([
                '明确分工和责任',
                '定期同步进度',
                '使用协作工具'
            ])
        elif goal == 'skill_building':
                recommendations.extend([
                '轮流教授各自擅长的部分',
                '共同完成练习',
                '讨论疑难点'
            ])
        
        # 个性化建议
        if a.help_availability > 0.7 and b.help_availability > 0.7:
            recommendations.append('双方都有较强的帮助意愿，建议采用轮流主导的学习模式')
        
        return recommendations
    
    def _suggest_pair_schedule(
        self,
        a: StudyPartnerProfile,
        b: StudyPartnerProfile
    ) -> Dict[str, Any]:
        """建议配对学习时间"""
        # 找出最佳重叠时间
        best_hours = []
        
        for hour in range(24):
            overlap = min(
                a.study_hours.get(hour, 0),
                b.study_hours.get(hour, 0)
            )
            best_hours.append((hour, overlap))
        
        best_hours.sort(key=lambda x: x[1], reverse=True)
        
        return {
            'best_time_slots': [
                f'{h:02d}:00-{h+1:02d}:00' for h, _ in best_hours[:3]
            ],
            'recommended_session_length': 60,  # 分钟
            'recommended_frequency': '每周2-3次'
        }
    
    def record_interaction(
        self,
        user_a: str,
        user_b: str,
        interaction_type: str,
        outcome: Dict[str, Any]
    ):
        """记录配对交互"""
        interaction = {
            'timestamp': datetime.utcnow().isoformat(),
            'partner': user_b,
            'type': interaction_type,
            'outcome': outcome
        }
        
        self.interaction_history[user_a].append(interaction)
        
        # 更新评分
        if 'rating' in outcome:
            if user_a in self.profiles:
                self.profiles[user_a].ratings_given[user_b] = outcome['rating']
            if user_b in self.profiles:
                self.profiles[user_b].ratings_received[user_a] = outcome['rating']
    
    def get_match_statistics(self, user_id: str) -> Dict[str, Any]:
        """获取用户匹配统计"""
        if user_id not in self.profiles:
            return {}
        
        profile = self.profiles[user_id]
        interactions = self.interaction_history[user_id]
        
        return {
            'total_partners': len(profile.past_partners),
            'average_rating_given': np.mean(list(profile.ratings_given.values())) if profile.ratings_given else None,
            'average_rating_received': np.mean(list(profile.ratings_received.values())) if profile.ratings_received else None,
            'total_interactions': len(interactions),
            'recent_matches': [
                {
                    'partner': i['partner'],
                    'type': i['type'],
                    'timestamp': i['timestamp']
                }
                for i in interactions[-5:]
            ]
        }
