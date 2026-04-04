"""
内容推荐系统
- 基于概念相似度
- 难度自适应
- 学习风格匹配
"""
import numpy as np
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass
from enum import Enum
from sqlalchemy.orm import Session
from collections import defaultdict
import logging
from datetime import datetime, timedelta

from ..models.models import (
    User, UserProgress, UserActivity, 
    KnowledgeGraphNode, ConceptDifficulty
)

logger = logging.getLogger(__name__)


class LearningStyle(Enum):
    """学习风格类型"""
    VISUAL = "visual"           # 视觉型
    AUDITORY = "auditory"       # 听觉型
    READING = "reading"         # 阅读型
    KINESTHETIC = "kinesthetic" # 动觉型
    LOGICAL = "logical"         # 逻辑型
    SOCIAL = "social"           # 社交型
    SOLITARY = "solitary"       # 独立型


@dataclass
class UserProfile:
    """用户画像"""
    user_id: int
    learning_style: Dict[LearningStyle, float] = None
    preferred_difficulty: str = "intermediate"
    avg_study_session: int = 30  # 分钟
    preferred_branches: List[str] = None
    weak_areas: List[str] = None
    strong_areas: List[str] = None
    
    def __post_init__(self):
        if self.learning_style is None:
            self.learning_style = {style: 0.0 for style in LearningStyle}
        if self.preferred_branches is None:
            self.preferred_branches = []
        if self.weak_areas is None:
            self.weak_areas = []
        if self.strong_areas is None:
            self.strong_areas = []


class ContentRecommender:
    """内容推荐器"""
    
    def __init__(self, db: Session):
        self.db = db
        self.user_profiles: Dict[int, UserProfile] = {}
        self.concept_features = {}
        self.concept_similarity_cache = {}
        
    def analyze_user_profile(self, user_id: int) -> UserProfile:
        """
        分析用户画像
        
        分析维度：
        1. 学习风格偏好
        2. 难度偏好
        3. 学习时间模式
        4. 强弱领域
        """
        # 获取用户活动记录
        activities = self.db.query(UserActivity).filter(
            UserActivity.user_id == user_id
        ).order_by(UserActivity.created_at.desc()).all()
        
        # 初始化学习风格分数
        style_scores = defaultdict(float)
        style_counts = defaultdict(int)
        
        # 分析活动类型推断学习风格
        for activity in activities:
            metadata = activity.metadata or {}
            
            if activity.activity_type == "watch_video":
                style_scores[LearningStyle.VISUAL] += 1
                style_scores[LearningStyle.AUDITORY] += 0.5
            elif activity.activity_type == "read_material":
                style_scores[LearningStyle.READING] += 1
            elif activity.activity_type == "practice_exercise":
                style_scores[LearningStyle.KINESTHETIC] += 1
                style_scores[LearningStyle.LOGICAL] += 0.5
            elif activity.activity_type == "discussion":
                style_scores[LearningStyle.SOCIAL] += 1
            elif activity.activity_type == "self_study":
                style_scores[LearningStyle.SOLITARY] += 1
        
        # 归一化学习风格分数
        total = sum(style_scores.values()) or 1
        learning_style = {
            style: style_scores[style] / total 
            for style in LearningStyle
        }
        
        # 分析难度偏好
        progress = self.db.query(UserProgress).filter(
            UserProgress.user_id == user_id
        ).all()
        
        difficulty_scores = defaultdict(float)
        for p in progress:
            concept = self.db.query(KnowledgeGraphNode).filter(
                KnowledgeGraphNode.id == p.concept_id
            ).first()
            if concept:
                # 高掌握程度的高难度概念说明用户喜欢挑战
                weight = p.mastery_level * (1 if p.mastery_level > 0.7 else -0.5)
                difficulty_scores[concept.difficulty.value] += weight
        
        preferred_difficulty = max(
            difficulty_scores, 
            key=difficulty_scores.get
        ) if difficulty_scores else "intermediate"
        
        # 分析学习时间
        if progress:
            avg_time = np.mean([p.study_time for p in progress])
        else:
            avg_time = 30
        
        # 分析强弱领域
        branch_performance = defaultdict(lambda: {"total": 0, "mastery": 0})
        for p in progress:
            concept = self.db.query(KnowledgeGraphNode).filter(
                KnowledgeGraphNode.id == p.concept_id
            ).first()
            if concept:
                branch_performance[concept.branch]["total"] += 1
                branch_performance[concept.branch]["mastery"] += p.mastery_level
        
        weak_areas = []
        strong_areas = []
        preferred_branches = []
        
        for branch, stats in branch_performance.items():
            avg_mastery = stats["mastery"] / stats["total"] if stats["total"] > 0 else 0
            preferred_branches.append(branch)
            
            if avg_mastery < 0.5:
                weak_areas.append(branch)
            elif avg_mastery > 0.8:
                strong_areas.append(branch)
        
        profile = UserProfile(
            user_id=user_id,
            learning_style=learning_style,
            preferred_difficulty=preferred_difficulty,
            avg_study_session=int(avg_time),
            preferred_branches=preferred_branches,
            weak_areas=weak_areas,
            strong_areas=strong_areas
        )
        
        self.user_profiles[user_id] = profile
        return profile
    
    def get_concept_features(self, concept_id: str) -> Optional[np.ndarray]:
        """获取概念的特征向量"""
        if concept_id in self.concept_features:
            return self.concept_features[concept_id]
        
        concept = self.db.query(KnowledgeGraphNode).filter(
            KnowledgeGraphNode.id == concept_id
        ).first()
        
        if not concept:
            return None
        
        # 构建特征向量
        # [难度, 前置概念数, 出度, 入度, 学习人数, 平均掌握度]
        difficulty_map = {"basic": 0, "intermediate": 0.33, "advanced": 0.67, "research": 1.0}
        difficulty = difficulty_map.get(concept.difficulty.value, 0.5)
        
        prereq_count = len(concept.prerequisites) if concept.prerequisites else 0
        
        # 统计学习数据
        progress_stats = self.db.query(UserProgress).filter(
            UserProgress.concept_id == concept_id
        ).all()
        
        learner_count = len(progress_stats)
        avg_mastery = np.mean([p.mastery_level for p in progress_stats]) if progress_stats else 0.5
        
        features = np.array([
            difficulty,
            prereq_count / 10.0,
            learner_count / 100.0,
            avg_mastery
        ])
        
        self.concept_features[concept_id] = features
        return features
    
    def compute_concept_similarity(self, concept_id1: str, concept_id2: str) -> float:
        """计算两个概念的内容相似度"""
        cache_key = tuple(sorted([concept_id1, concept_id2]))
        if cache_key in self.concept_similarity_cache:
            return self.concept_similarity_cache[cache_key]
        
        # 特征相似度
        feat1 = self.get_concept_features(concept_id1)
        feat2 = self.get_concept_features(concept_id2)
        
        if feat1 is None or feat2 is None:
            return 0.0
        
        # 余弦相似度
        similarity = np.dot(feat1, feat2) / (np.linalg.norm(feat1) * np.linalg.norm(feat2) + 1e-8)
        
        # 检查是否在同一分支
        concept1 = self.db.query(KnowledgeGraphNode).filter(
            KnowledgeGraphNode.id == concept_id1
        ).first()
        concept2 = self.db.query(KnowledgeGraphNode).filter(
            KnowledgeGraphNode.id == concept_id2
        ).first()
        
        if concept1 and concept2 and concept1.branch == concept2.branch:
            similarity += 0.2  # 同分支加分
        
        # 检查前置关系
        if concept1 and concept2:
            if concept_id2 in (concept1.prerequisites or []):
                similarity += 0.3  # 是前置概念
            if concept_id1 in (concept2.prerequisites or []):
                similarity += 0.3  # 是后续概念
        
        self.concept_similarity_cache[cache_key] = min(similarity, 1.0)
        return min(similarity, 1.0)
    
    def adaptive_difficulty_recommend(
        self,
        user_id: int,
        n_recommendations: int = 10
    ) -> List[Dict[str, Any]]:
        """
        难度自适应推荐
        
        策略：
        1. 分析用户当前能力水平
        2. 推荐适当难度（挑战+1级）的概念
        3. 避免过难或过易的内容
        """
        profile = self.user_profiles.get(user_id) or self.analyze_user_profile(user_id)
        
        # 获取用户当前掌握的概念
        progress = self.db.query(UserProgress).filter(
            UserProgress.user_id == user_id
        ).all()
        
        studied_concepts = {p.concept_id for p in progress}
        
        # 计算用户平均掌握程度
        avg_mastery = np.mean([p.mastery_level for p in progress]) if progress else 0.5
        
        # 确定推荐难度
        difficulty_order = ["basic", "intermediate", "advanced", "research"]
        current_difficulty_idx = difficulty_order.index(profile.preferred_difficulty) \
            if profile.preferred_difficulty in difficulty_order else 1
        
        # 根据掌握程度调整
        if avg_mastery > 0.8 and current_difficulty_idx < 3:
            target_difficulty = difficulty_order[current_difficulty_idx + 1]
        elif avg_mastery < 0.4 and current_difficulty_idx > 0:
            target_difficulty = difficulty_order[current_difficulty_idx - 1]
        else:
            target_difficulty = difficulty_order[current_difficulty_idx]
        
        # 查询目标难度的概念
        candidates = self.db.query(KnowledgeGraphNode).filter(
            KnowledgeGraphNode.difficulty == target_difficulty,
            ~KnowledgeGraphNode.id.in_(studied_concepts) if studied_concepts else True
        ).limit(n_recommendations * 2).all()
        
        # 评分并排序
        scored_candidates = []
        for concept in candidates:
            score = 0.5  # 基础分
            
            # 偏好分支加分
            if concept.branch in profile.preferred_branches:
                score += 0.2
            
            # 弱领域加分（帮助提升）
            if concept.branch in profile.weak_areas:
                score += 0.15
            
            # 检查前置条件满足度
            if concept.prerequisites:
                prereqs_met = sum(
                    1 for p in concept.prerequisites 
                    if p in studied_concepts
                )
                prereq_ratio = prereqs_met / len(concept.prerequisites)
                score += prereq_ratio * 0.15
            
            scored_candidates.append((concept, score))
        
        scored_candidates.sort(key=lambda x: x[1], reverse=True)
        
        recommendations = []
        for concept, score in scored_candidates[:n_recommendations]:
            recommendations.append({
                "concept_id": concept.id,
                "name": concept.name,
                "branch": concept.branch,
                "difficulty": concept.difficulty.value,
                "score": float(score),
                "reason": f"难度自适应推荐: {target_difficulty}级别，匹配您的学习进度"
            })
        
        return recommendations
    
    def learning_style_match_recommend(
        self,
        user_id: int,
        n_recommendations: int = 10
    ) -> List[Dict[str, Any]]:
        """
        基于学习风格的推荐
        
        匹配学习资源和概念呈现方式
        """
        profile = self.user_profiles.get(user_id) or self.analyze_user_profile(user_id)
        
        # 确定主导学习风格
        dominant_style = max(profile.learning_style, key=profile.learning_style.get)
        
        # 获取用户进度
        progress = self.db.query(UserProgress).filter(
            UserProgress.user_id == user_id
        ).all()
        studied_concepts = {p.concept_id for p in progress}
        
        # 根据学习风格选择概念类型
        style_branch_mapping = {
            LearningStyle.VISUAL: ["geometry", "topology"],
            LearningStyle.LOGICAL: ["algebra", "logic", "number_theory"],
            LearningStyle.READING: ["history", "foundations"],
            LearningStyle.KINESTHETIC: ["applied_math", "computation"],
        }
        
        preferred_branches = style_branch_mapping.get(dominant_style, [])
        
        # 查询候选概念
        if preferred_branches:
            candidates = self.db.query(KnowledgeGraphNode).filter(
                KnowledgeGraphNode.branch.in_(preferred_branches),
                ~KnowledgeGraphNode.id.in_(studied_concepts) if studied_concepts else True
            ).limit(n_recommendations * 2).all()
        else:
            candidates = self.db.query(KnowledgeGraphNode).filter(
                ~KnowledgeGraphNode.id.in_(studied_concepts) if studied_concepts else True
            ).limit(n_recommendations * 2).all()
        
        recommendations = []
        for concept in candidates[:n_recommendations]:
            match_score = profile.learning_style[dominant_style]
            
            recommendations.append({
                "concept_id": concept.id,
                "name": concept.name,
                "branch": concept.branch,
                "score": float(match_score),
                "reason": f"基于您的{dominant_style.value}型学习风格推荐"
            })
        
        return recommendations
    
    def similar_content_recommend(
        self,
        user_id: int,
        n_recommendations: int = 10
    ) -> List[Dict[str, Any]]:
        """
        基于内容相似度的推荐
        
        推荐与用户已学习内容相似的新概念
        """
        # 获取用户喜欢的概念（高掌握度）
        liked_concepts = self.db.query(UserProgress).filter(
            UserProgress.user_id == user_id,
            UserProgress.mastery_level > 0.7
        ).all()
        
        if not liked_concepts:
            # 没有高掌握度概念，使用最近学习的
            liked_concepts = self.db.query(UserProgress).filter(
                UserProgress.user_id == user_id
            ).order_by(UserProgress.last_studied_at.desc()).limit(5).all()
        
        if not liked_concepts:
            return []
        
        # 获取所有未学习概念
        studied_ids = {p.concept_id for p in self.db.query(UserProgress).filter(
            UserProgress.user_id == user_id
        ).all()}
        
        all_concepts = self.db.query(KnowledgeGraphNode).filter(
            ~KnowledgeGraphNode.id.in_(studied_ids) if studied_ids else True
        ).all()
        
        # 计算相似度
        concept_scores = defaultdict(float)
        
        for liked in liked_concepts:
            for candidate in all_concepts:
                sim = self.compute_concept_similarity(liked.concept_id, candidate.id)
                # 加权：掌握程度越高权重越大
                weight = liked.mastery_level
                concept_scores[candidate.id] += sim * weight
        
        # 排序并返回
        sorted_concepts = sorted(concept_scores.items(), key=lambda x: x[1], reverse=True)
        
        recommendations = []
        for concept_id, score in sorted_concepts[:n_recommendations]:
            concept = self.db.query(KnowledgeGraphNode).filter(
                KnowledgeGraphNode.id == concept_id
            ).first()
            if concept:
                recommendations.append({
                    "concept_id": concept_id,
                    "name": concept.name,
                    "branch": concept.branch,
                    "score": float(score),
                    "reason": "基于您已掌握内容的相似度推荐"
                })
        
        return recommendations
    
    def recommend(
        self,
        user_id: int,
        n_recommendations: int = 10,
        strategy: str = "adaptive"
    ) -> List[Dict[str, Any]]:
        """
        内容推荐主接口
        
        Args:
            user_id: 用户ID
            n_recommendations: 推荐数量
            strategy: 推荐策略 (adaptive/style/similar/hybrid)
        """
        if strategy == "adaptive":
            return self.adaptive_difficulty_recommend(user_id, n_recommendations)
        elif strategy == "style":
            return self.learning_style_match_recommend(user_id, n_recommendations)
        elif strategy == "similar":
            return self.similar_content_recommend(user_id, n_recommendations)
        elif strategy == "hybrid":
            # 混合策略
            adaptive = self.adaptive_difficulty_recommend(user_id, n_recommendations // 2)
            similar = self.similar_content_recommend(user_id, n_recommendations // 2)
            return adaptive + similar
        else:
            return self.adaptive_difficulty_recommend(user_id, n_recommendations)
