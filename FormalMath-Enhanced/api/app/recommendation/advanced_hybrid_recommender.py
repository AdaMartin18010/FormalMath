"""
高级混合推荐系统 v2.0
=====================================
核心特性:
1. 动态权重调整 - 基于实时反馈的自适应权重优化
2. 反馈学习机制 - 多维度反馈收集与在线学习
3. 冷启动优化 - 多层次冷启动处理策略
4. 多样性算法 - MMR与重新排序确保多样性
5. 可解释性输出 - 详细的推荐理由与透明度报告

Author: AI Recommendation System
Version: 2.0.0
"""

import numpy as np
import logging
from typing import Dict, List, Optional, Tuple, Any, Set
from dataclasses import dataclass, field
from enum import Enum
from collections import defaultdict
from datetime import datetime, timedelta
from abc import ABC, abstractmethod
import hashlib
import json

from sqlalchemy.orm import Session
from sklearn.preprocessing import normalize

# 导入现有推荐器
from .collaborative_filtering import CollaborativeFiltering
from .knowledge_embedding import KnowledgeGraphEmbedding
from .rl_recommendation import RLRecommender
from .content_recommendation import ContentRecommender

logger = logging.getLogger(__name__)


# ============================================================================
# 枚举与常量定义
# ============================================================================

class RecommenderType(Enum):
    """推荐器类型枚举"""
    COLLABORATIVE = "collaborative"
    KNOWLEDGE_GRAPH = "knowledge_graph"
    REINFORCEMENT_LEARNING = "reinforcement_learning"
    CONTENT = "content"
    POPULARITY = "popularity"


class UserAction(Enum):
    """用户行为类型"""
    CLICK = "click"
    COMPLETE = "complete"
    SKIP = "skip"
    DISMISS = "dismiss"
    BOOKMARK = "bookmark"
    SHARE = "share"
    RATE = "rate"
    TIME_SPENT = "time_spent"


class ColdStartLevel(Enum):
    """冷启动等级"""
    NEW_USER = "new_user"           # 完全新用户
    INTEREST_KNOWN = "interest_known"  # 已知兴趣
    SOME_ACTIVITY = "some_activity"    # 有一些活动
    WARM_USER = "warm_user"           # 接近正常用户


# ============================================================================
# 数据类定义
# ============================================================================

@dataclass
class UserFeedback:
    """用户反馈数据类"""
    user_id: int
    concept_id: str
    action: UserAction
    timestamp: datetime = field(default_factory=datetime.utcnow)
    rating: Optional[float] = None
    context: Dict[str, Any] = field(default_factory=dict)
    metadata: Dict[str, Any] = field(default_factory=dict)


@dataclass
class RecommendationItem:
    """推荐项数据类"""
    concept_id: str
    name: str
    branch: str
    difficulty: str
    final_score: float
    component_scores: Dict[str, float] = field(default_factory=dict)
    explanation: Dict[str, Any] = field(default_factory=dict)
    confidence: float = 0.0
    diversity_score: float = 0.0
    novelty_score: float = 0.0
    
    def to_dict(self) -> Dict[str, Any]:
        """转换为字典格式"""
        return {
            "concept_id": self.concept_id,
            "name": self.name,
            "branch": self.branch,
            "difficulty": self.difficulty,
            "final_score": float(self.final_score),
            "component_scores": self.component_scores,
            "explanation": self.explanation,
            "confidence": float(self.confidence),
            "diversity_score": float(self.diversity_score),
            "novelty_score": float(self.novelty_score)
        }


@dataclass
class ExplanationReport:
    """可解释性报告"""
    primary_reason: str
    contributing_factors: List[str]
    algorithm_breakdown: Dict[str, Any]
    user_profile_match: Dict[str, float]
    confidence_explanation: str
    alternative_recommendations: List[str]


# ============================================================================
# 动态权重调整模块
# ============================================================================

class DynamicWeightAdjuster:
    """
    动态权重调整器
    
    使用在线梯度下降和反馈驱动的方式动态调整各推荐器的权重。
    支持用户级和全局两种级别的权重调整。
    """
    
    def __init__(
        self,
        learning_rate: float = 0.05,
        min_weight: float = 0.05,
        max_weight: float = 0.6,
        momentum: float = 0.9,
        regularization: float = 0.01
    ):
        self.learning_rate = learning_rate
        self.min_weight = min_weight
        self.max_weight = max_weight
        self.momentum = momentum
        self.regularization = regularization
        
        # 全局权重历史
        self.global_weights: Dict[RecommenderType, float] = self._init_weights()
        self.weight_history: List[Dict[str, float]] = []
        
        # 用户级权重
        self.user_weights: Dict[int, Dict[RecommenderType, float]] = {}
        
        # 性能追踪
        self.performance_history: Dict[RecommenderType, List[float]] = defaultdict(list)
        self.velocity: Dict[RecommenderType, float] = {rt: 0.0 for rt in RecommenderType}
        
        # 反馈缓冲
        self.feedback_buffer: List[Tuple[UserFeedback, Dict[str, float]]] = []
        self.batch_size = 20
    
    def _init_weights(self) -> Dict[RecommenderType, float]:
        """初始化均衡权重"""
        weights = {rt: 0.2 for rt in RecommenderType}
        return weights
    
    def get_weights(
        self,
        user_id: Optional[int] = None,
        context: Optional[Dict[str, Any]] = None
    ) -> Dict[RecommenderType, float]:
        """
        获取当前权重
        
        Args:
            user_id: 用户ID（可选，用于个性化权重）
            context: 上下文信息（可选，用于上下文感知权重）
        
        Returns:
            权重字典
        """
        if user_id and user_id in self.user_weights:
            # 合并全局权重和用户权重
            user_w = self.user_weights[user_id].copy()
            global_w = self.global_weights
            
            # 加权融合
            fused_weights = {}
            for rt in RecommenderType:
                fused_weights[rt] = 0.7 * user_w.get(rt, 0.2) + 0.3 * global_w.get(rt, 0.2)
            
            return self._normalize_weights(fused_weights)
        
        # 上下文感知权重调整
        if context:
            return self._context_aware_weights(self.global_weights.copy(), context)
        
        return self.global_weights.copy()
    
    def _context_aware_weights(
        self,
        weights: Dict[RecommenderType, float],
        context: Dict[str, Any]
    ) -> Dict[RecommenderType, float]:
        """基于上下文调整权重"""
        # 新用户提升内容推荐权重
        if context.get("is_new_user", False):
            weights[RecommenderType.CONTENT] *= 1.5
            weights[RecommenderType.POPULARITY] *= 1.3
            weights[RecommenderType.COLLABORATIVE] *= 0.5
        
        # 有明确学习目标时提升知识图谱权重
        if context.get("has_learning_goal", False):
            weights[RecommenderType.KNOWLEDGE_GRAPH] *= 1.4
        
        # 探索模式下提升RL权重
        if context.get("exploration_mode", False):
            weights[RecommenderType.REINFORCEMENT_LEARNING] *= 1.3
        
        return self._normalize_weights(weights)
    
    def record_feedback(
        self,
        feedback: UserFeedback,
        component_contributions: Dict[str, float]
    ):
        """
        记录用户反馈
        
        Args:
            feedback: 用户反馈对象
            component_contributions: 各推荐器对该推荐的贡献度
        """
        self.feedback_buffer.append((feedback, component_contributions))
        
        # 批量处理
        if len(self.feedback_buffer) >= self.batch_size:
            self._process_feedback_batch()
    
    def _process_feedback_batch(self):
        """批量处理反馈并更新权重"""
        if not self.feedback_buffer:
            return
        
        # 计算各推荐器的性能信号
        performance_signals: Dict[RecommenderType, List[float]] = defaultdict(list)
        
        for feedback, contributions in self.feedback_buffer:
            # 将用户行为转换为反馈信号
            signal = self._action_to_signal(feedback.action, feedback.rating)
            
            # 归因到各推荐器
            for component, contribution in contributions.items():
                try:
                    if component == "collaborative":
                        rec_type = RecommenderType.COLLABORATIVE
                    elif component == "knowledge_graph":
                        rec_type = RecommenderType.KNOWLEDGE_GRAPH
                    elif component == "rl":
                        rec_type = RecommenderType.REINFORCEMENT_LEARNING
                    elif component == "content":
                        rec_type = RecommenderType.CONTENT
                    else:
                        continue
                    
                    # 按贡献度加权
                    weighted_signal = signal * contribution
                    performance_signals[rec_type].append(weighted_signal)
                    
                    # 记录到用户级
                    if feedback.user_id:
                        self._update_user_performance(feedback.user_id, rec_type, weighted_signal)
                
                except Exception:
                    continue
        
        # 更新全局权重
        self._update_global_weights(performance_signals)
        
        # 清空缓冲
        self.feedback_buffer = []
        
        logger.info(f"权重已更新: {self._weights_to_dict(self.global_weights)}")
    
    def _action_to_signal(self, action: UserAction, rating: Optional[float]) -> float:
        """将用户行为转换为信号值 [-1, 1]"""
        action_signals = {
            UserAction.COMPLETE: 1.0,
            UserAction.BOOKMARK: 0.8,
            UserAction.SHARE: 0.9,
            UserAction.CLICK: 0.3,
            UserAction.TIME_SPENT: 0.4,
            UserAction.RATE: 0.0,  # 依赖具体评分
            UserAction.DISMISS: -0.4,
            UserAction.SKIP: -0.6,
        }
        
        base_signal = action_signals.get(action, 0.0)
        
        # 如果有显式评分，融合到信号中
        if rating is not None:
            # 将评分 [0, 5] 转换到 [-1, 1]
            rating_signal = (rating - 2.5) / 2.5
            base_signal = 0.6 * base_signal + 0.4 * rating_signal
        
        return np.clip(base_signal, -1.0, 1.0)
    
    def _update_user_performance(
        self,
        user_id: int,
        rec_type: RecommenderType,
        signal: float
    ):
        """更新用户级性能历史"""
        if user_id not in self.user_weights:
            self.user_weights[user_id] = self.global_weights.copy()
        
        # 初始化用户性能历史
        if not hasattr(self, '_user_performance'):
            self._user_performance: Dict[int, Dict[RecommenderType, List[float]]] = defaultdict(
                lambda: defaultdict(list)
            )
        
        self._user_performance[user_id][rec_type].append(signal)
        
        # 只保留最近50条
        if len(self._user_performance[user_id][rec_type]) > 50:
            self._user_performance[user_id][rec_type] = self._user_performance[user_id][rec_type][-50:]
    
    def _update_global_weights(
        self,
        performance_signals: Dict[RecommenderType, List[float]]
    ):
        """使用动量梯度下降更新全局权重"""
        if not performance_signals:
            return
        
        # 计算各推荐器的平均性能
        avg_performance = {}
        for rec_type in RecommenderType:
            signals = performance_signals.get(rec_type, [0.0])
            # 使用最近20条，指数加权
            recent = signals[-20:] if len(signals) > 20 else signals
            weights = np.exp(np.linspace(-1, 0, len(recent)))
            avg_performance[rec_type] = np.average(recent, weights=weights)
        
        # 使用动量梯度下降更新权重
        new_weights = {}
        for rec_type in RecommenderType:
            current_weight = self.global_weights[rec_type]
            perf = avg_performance[rec_type]
            
            # 计算梯度（带正则化）
            gradient = perf - self.regularization * (current_weight - 0.2)
            
            # 动量更新
            self.velocity[rec_type] = (
                self.momentum * self.velocity[rec_type] + 
                self.learning_rate * gradient
            )
            
            # 更新权重
            new_weight = current_weight + self.velocity[rec_type]
            new_weight = np.clip(new_weight, self.min_weight, self.max_weight)
            new_weights[rec_type] = new_weight
        
        # 归一化
        self.global_weights = self._normalize_weights(new_weights)
        self.weight_history.append(self._weights_to_dict(self.global_weights))
    
    def _normalize_weights(
        self,
        weights: Dict[RecommenderType, float]
    ) -> Dict[RecommenderType, float]:
        """归一化权重使其和为1"""
        total = sum(weights.values())
        if total > 0:
            return {k: v / total for k, v in weights.items()}
        return self._init_weights()
    
    def _weights_to_dict(self, weights: Dict[RecommenderType, float]) -> Dict[str, float]:
        """转换权重为可序列化格式"""
        return {k.value: round(v, 4) for k, v in weights.items()}


# ============================================================================
# 多样性算法模块
# ============================================================================

class DiversityEnhancer:
    """
    多样性增强器
    
    使用MMR (Maximal Marginal Relevance) 算法和重新排序技术
    确保推荐结果的多样性，同时保持相关性。
    """
    
    def __init__(
        self,
        lambda_param: float = 0.5,
        branch_diversity_weight: float = 0.4,
        difficulty_diversity_weight: float = 0.3,
        novelty_weight: float = 0.3
    ):
        self.lambda_param = lambda_param
        self.branch_diversity_weight = branch_diversity_weight
        self.difficulty_diversity_weight = difficulty_diversity_weight
        self.novelty_weight = novelty_weight
        
        # 用户历史用于计算新颖性
        self.user_history: Dict[int, Set[str]] = defaultdict(set)
        self.user_branch_history: Dict[int, Dict[str, int]] = defaultdict(lambda: defaultdict(int))
    
    def enhance_diversity(
        self,
        candidates: List[RecommendationItem],
        user_id: int,
        n_recommendations: int,
        ensure_branch_coverage: bool = True
    ) -> List[RecommendationItem]:
        """
        增强推荐列表的多样性
        
        Args:
            candidates: 候选推荐项
            user_id: 用户ID
            n_recommendations: 需要的推荐数量
            ensure_branch_coverage: 是否确保分支覆盖
        
        Returns:
            重新排序后的推荐列表
        """
        if not candidates:
            return []
        
        # 1. 使用MMR算法进行重新排序
        selected = self._mmr_rerank(candidates, n_recommendations, user_id)
        
        # 2. 确保分支多样性
        if ensure_branch_coverage:
            selected = self._ensure_branch_diversity(selected, candidates, n_recommendations, user_id)
        
        # 3. 计算最终的多样性分数
        for item in selected:
            item.diversity_score = self._compute_diversity_score(item, selected, user_id)
            item.novelty_score = self._compute_novelty_score(item, user_id)
        
        # 更新用户历史
        self._update_user_history(user_id, selected)
        
        return selected
    
    def _mmr_rerank(
        self,
        candidates: List[RecommendationItem],
        n: int,
        user_id: int
    ) -> List[RecommendationItem]:
        """
        MMR (Maximal Marginal Relevance) 重新排序
        
        MMR = λ * Relevance - (1-λ) * max(Similarity to selected)
        """
        selected: List[RecommendationItem] = []
        remaining = candidates.copy()
        
        while len(selected) < n and remaining:
            if not selected:
                # 第一个选择相关性最高的
                best = max(remaining, key=lambda x: x.final_score)
            else:
                # 计算MMR分数
                mmr_scores = []
                for item in remaining:
                    relevance = item.final_score
                    max_sim = max(
                        self._compute_similarity(item, s) 
                        for s in selected
                    )
                    mmr_score = (
                        self.lambda_param * relevance - 
                        (1 - self.lambda_param) * max_sim
                    )
                    mmr_scores.append((item, mmr_score))
                
                best = max(mmr_scores, key=lambda x: x[1])[0]
            
            selected.append(best)
            remaining.remove(best)
        
        return selected
    
    def _compute_similarity(
        self,
        item1: RecommendationItem,
        item2: RecommendationItem
    ) -> float:
        """计算两个推荐项之间的相似度"""
        similarities = []
        
        # 分支相似度
        if item1.branch == item2.branch:
            similarities.append(1.0)
        else:
            similarities.append(0.0)
        
        # 难度相似度
        difficulty_map = {"basic": 0, "intermediate": 1, "advanced": 2, "research": 3}
        d1 = difficulty_map.get(item1.difficulty, 1)
        d2 = difficulty_map.get(item2.difficulty, 1)
        diff_sim = 1 - abs(d1 - d2) / 3.0
        similarities.append(diff_sim)
        
        # 组件分数相似度
        if item1.component_scores and item2.component_scores:
            common_keys = set(item1.component_scores.keys()) & set(item2.component_scores.keys())
            if common_keys:
                scores1 = [item1.component_scores[k] for k in common_keys]
                scores2 = [item2.component_scores[k] for k in common_keys]
                score_sim = 1 - abs(np.mean(scores1) - np.mean(scores2))
                similarities.append(score_sim)
        
        return np.mean(similarities)
    
    def _ensure_branch_diversity(
        self,
        selected: List[RecommendationItem],
        candidates: List[RecommendationItem],
        n: int,
        user_id: int
    ) -> List[RecommendationItem]:
        """确保推荐列表覆盖不同的数学分支"""
        branches_in_selected = {item.branch for item in selected}
        
        # 如果分支多样性不足，尝试替换部分推荐
        if len(branches_in_selected) < min(n // 3 + 1, 4):  # 至少覆盖几个分支
            # 找出缺失的热门分支
            all_branches = {c.branch for c in candidates}
            missing_branches = all_branches - branches_in_selected
            
            # 对于每个缺失的分支，尝试添加一个高质量推荐
            for branch in missing_branches:
                if len(selected) >= n:
                    break
                
                # 找到该分支的最佳候选
                branch_candidates = [
                    c for c in candidates 
                    if c.branch == branch and c not in selected
                ]
                
                if branch_candidates:
                    best_in_branch = max(branch_candidates, key=lambda x: x.final_score)
                    # 如果分数不太低，添加到推荐列表
                    if best_in_branch.final_score > 0.3:
                        # 找到selected中分数最低且同分支有其他推荐的项进行替换
                        candidates_to_replace = [
                            i for i, item in enumerate(selected)
                            if sum(1 for s in selected if s.branch == item.branch) > 1
                        ]
                        
                        if candidates_to_replace:
                            replace_idx = min(candidates_to_replace, key=lambda i: selected[i].final_score)
                            if selected[replace_idx].final_score < best_in_branch.final_score * 1.2:
                                selected[replace_idx] = best_in_branch
                        elif len(selected) < n:
                            selected.append(best_in_branch)
        
        return selected[:n]
    
    def _compute_diversity_score(
        self,
        item: RecommendationItem,
        selected: List[RecommendationItem],
        user_id: int
    ) -> float:
        """计算推荐项的多样性分数"""
        # 与其他选中项的平均距离
        if len(selected) <= 1:
            return 1.0
        
        similarities = [
            self._compute_similarity(item, other)
            for other in selected
            if other != item
        ]
        
        avg_dissimilarity = 1 - np.mean(similarities) if similarities else 1.0
        return avg_dissimilarity
    
    def _compute_novelty_score(
        self,
        item: RecommendationItem,
        user_id: int
    ) -> float:
        """计算新颖性分数"""
        # 基于用户历史
        if item.concept_id in self.user_history.get(user_id, set()):
            return 0.0
        
        # 基于分支历史
        branch_count = self.user_branch_history.get(user_id, {}).get(item.branch, 0)
        novelty = 1 / (1 + np.log1p(branch_count))
        
        return novelty
    
    def _update_user_history(self, user_id: int, selected: List[RecommendationItem]):
        """更新用户历史"""
        for item in selected:
            self.user_history[user_id].add(item.concept_id)
            self.user_branch_history[user_id][item.branch] += 1


# ============================================================================
# 冷启动处理模块
# ============================================================================

class ColdStartHandler:
    """
    冷启动处理器
    
    针对新用户的多层次冷启动策略，从完全新用户到正常用户的平滑过渡。
    """
    
    def __init__(self, db: Session):
        self.db = db
        self.user_profiles: Dict[int, Dict[str, Any]] = {}
        
        # 热门概念缓存
        self._popular_concepts_cache: Optional[List[Dict]] = None
        self._cache_timestamp: Optional[datetime] = None
    
    def detect_cold_start_level(self, user_id: int) -> Tuple[ColdStartLevel, Dict[str, Any]]:
        """
        检测用户的冷启动等级
        
        Returns:
            (冷启动等级, 用户信息)
        """
        # 获取用户活动统计
        from ..models.models import UserActivity, UserProgress
        
        activity_count = self.db.query(UserActivity).filter(
            UserActivity.user_id == user_id
        ).count()
        
        progress_count = self.db.query(UserProgress).filter(
            UserProgress.user_id == user_id
        ).count()
        
        # 获取兴趣设置
        activities = self.db.query(UserActivity).filter(
            UserActivity.user_id == user_id,
            UserActivity.activity_type.in_(["set_interest", "select_branch"])
        ).all()
        
        has_interest = len(activities) > 0
        
        # 判断冷启动等级
        if progress_count == 0 and activity_count < 5 and not has_interest:
            return ColdStartLevel.NEW_USER, {
                "activity_count": activity_count,
                "progress_count": progress_count,
                "has_interest": has_interest
            }
        elif has_interest and progress_count < 3:
            return ColdStartLevel.INTEREST_KNOWN, {
                "activity_count": activity_count,
                "progress_count": progress_count,
                "has_interest": has_interest
            }
        elif progress_count < 10:
            return ColdStartLevel.SOME_ACTIVITY, {
                "activity_count": activity_count,
                "progress_count": progress_count,
                "has_interest": has_interest
            }
        else:
            return ColdStartLevel.WARM_USER, {
                "activity_count": activity_count,
                "progress_count": progress_count,
                "has_interest": has_interest
            }
    
    def get_cold_start_recommendations(
        self,
        user_id: int,
        n_recommendations: int,
        level: ColdStartLevel
    ) -> List[RecommendationItem]:
        """
        根据冷启动等级获取推荐
        """
        if level == ColdStartLevel.NEW_USER:
            return self._new_user_recommendations(user_id, n_recommendations)
        elif level == ColdStartLevel.INTEREST_KNOWN:
            return self._interest_based_recommendations(user_id, n_recommendations)
        elif level == ColdStartLevel.SOME_ACTIVITY:
            return self._activity_based_recommendations(user_id, n_recommendations)
        else:
            return []  # 温用户不需要冷启动处理
    
    def _new_user_recommendations(
        self,
        user_id: int,
        n: int
    ) -> List[RecommendationItem]:
        """完全新用户推荐：热门基础概念 + 探索性推荐"""
        recommendations = []
        
        # 1. 获取热门基础概念
        popular = self._get_popular_concepts(n // 2)
        for p in popular:
            recommendations.append(RecommendationItem(
                concept_id=p["concept_id"],
                name=p["name"],
                branch=p["branch"],
                difficulty="basic",
                final_score=p["score"] * 0.9,  # 略降分以鼓励探索
                component_scores={"popularity": p["score"]},
                explanation={
                    "primary_reason": "popular_basic",
                    "message": f"热门基础概念，{p['learner_count']}人正在学习"
                },
                confidence=0.7
            ))
        
        # 2. 从各分支选一个代表性概念
        from ..models.models import KnowledgeGraphNode
        branches = self.db.query(KnowledgeGraphNode.branch).distinct().all()
        branches = [b[0] for b in branches]
        
        for branch in branches[:n - len(recommendations)]:
            concept = self.db.query(KnowledgeGraphNode).filter(
                KnowledgeGraphNode.branch == branch,
                KnowledgeGraphNode.difficulty == "basic"
            ).order_by(KnowledgeGraphNode.importance.desc()).first()
            
            if concept and not any(r.concept_id == concept.id for r in recommendations):
                recommendations.append(RecommendationItem(
                    concept_id=concept.id,
                    name=concept.name,
                    branch=concept.branch,
                    difficulty="basic",
                    final_score=0.75,
                    component_scores={"exploration": 0.75},
                    explanation={
                        "primary_reason": "exploration",
                        "message": f"{branch}领域入门概念，帮助您发现兴趣"
                    },
                    confidence=0.6
                ))
        
        return recommendations[:n]
    
    def _interest_based_recommendations(
        self,
        user_id: int,
        n: int
    ) -> List[RecommendationItem]:
        """已知兴趣用户的推荐"""
        from ..models.models import UserActivity, KnowledgeGraphNode
        
        # 获取用户兴趣
        interest_activities = self.db.query(UserActivity).filter(
            UserActivity.user_id == user_id,
            UserActivity.activity_type.in_(["set_interest", "select_branch"])
        ).all()
        
        interested_branches = set()
        for activity in interest_activities:
            if activity.metadata:
                interested_branches.add(activity.metadata.get("branch", ""))
        
        recommendations = []
        
        # 基于兴趣分支推荐
        for branch in interested_branches:
            if len(recommendations) >= n:
                break
            
            concepts = self.db.query(KnowledgeGraphNode).filter(
                KnowledgeGraphNode.branch == branch,
                KnowledgeGraphNode.difficulty.in_(["basic", "intermediate"])
            ).order_by(KnowledgeGraphNode.importance.desc()).limit(3).all()
            
            for concept in concepts:
                recommendations.append(RecommendationItem(
                    concept_id=concept.id,
                    name=concept.name,
                    branch=concept.branch,
                    difficulty=concept.difficulty.value,
                    final_score=0.85,
                    component_scores={"interest_match": 0.85},
                    explanation={
                        "primary_reason": "interest_match",
                        "message": f"基于您对{branch}的兴趣推荐"
                    },
                    confidence=0.75
                ))
        
        # 补充热门概念
        if len(recommendations) < n:
            popular = self._get_popular_concepts(n - len(recommendations))
            for p in popular:
                if not any(r.concept_id == p["concept_id"] for r in recommendations):
                    recommendations.append(RecommendationItem(
                        concept_id=p["concept_id"],
                        name=p["name"],
                        branch=p["branch"],
                        difficulty="basic",
                        final_score=p["score"] * 0.8,
                        component_scores={"popularity": p["score"]},
                        explanation={
                            "primary_reason": "popular",
                            "message": "热门学习内容"
                        },
                        confidence=0.7
                    ))
        
        return recommendations[:n]
    
    def _activity_based_recommendations(
        self,
        user_id: int,
        n: int
    ) -> List[RecommendationItem]:
        """有一定活动用户的推荐"""
        from ..models.models import UserActivity, UserProgress, KnowledgeGraphNode
        
        # 获取用户最近学习的概念
        recent_progress = self.db.query(UserProgress).filter(
            UserProgress.user_id == user_id
        ).order_by(UserProgress.last_studied_at.desc()).limit(5).all()
        
        studied_branches = set()
        for p in recent_progress:
            concept = self.db.query(KnowledgeGraphNode).filter(
                KnowledgeGraphNode.id == p.concept_id
            ).first()
            if concept:
                studied_branches.add(concept.branch)
        
        recommendations = []
        
        # 推荐已学分支的进阶内容
        for branch in studied_branches:
            if len(recommendations) >= n // 2:
                break
            
            studied_ids = {p.concept_id for p in recent_progress}
            
            next_concepts = self.db.query(KnowledgeGraphNode).filter(
                KnowledgeGraphNode.branch == branch,
                ~KnowledgeGraphNode.id.in_(studied_ids)
            ).order_by(KnowledgeGraphNode.importance.desc()).limit(2).all()
            
            for concept in next_concepts:
                recommendations.append(RecommendationItem(
                    concept_id=concept.id,
                    name=concept.name,
                    branch=concept.branch,
                    difficulty=concept.difficulty.value,
                    final_score=0.8,
                    component_scores={"continuation": 0.8},
                    explanation={
                        "primary_reason": "continuation",
                        "message": f"{branch}领域的进阶内容"
                    },
                    confidence=0.72
                ))
        
        # 推荐新分支的入门内容
        all_branches = {b[0] for b in self.db.query(KnowledgeGraphNode.branch).distinct().all()}
        new_branches = all_branches - studied_branches
        
        for branch in list(new_branches)[:n - len(recommendations)]:
            concept = self.db.query(KnowledgeGraphNode).filter(
                KnowledgeGraphNode.branch == branch,
                KnowledgeGraphNode.difficulty == "basic"
            ).order_by(KnowledgeGraphNode.importance.desc()).first()
            
            if concept:
                recommendations.append(RecommendationItem(
                    concept_id=concept.id,
                    name=concept.name,
                    branch=concept.branch,
                    difficulty="basic",
                    final_score=0.75,
                    component_scores={"exploration": 0.75},
                    explanation={
                        "primary_reason": "exploration",
                        "message": f"探索新的数学领域: {branch}"
                    },
                    confidence=0.65
                ))
        
        return recommendations[:n]
    
    def _get_popular_concepts(self, n: int) -> List[Dict]:
        """获取热门概念（带缓存）"""
        from ..models.models import UserProgress, KnowledgeGraphNode
        from sqlalchemy import func
        
        # 检查缓存
        if (self._popular_concepts_cache and self._cache_timestamp and
            datetime.utcnow() - self._cache_timestamp < timedelta(hours=1)):
            return self._popular_concepts_cache[:n]
        
        # 查询热门概念
        popular = self.db.query(
            UserProgress.concept_id,
            func.count(UserProgress.user_id).label("user_count"),
            func.avg(UserProgress.mastery_level).label("avg_mastery")
        ).group_by(UserProgress.concept_id).order_by(
            func.count(UserProgress.user_id).desc()
        ).limit(n * 2).all()
        
        result = []
        for p in popular:
            concept = self.db.query(KnowledgeGraphNode).filter(
                KnowledgeGraphNode.id == p.concept_id
            ).first()
            
            if concept and concept.difficulty == "basic":
                score = min(p.user_count / 100, 1.0) * 0.5 + p.avg_mastery * 0.5
                result.append({
                    "concept_id": p.concept_id,
                    "name": concept.name,
                    "branch": concept.branch,
                    "score": float(score),
                    "learner_count": p.user_count
                })
        
        # 更新缓存
        self._popular_concepts_cache = result
        self._cache_timestamp = datetime.utcnow()
        
        return result[:n]
    
    def get_cold_start_context(self, user_id: int) -> Dict[str, Any]:
        """获取冷启动上下文信息"""
        level, info = self.detect_cold_start_level(user_id)
        
        return {
            "level": level.value,
            "is_cold_start": level != ColdStartLevel.WARM_USER,
            "activity_count": info["activity_count"],
            "progress_count": info["progress_count"],
            "has_interest": info["has_interest"],
            "recommended_strategy": self._get_strategy_for_level(level)
        }
    
    def _get_strategy_for_level(self, level: ColdStartLevel) -> str:
        """获取对应等级的策略描述"""
        strategies = {
            ColdStartLevel.NEW_USER: "热门基础概念 + 多领域探索",
            ColdStartLevel.INTEREST_KNOWN: "兴趣匹配 + 个性化入门",
            ColdStartLevel.SOME_ACTIVITY: "学习延续 + 适度探索",
            ColdStartLevel.WARM_USER: "标准推荐算法"
        }
        return strategies.get(level, "标准推荐")


# ============================================================================
# 可解释性模块
# ============================================================================

class ExplainabilityEngine:
    """
    可解释性引擎
    
    生成详细的推荐理由和透明度报告，帮助用户理解推荐逻辑。
    """
    
    def __init__(self, db: Session):
        self.db = db
    
    def generate_explanation(
        self,
        item: RecommendationItem,
        user_id: int,
        weights: Dict[RecommenderType, float]
    ) -> Dict[str, Any]:
        """
        生成推荐项的详细解释
        """
        explanation = {
            "primary_reason": "",
            "contributing_factors": [],
            "algorithm_breakdown": {},
            "user_profile_match": {},
            "confidence_explanation": "",
            "alternative_options": []
        }
        
        # 1. 主要推荐理由
        explanation["primary_reason"] = self._determine_primary_reason(
            item, weights
        )
        
        # 2. 贡献因素
        explanation["contributing_factors"] = self._identify_contributing_factors(
            item, user_id
        )
        
        # 3. 算法分解
        explanation["algorithm_breakdown"] = self._breakdown_algorithms(
            item, weights
        )
        
        # 4. 用户画像匹配
        explanation["user_profile_match"] = self._analyze_profile_match(
            item, user_id
        )
        
        # 5. 置信度解释
        explanation["confidence_explanation"] = self._explain_confidence(
            item.confidence, item.component_scores
        )
        
        # 6. 替代选项说明
        explanation["alternative_options"] = self._suggest_alternatives(
            item, user_id
        )
        
        return explanation
    
    def _determine_primary_reason(
        self,
        item: RecommendationItem,
        weights: Dict[RecommenderType, float]
    ) -> str:
        """确定主要推荐理由"""
        if not item.component_scores:
            return "综合推荐"
        
        # 找出加权后贡献最大的组件
        weighted_scores = {}
        for comp, score in item.component_scores.items():
            weight_key = None
            if comp == "collaborative":
                weight_key = RecommenderType.COLLABORATIVE
            elif comp == "knowledge_graph":
                weight_key = RecommenderType.KNOWLEDGE_GRAPH
            elif comp == "rl":
                weight_key = RecommenderType.REINFORCEMENT_LEARNING
            elif comp == "content":
                weight_key = RecommenderType.CONTENT
            
            if weight_key:
                weighted_scores[comp] = score * weights.get(weight_key, 0.2)
        
        if not weighted_scores:
            return "综合多维度匹配"
        
        strongest = max(weighted_scores, key=weighted_scores.get)
        
        reason_map = {
            "collaborative": "与您学习路径相似的用户也在学习此概念",
            "knowledge_graph": "基于知识图谱的语义关联推荐",
            "rl": "智能算法预测此概念对您的学习收益最大",
            "content": "与您当前的学习水平和兴趣高度匹配",
            "popularity": "广受学习者欢迎的基础概念",
            "exploration": "帮助您探索新的数学领域",
            "interest_match": "与您的学习兴趣高度契合"
        }
        
        return reason_map.get(strongest, "综合多维度匹配")
    
    def _identify_contributing_factors(
        self,
        item: RecommendationItem,
        user_id: int
    ) -> List[str]:
        """识别贡献因素"""
        factors = []
        
        # 难度匹配
        difficulty_map = {"basic": 0, "intermediate": 1, "advanced": 2, "research": 3}
        diff_level = difficulty_map.get(item.difficulty, 1)
        
        if diff_level <= 1:
            factors.append("适合您当前的学习阶段")
        elif diff_level == 2:
            factors.append("适度的挑战性，有助于能力提升")
        else:
            factors.append("高级内容，适合深入学习")
        
        # 分支相关
        factors.append(f"属于{item.branch}领域")
        
        # 多样性贡献
        if item.diversity_score > 0.7:
            factors.append("有助于拓展您的学习广度")
        
        # 新颖性
        if item.novelty_score > 0.8:
            factors.append("全新的学习领域")
        
        return factors
    
    def _breakdown_algorithms(
        self,
        item: RecommendationItem,
        weights: Dict[RecommenderType, float]
    ) -> Dict[str, Any]:
        """分解各算法的贡献"""
        breakdown = {}
        
        for comp, score in item.component_scores.items():
            rec_type = None
            name = comp
            if comp == "collaborative":
                rec_type = RecommenderType.COLLABORATIVE
                name = "协同过滤"
            elif comp == "knowledge_graph":
                rec_type = RecommenderType.KNOWLEDGE_GRAPH
                name = "知识图谱"
            elif comp == "rl":
                rec_type = RecommenderType.REINFORCEMENT_LEARNING
                name = "强化学习"
            elif comp == "content":
                rec_type = RecommenderType.CONTENT
                name = "内容分析"
            
            if rec_type:
                breakdown[name] = {
                    "raw_score": round(score, 4),
                    "weight": round(weights.get(rec_type, 0.2), 4),
                    "weighted_contribution": round(
                        score * weights.get(rec_type, 0.2), 4
                    )
                }
        
        return breakdown
    
    def _analyze_profile_match(
        self,
        item: RecommendationItem,
        user_id: int
    ) -> Dict[str, float]:
        """分析用户画像匹配度"""
        from ..models.models import UserProgress, UserActivity
        
        match_scores = {}
        
        # 检查用户在该分支的历史
        branch_progress = self.db.query(UserProgress).join(
            KnowledgeGraphNode,
            UserProgress.concept_id == KnowledgeGraphNode.id
        ).filter(
            UserProgress.user_id == user_id,
            KnowledgeGraphNode.branch == item.branch
        ).count()
        
        if branch_progress > 0:
            match_scores["branch_familiarity"] = min(branch_progress / 10, 1.0)
        else:
            match_scores["branch_familiarity"] = 0.0
        
        # 难度匹配
        user_avg_mastery = self.db.query(
            func.avg(UserProgress.mastery_level)
        ).filter(
            UserProgress.user_id == user_id
        ).scalar() or 0.5
        
        difficulty_map = {"basic": 0.25, "intermediate": 0.5, "advanced": 0.75, "research": 1.0}
        item_difficulty = difficulty_map.get(item.difficulty, 0.5)
        
        match_scores["difficulty_match"] = 1 - abs(user_avg_mastery - item_difficulty)
        
        return match_scores
    
    def _explain_confidence(
        self,
        confidence: float,
        component_scores: Dict[str, float]
    ) -> str:
        """解释置信度"""
        num_sources = len(component_scores)
        
        if confidence >= 0.8:
            return f"高置信度（{num_sources}个推荐源一致支持）"
        elif confidence >= 0.5:
            return f"中等置信度（{num_sources}个推荐源支持，建议尝试）"
        else:
            return f"探索性推荐（{num_sources}个推荐源支持，供您参考）"
    
    def _suggest_alternatives(
        self,
        item: RecommendationItem,
        user_id: int
    ) -> List[str]:
        """建议替代选项"""
        from ..models.models import KnowledgeGraphNode
        
        # 查找同分支的其他概念
        alternatives = self.db.query(KnowledgeGraphNode).filter(
            KnowledgeGraphNode.branch == item.branch,
            KnowledgeGraphNode.id != item.concept_id
        ).limit(3).all()
        
        return [alt.name for alt in alternatives]
    
    def generate_transparency_report(
        self,
        user_id: int,
        recommendations: List[RecommendationItem],
        weights: Dict[RecommenderType, float]
    ) -> Dict[str, Any]:
        """生成透明度报告"""
        return {
            "report_type": "recommendation_transparency",
            "timestamp": datetime.utcnow().isoformat(),
            "user_id": user_id,
            "algorithm_weights": {k.value: round(v, 4) for k, v in weights.items()},
            "recommendation_count": len(recommendations),
            "diversity_metrics": {
                "branch_coverage": len(set(r.branch for r in recommendations)),
                "avg_diversity_score": np.mean([r.diversity_score for r in recommendations]),
                "avg_novelty_score": np.mean([r.novelty_score for r in recommendations])
            },
            "data_usage": {
                "user_history_used": True,
                "collaborative_data_used": True,
                "knowledge_graph_used": True
            }
        }


# ============================================================================
# 主推荐器类
# ============================================================================

class AdvancedHybridRecommender:
    """
    高级混合推荐器 v2.0
    
    整合所有优化功能的统一推荐接口。
    """
    
    def __init__(self, db: Session):
        self.db = db
        
        # 初始化各模块
        self.weight_adjuster = DynamicWeightAdjuster()
        self.diversity_enhancer = DiversityEnhancer()
        self.cold_start_handler = ColdStartHandler(db)
        self.explainability_engine = ExplainabilityEngine(db)
        
        # 基础推荐器
        self.recommenders: Dict[RecommenderType, Any] = {}
        self._initialized = False
        
        # A/B测试
        self.ab_test_config: Optional[Dict[str, Any]] = None
        
        logger.info("AdvancedHybridRecommender 初始化完成")
    
    def initialize(self):
        """初始化所有基础推荐器"""
        if self._initialized:
            return
        
        logger.info("初始化基础推荐器...")
        
        # 协同过滤
        try:
            cf = CollaborativeFiltering(self.db)
            cf.build_user_item_matrix()
            cf.compute_user_similarity()
            cf.train_matrix_factorization()
            self.recommenders[RecommenderType.COLLABORATIVE] = cf
            logger.info("协同过滤推荐器初始化完成")
        except Exception as e:
            logger.warning(f"协同过滤初始化失败: {e}")
        
        # 知识图谱
        try:
            kg = KnowledgeGraphEmbedding(self.db)
            kg.build_model()
            self.recommenders[RecommenderType.KNOWLEDGE_GRAPH] = kg
            logger.info("知识图谱推荐器初始化完成")
        except Exception as e:
            logger.warning(f"知识图谱初始化失败: {e}")
        
        # 强化学习
        try:
            rl = RLRecommender(self.db)
            rl.initialize()
            self.recommenders[RecommenderType.REINFORCEMENT_LEARNING] = rl
            logger.info("强化学习推荐器初始化完成")
        except Exception as e:
            logger.warning(f"强化学习初始化失败: {e}")
        
        # 内容推荐
        try:
            content = ContentRecommender(self.db)
            self.recommenders[RecommenderType.CONTENT] = content
            logger.info("内容推荐器初始化完成")
        except Exception as e:
            logger.warning(f"内容推荐初始化失败: {e}")
        
        self._initialized = True
    
    def recommend(
        self,
        user_id: int,
        n_recommendations: int = 10,
        context: Optional[Dict[str, Any]] = None,
        enable_diversity: bool = True,
        enable_explanation: bool = True
    ) -> Dict[str, Any]:
        """
        生成推荐
        
        Args:
            user_id: 用户ID
            n_recommendations: 推荐数量
            context: 上下文信息
            enable_diversity: 是否启用多样性增强
            enable_explanation: 是否生成解释
        
        Returns:
            包含推荐结果和元数据的字典
        """
        if not self._initialized:
            self.initialize()
        
        # 1. 检测冷启动
        cold_start_level, _ = self.cold_start_handler.detect_cold_start_level(user_id)
        
        # 2. 冷启动处理
        if cold_start_level != ColdStartLevel.WARM_USER:
            recommendations = self.cold_start_handler.get_cold_start_recommendations(
                user_id, n_recommendations, cold_start_level
            )
            
            # 冷启动用户也需要多样性
            if enable_diversity and recommendations:
                recommendations = self.diversity_enhancer.enhance_diversity(
                    recommendations, user_id, n_recommendations
                )
            
            # 生成解释
            if enable_explanation:
                weights = self.weight_adjuster.get_weights(user_id, context)
                for item in recommendations:
                    item.explanation = self.explainability_engine.generate_explanation(
                        item, user_id, weights
                    )
            
            return {
                "recommendations": [r.to_dict() for r in recommendations],
                "metadata": {
                    "cold_start": True,
                    "cold_start_level": cold_start_level.value,
                    "strategy": self.cold_start_handler._get_strategy_for_level(cold_start_level)
                }
            }
        
        # 3. 获取动态权重
        weights = self.weight_adjuster.get_weights(user_id, context)
        
        # 4. 收集各推荐器结果
        all_candidates = self._collect_recommendations(
            user_id, n_recommendations * 3, weights
        )
        
        # 5. 融合分数
        fused_candidates = self._fuse_scores(all_candidates, weights)
        
        # 6. 多样性增强
        if enable_diversity:
            final_recommendations = self.diversity_enhancer.enhance_diversity(
                fused_candidates, user_id, n_recommendations
            )
        else:
            final_recommendations = fused_candidates[:n_recommendations]
        
        # 7. 生成解释
        if enable_explanation:
            for item in final_recommendations:
                item.explanation = self.explainability_engine.generate_explanation(
                    item, user_id, weights
                )
        
        # 8. 构建返回结果
        result = {
            "recommendations": [r.to_dict() for r in final_recommendations],
            "metadata": {
                "cold_start": False,
                "algorithm_weights": {k.value: round(v, 4) for k, v in weights.items()},
                "total_candidates": len(all_candidates),
                "diversity_enabled": enable_diversity,
                "explanation_enabled": enable_explanation
            }
        }
        
        # 9. 添加透明度报告
        if enable_explanation:
            result["transparency_report"] = \
                self.explainability_engine.generate_transparency_report(
                    user_id, final_recommendations, weights
                )
        
        return result
    
    def _collect_recommendations(
        self,
        user_id: int,
        n_candidates: int,
        weights: Dict[RecommenderType, float]
    ) -> List[Tuple[RecommendationItem, str]]:
        """收集所有推荐器的候选"""
        candidates = []
        
        # 协同过滤
        if RecommenderType.COLLABORATIVE in self.recommenders:
            try:
                cf = self.recommenders[RecommenderType.COLLABORATIVE]
                recs = cf.recommend_for_user(user_id, n_candidates, method="hybrid")
                for r in recs:
                    candidates.append((self._dict_to_item(r, "collaborative"), "collaborative"))
            except Exception as e:
                logger.warning(f"协同过滤推荐失败: {e}")
        
        # 知识图谱
        if RecommenderType.KNOWLEDGE_GRAPH in self.recommenders:
            try:
                kg = self.recommenders[RecommenderType.KNOWLEDGE_GRAPH]
                if kg.model is not None:
                    recs = kg.recommend_by_knowledge_graph(user_id, n_candidates)
                    for r in recs:
                        candidates.append((self._dict_to_item(r, "knowledge_graph"), "knowledge_graph"))
            except Exception as e:
                logger.warning(f"知识图谱推荐失败: {e}")
        
        # 强化学习
        if RecommenderType.REINFORCEMENT_LEARNING in self.recommenders:
            try:
                rl = self.recommenders[RecommenderType.REINFORCEMENT_LEARNING]
                recs = rl.recommend(user_id, n_candidates // 2)
                for r in recs:
                    candidates.append((self._dict_to_item(r, "rl"), "rl"))
            except Exception as e:
                logger.warning(f"强化学习推荐失败: {e}")
        
        # 内容推荐
        if RecommenderType.CONTENT in self.recommenders:
            try:
                content = self.recommenders[RecommenderType.CONTENT]
                recs = content.recommend(user_id, n_candidates, strategy="hybrid")
                for r in recs:
                    candidates.append((self._dict_to_item(r, "content"), "content"))
            except Exception as e:
                logger.warning(f"内容推荐失败: {e}")
        
        return candidates
    
    def _dict_to_item(self, rec: Dict, source: str) -> RecommendationItem:
        """将字典转换为RecommendationItem"""
        return RecommendationItem(
            concept_id=rec.get("concept_id", ""),
            name=rec.get("name", ""),
            branch=rec.get("branch", ""),
            difficulty=rec.get("difficulty", "intermediate"),
            final_score=rec.get("score", rec.get("expected_reward", 0.5)),
            component_scores={source: rec.get("score", rec.get("expected_reward", 0.5))},
            explanation={"source": source}
        )
    
    def _fuse_scores(
        self,
        candidates: List[Tuple[RecommendationItem, str]],
        weights: Dict[RecommenderType, float]
    ) -> List[RecommendationItem]:
        """融合多个推荐器的分数"""
        # 按concept_id分组
        grouped = defaultdict(lambda: {"item": None, "scores": {}})
        
        for item, source in candidates:
            cid = item.concept_id
            if grouped[cid]["item"] is None:
                grouped[cid]["item"] = item
            
            score = item.component_scores.get(source, item.final_score)
            grouped[cid]["scores"][source] = score
        
        # 融合分数
        fused_items = []
        for cid, data in grouped.items():
            item = data["item"]
            scores = data["scores"]
            
            # 加权融合
            final_score = 0.0
            for source, score in scores.items():
                weight_key = None
                if source == "collaborative":
                    weight_key = RecommenderType.COLLABORATIVE
                elif source == "knowledge_graph":
                    weight_key = RecommenderType.KNOWLEDGE_GRAPH
                elif source == "rl":
                    weight_key = RecommenderType.REINFORCEMENT_LEARNING
                elif source == "content":
                    weight_key = RecommenderType.CONTENT
                
                if weight_key:
                    final_score += score * weights.get(weight_key, 0.2)
            
            item.final_score = final_score
            item.component_scores = scores
            item.confidence = len(scores) / 4.0  # 基于支持来源数量
            
            fused_items.append(item)
        
        # 按分数排序
        fused_items.sort(key=lambda x: x.final_score, reverse=True)
        return fused_items
    
    def record_feedback(
        self,
        user_id: int,
        concept_id: str,
        action: str,
        rating: Optional[float] = None,
        context: Optional[Dict[str, Any]] = None
    ):
        """记录用户反馈"""
        try:
            action_enum = UserAction(action)
        except ValueError:
            action_enum = UserAction.CLICK
        
        feedback = UserFeedback(
            user_id=user_id,
            concept_id=concept_id,
            action=action_enum,
            rating=rating,
            context=context or {},
            metadata={"timestamp": datetime.utcnow().isoformat()}
        )
        
        # 构建组件贡献（简化处理，实际需要记录推荐时的贡献）
        component_contributions = {action: 1.0}
        
        self.weight_adjuster.record_feedback(feedback, component_contributions)
        
        logger.info(f"记录反馈: user={user_id}, concept={concept_id}, action={action}")
    
    def setup_ab_test(
        self,
        test_name: str,
        variants: List[Dict[str, Any]]
    ):
        """设置A/B测试"""
        self.ab_test_config = {
            "test_name": test_name,
            "variants": variants,
            "user_assignments": {}
        }
    
    def get_ab_test_group(self, user_id: int, test_name: str) -> str:
        """获取用户的A/B测试分组"""
        # 使用一致性哈希
        hash_input = f"{test_name}:{user_id}"
        hash_value = int(hashlib.md5(hash_input.encode()).hexdigest(), 16)
        
        # 假设有A、B两组
        return "A" if hash_value % 2 == 0 else "B"


# ============================================================================
# 便捷函数
# ============================================================================

def get_advanced_recommender(db: Session) -> AdvancedHybridRecommender:
    """获取高级推荐器实例"""
    return AdvancedHybridRecommender(db)
