"""
混合推荐系统 - 优化版本
- 动态权重调整
- 在线学习
- 更好的冷启动处理
"""
import numpy as np
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, field
from enum import Enum
from sqlalchemy.orm import Session
from collections import defaultdict
import logging
import hashlib
import json
from datetime import datetime

from ..models.models import User, UserProgress, KnowledgeGraphNode, UserActivity
from .collaborative_filtering import CollaborativeFiltering
from .knowledge_embedding import KnowledgeGraphEmbedding
from .rl_recommendation import RLRecommender
from .content_recommendation import ContentRecommender

logger = logging.getLogger(__name__)


class RecommenderType(Enum):
    """推荐器类型"""
    COLLABORATIVE = "collaborative"
    KNOWLEDGE_GRAPH = "knowledge_graph"
    REINFORCEMENT_LEARNING = "reinforcement_learning"
    CONTENT = "content"


@dataclass
class RecommendationResult:
    """推荐结果"""
    concept_id: str
    name: str
    branch: str
    final_score: float
    component_scores: Dict[str, float] = field(default_factory=dict)
    explanation: str = ""
    confidence: float = 0.0


@dataclass
class UserFeedback:
    """用户反馈"""
    user_id: int
    concept_id: str
    action: str  # 'click', 'complete', 'skip', 'dismiss'
    rating: Optional[float] = None  # 显式评分
    timestamp: datetime = field(default_factory=datetime.utcnow)


class DynamicWeightOptimizer:
    """
    动态权重优化器
    基于用户反馈自动调整各推荐器的权重
    """
    
    def __init__(self, learning_rate: float = 0.01, min_weight: float = 0.1):
        self.learning_rate = learning_rate
        self.min_weight = min_weight
        self.feedback_history: Dict[int, List[UserFeedback]] = defaultdict(list)
        self.weight_performance: Dict[RecommenderType, List[float]] = defaultdict(list)
        
    def record_feedback(self, feedback: UserFeedback, component_scores: Dict[str, float]):
        """记录用户反馈"""
        self.feedback_history[feedback.user_id].append(feedback)
        
        # 将反馈归因到各推荐器组件
        action_weight = self._action_to_weight(feedback.action)
        
        for component, score in component_scores.items():
            if score > 0:  # 该推荐器推荐了此项目
                try:
                    rec_type = RecommenderType(component)
                    self.weight_performance[rec_type].append(action_weight)
                except ValueError:
                    pass
    
    def _action_to_weight(self, action: str) -> float:
        """将用户动作转换为权重信号"""
        action_weights = {
            'complete': 1.0,    # 完成学习 - 强正反馈
            'click': 0.5,       # 点击 - 正反馈
            'dismiss': -0.3,    # 忽略 - 负反馈
            'skip': -0.5,       # 跳过 - 强负反馈
        }
        return action_weights.get(action, 0.0)
    
    def optimize_weights(
        self,
        current_weights: Dict[RecommenderType, float],
        user_id: Optional[int] = None
    ) -> Dict[RecommenderType, float]:
        """
        优化权重
        
        使用梯度上升法基于反馈历史调整权重
        """
        if user_id and len(self.feedback_history[user_id]) < 5:
            # 反馈不足，使用全局权重
            return current_weights
        
        # 计算各推荐器的平均表现
        performance = {}
        for rec_type in RecommenderType:
            if self.weight_performance[rec_type]:
                # 使用最近20条反馈
                recent = self.weight_performance[rec_type][-20:]
                performance[rec_type] = np.mean(recent)
            else:
                performance[rec_type] = 0.0
        
        # 基于表现调整权重
        new_weights = {}
        total = 0.0
        
        for rec_type in RecommenderType:
            current = current_weights.get(rec_type, 0.25)
            perf = performance.get(rec_type, 0.0)
            
            # 梯度上升更新
            adjustment = self.learning_rate * perf
            new_weight = max(self.min_weight, current + adjustment)
            new_weights[rec_type] = new_weight
            total += new_weight
        
        # 归一化
        for rec_type in new_weights:
            new_weights[rec_type] /= total
        
        return new_weights


class HybridRecommenderOptimized:
    """
    优化的混合推荐器
    
    改进点：
    1. 动态权重调整
    2. 更好的ground truth获取
    3. 在线学习机制
    4. 用户级个性化权重
    """
    
    def __init__(self, db: Session):
        self.db = db
        self.recommenders = {}
        self.base_weights = {
            RecommenderType.COLLABORATIVE: 0.25,
            RecommenderType.KNOWLEDGE_GRAPH: 0.25,
            RecommenderType.REINFORCEMENT_LEARNING: 0.25,
            RecommenderType.CONTENT: 0.25
        }
        self.user_weights: Dict[int, Dict[RecommenderType, float]] = {}
        self.ab_test_assignments = {}
        
        # 动态权重优化器
        self.weight_optimizer = DynamicWeightOptimizer(learning_rate=0.02)
        
        # 反馈历史
        self.feedback_buffer: List[UserFeedback] = []
        
    def get_weights(self, user_id: int) -> Dict[RecommenderType, float]:
        """获取用户特定的权重"""
        if user_id not in self.user_weights:
            # 新用户使用基础权重
            self.user_weights[user_id] = self.base_weights.copy()
        return self.user_weights[user_id]
    
    def set_user_weights(self, user_id: int, weights: Dict[RecommenderType, float]):
        """设置用户特定权重"""
        total = sum(weights.values())
        self.user_weights[user_id] = {k: v/total for k, v in weights.items()}
    
    def initialize_recommenders(self):
        """初始化所有推荐器"""
        logger.info("初始化优化版混合推荐器...")
        
        # 协同过滤
        cf = CollaborativeFiltering(self.db)
        cf.build_user_item_matrix()
        cf.compute_user_similarity()
        cf.train_matrix_factorization()
        self.recommenders[RecommenderType.COLLABORATIVE] = cf
        
        # 知识图谱嵌入
        kg = KnowledgeGraphEmbedding(self.db, model_type="rotate")
        kg.build_model()
        self.recommenders[RecommenderType.KNOWLEDGE_GRAPH] = kg
        
        # 强化学习
        rl = RLRecommender(self.db, algorithm="linucb")
        rl.initialize()
        self.recommenders[RecommenderType.REINFORCEMENT_LEARNING] = rl
        
        # 内容推荐
        content = ContentRecommender(self.db)
        self.recommenders[RecommenderType.CONTENT] = content
        
        logger.info("所有推荐器初始化完成")
    
    def recommend(
        self,
        user_id: int,
        n_recommendations: int = 10,
        context: Optional[Dict[str, Any]] = None,
        enable_weight_optimization: bool = True
    ) -> List[RecommendationResult]:
        """
        生成混合推荐
        
        Args:
            user_id: 用户ID
            n_recommendations: 推荐数量
            context: 上下文信息
            enable_weight_optimization: 是否启用权重优化
        """
        if not self.recommenders:
            self.initialize_recommenders()
        
        # 获取用户权重
        weights = self.get_weights(user_id)
        
        # 收集所有推荐器的输出
        all_recommendations = defaultdict(lambda: {"scores": {}, "info": None})
        
        # 1. 协同过滤推荐
        if RecommenderType.COLLABORATIVE in self.recommenders:
            cf_recs = self.recommenders[RecommenderType.COLLABORATIVE].recommend_for_user(
                user_id, n_recommendations * 2, method="hybrid"
            )
            for rec in cf_recs:
                cid = rec["concept_id"]
                all_recommendations[cid]["scores"]["collaborative"] = rec["score"]
                all_recommendations[cid]["info"] = rec
        
        # 2. 知识图谱推荐
        if RecommenderType.KNOWLEDGE_GRAPH in self.recommenders:
            kg = self.recommenders[RecommenderType.KNOWLEDGE_GRAPH]
            if kg.model is not None:
                kg_recs = kg.recommend_by_knowledge_graph(user_id, n_recommendations * 2)
                for rec in kg_recs:
                    cid = rec["concept_id"]
                    all_recommendations[cid]["scores"]["knowledge_graph"] = rec["score"]
                    if all_recommendations[cid]["info"] is None:
                        all_recommendations[cid]["info"] = rec
        
        # 3. 强化学习推荐
        if RecommenderType.REINFORCEMENT_LEARNING in self.recommenders:
            rl_recs = self.recommenders[RecommenderType.REINFORCEMENT_LEARNING].recommend(
                user_id, n_recommendations
            )
            for rec in rl_recs:
                cid = rec["concept_id"]
                all_recommendations[cid]["scores"]["rl"] = rec.get("expected_reward", 0.5)
                if all_recommendations[cid]["info"] is None:
                    all_recommendations[cid]["info"] = rec
        
        # 4. 内容推荐
        if RecommenderType.CONTENT in self.recommenders:
            content_recs = self.recommenders[RecommenderType.CONTENT].recommend(
                user_id, n_recommendations, strategy="hybrid"
            )
            for rec in content_recs:
                cid = rec["concept_id"]
                all_recommendations[cid]["scores"]["content"] = rec["score"]
                if all_recommendations[cid]["info"] is None:
                    all_recommendations[cid]["info"] = rec
        
        # 融合分数
        results = []
        for concept_id, data in all_recommendations.items():
            final_score = 0.0
            component_scores = data["scores"]
            
            # 使用动态权重进行加权融合
            if "collaborative" in component_scores:
                final_score += weights[RecommenderType.COLLABORATIVE] * component_scores["collaborative"]
            if "knowledge_graph" in component_scores:
                final_score += weights[RecommenderType.KNOWLEDGE_GRAPH] * component_scores["knowledge_graph"]
            if "rl" in component_scores:
                final_score += weights[RecommenderType.REINFORCEMENT_LEARNING] * component_scores["rl"]
            if "content" in component_scores:
                final_score += weights[RecommenderType.CONTENT] * component_scores["content"]
            
            # 计算置信度（基于有多少推荐器支持）
            confidence = len(component_scores) / 4.0
            
            # 获取概念详情
            info = data["info"]
            concept = self.db.query(KnowledgeGraphNode).filter(
                KnowledgeGraphNode.id == concept_id
            ).first()
            
            if concept:
                result = RecommendationResult(
                    concept_id=concept_id,
                    name=concept.name,
                    branch=concept.branch,
                    final_score=float(final_score),
                    component_scores=component_scores,
                    explanation=self._generate_explanation(component_scores, concept, weights),
                    confidence=float(confidence)
                )
                results.append(result)
        
        # 按最终分数排序
        results.sort(key=lambda x: x.final_score, reverse=True)
        return results[:n_recommendations]
    
    def _generate_explanation(
        self,
        component_scores: Dict[str, float],
        concept,
        weights: Dict[RecommenderType, float]
    ) -> str:
        """生成推荐解释（包含权重信息）"""
        explanations = []
        
        if component_scores:
            # 找出贡献最大的推荐来源
            weighted_scores = {}
            for comp, score in component_scores.items():
                try:
                    rec_type = RecommenderType(comp)
                    weighted_scores[comp] = score * weights.get(rec_type, 0.25)
                except ValueError:
                    weighted_scores[comp] = score
            
            strongest = max(weighted_scores, key=weighted_scores.get)
            
            explanations_map = {
                "collaborative": f"与相似用户的学习路径匹配 (权重: {weights[RecommenderType.COLLABORATIVE]:.0%})",
                "knowledge_graph": f"知识图谱语义相似度: {component_scores['knowledge_graph']:.2f}",
                "rl": f"强化学习预期收益: {component_scores['rl']:.2f}",
                "content": f"内容匹配度: {component_scores['content']:.2f}"
            }
            
            if strongest in explanations_map:
                explanations.append(f"主要依据: {explanations_map[strongest]}")
        
        # 添加难度信息
        if concept:
            explanations.append(f"难度: {concept.difficulty.value}")
        
        return " | ".join(explanations)
    
    def record_feedback(
        self,
        user_id: int,
        concept_id: str,
        action: str,
        rating: Optional[float] = None
    ):
        """
        记录用户反馈
        
        Args:
            user_id: 用户ID
            concept_id: 概念ID
            action: 用户动作
            rating: 显式评分（可选）
        """
        feedback = UserFeedback(
            user_id=user_id,
            concept_id=concept_id,
            action=action,
            rating=rating
        )
        
        self.feedback_buffer.append(feedback)
        
        # 批量处理反馈
        if len(self.feedback_buffer) >= 10:
            self._process_feedback_batch()
    
    def _process_feedback_batch(self):
        """批量处理反馈并更新权重"""
        for feedback in self.feedback_buffer:
            # 获取该推荐时的组件分数（这里简化处理）
            component_scores = {feedback.concept_id: {"collaborative": 1.0}}  # 简化示例
            self.weight_optimizer.record_feedback(feedback, component_scores)
        
        # 清空缓冲区
        self.feedback_buffer = []
        
        # 定期优化权重（可以按用户或全局）
        new_weights = self.weight_optimizer.optimize_weights(self.base_weights)
        self.base_weights = new_weights
        
        logger.info(f"权重已优化: {new_weights}")
    
    def _get_ground_truth_enhanced(self, user_id: int) -> List[str]:
        """
        增强的ground truth获取
        
        结合多种用户行为信号：
        - 高掌握度概念
        - 收藏的概念
        - 主动搜索的概念
        - 完课率高的概念
        """
        ground_truth = set()
        
        # 1. 高掌握度概念
        high_mastery = self.db.query(UserProgress).filter(
            UserProgress.user_id == user_id,
            UserProgress.mastery_level > 0.7
        ).all()
        ground_truth.update(p.concept_id for p in high_mastery)
        
        # 2. 最近学习的概念（假设有搜索历史表）
        # 这里简化处理，实际可以从搜索日志获取
        recent_activity = self.db.query(UserActivity).filter(
            UserActivity.user_id == user_id,
            UserActivity.activity_type.in_([
                "search_concept", "view_concept", "bookmark_concept"
            ])
        ).order_by(UserActivity.created_at.desc()).limit(20).all()
        
        for activity in recent_activity:
            metadata = activity.metadata or {}
            if "concept_id" in metadata:
                ground_truth.add(metadata["concept_id"])
        
        return list(ground_truth)
    
    def evaluate_recommender_enhanced(
        self,
        test_users: List[int],
        k_values: List[int] = [5, 10, 20]
    ) -> Dict[str, Any]:
        """
        增强的推荐系统评估
        
        包含更多指标和分析
        """
        results = {
            "precision": {},
            "recall": {},
            "ndcg": {},
            "diversity": {},
            "coverage": set(),
            "user_satisfaction": []
        }
        
        for k in k_values:
            precisions = []
            recalls = []
            ndcgs = []
            diversities = []
            
            for user_id in test_users:
                recs = self.recommend(user_id, n_recommendations=k)
                rec_concepts = [r.concept_id for r in recs]
                
                # 使用增强的ground truth
                actual_concepts = self._get_ground_truth_enhanced(user_id)
                
                if not actual_concepts:
                    continue
                
                # 基础指标
                hits = len(set(rec_concepts) & set(actual_concepts))
                precision = hits / k
                recall = hits / len(actual_concepts)
                
                precisions.append(precision)
                recalls.append(recall)
                
                # NDCG
                dcg = sum(1.0 / np.log2(i + 2) for i, c in enumerate(rec_concepts) if c in actual_concepts)
                idcg = sum(1.0 / np.log2(i + 2) for i in range(min(len(actual_concepts), k)))
                ndcg = dcg / idcg if idcg > 0 else 0
                ndcgs.append(ndcg)
                
                # 多样性（基于分支）
                branches = set()
                for r in recs:
                    concept = self.db.query(KnowledgeGraphNode).filter(
                        KnowledgeGraphNode.id == r.concept_id
                    ).first()
                    if concept:
                        branches.add(concept.branch)
                diversity = len(branches) / k if k > 0 else 0
                diversities.append(diversity)
                
                # 覆盖率
                results["coverage"].update(rec_concepts)
            
            results["precision"][f"@{k}"] = np.mean(precisions) if precisions else 0
            results["recall"][f"@{k}"] = np.mean(recalls) if recalls else 0
            results["ndcg"][f"@{k}"] = np.mean(ndcgs) if ndcgs else 0
            results["diversity"][f"@{k}"] = np.mean(diversities) if diversities else 0
        
        # 计算覆盖率
        total_concepts = self.db.query(KnowledgeGraphNode).count()
        results["coverage"] = len(results["coverage"]) / total_concepts if total_concepts > 0 else 0
        
        return results


# 保持向后兼容
def get_hybrid_recommender(db: Session) -> HybridRecommenderOptimized:
    """获取混合推荐器实例"""
    return HybridRecommenderOptimized(db)
