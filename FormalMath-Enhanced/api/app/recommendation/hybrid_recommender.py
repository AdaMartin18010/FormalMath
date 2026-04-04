"""
混合推荐系统
- 多模型融合
- 可解释推荐
- A/B测试框架
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


class HybridRecommender:
    """
    混合推荐器
    整合多种推荐算法的结果
    """
    
    def __init__(self, db: Session):
        self.db = db
        self.recommenders = {}
        self.weights = {
            RecommenderType.COLLABORATIVE: 0.25,
            RecommenderType.KNOWLEDGE_GRAPH: 0.25,
            RecommenderType.REINFORCEMENT_LEARNING: 0.25,
            RecommenderType.CONTENT: 0.25
        }
        self.ab_test_assignments = {}
        
    def initialize_recommenders(self):
        """初始化所有推荐器"""
        logger.info("初始化混合推荐器...")
        
        # 协同过滤
        cf = CollaborativeFiltering(self.db)
        cf.build_user_item_matrix()
        cf.compute_user_similarity()
        cf.train_matrix_factorization()
        self.recommenders[RecommenderType.COLLABORATIVE] = cf
        
        # 知识图谱嵌入
        kg = KnowledgeGraphEmbedding(self.db, model_type="rotate")
        kg.build_model()
        # 这里可以选择加载预训练模型
        self.recommenders[RecommenderType.KNOWLEDGE_GRAPH] = kg
        
        # 强化学习
        rl = RLRecommender(self.db, algorithm="linucb")
        rl.initialize()
        self.recommenders[RecommenderType.REINFORCEMENT_LEARNING] = rl
        
        # 内容推荐
        content = ContentRecommender(self.db)
        self.recommenders[RecommenderType.CONTENT] = content
        
        logger.info("所有推荐器初始化完成")
    
    def set_weights(self, weights: Dict[RecommenderType, float]):
        """设置各推荐器的权重"""
        # 归一化权重
        total = sum(weights.values())
        self.weights = {k: v/total for k, v in weights.items()}
        logger.info(f"更新权重: {self.weights}")
    
    def recommend(
        self,
        user_id: int,
        n_recommendations: int = 10,
        context: Optional[Dict[str, Any]] = None
    ) -> List[RecommendationResult]:
        """
        生成混合推荐
        
        Args:
            user_id: 用户ID
            n_recommendations: 推荐数量
            context: 上下文信息
        
        Returns:
            推荐结果列表
        """
        if not self.recommenders:
            self.initialize_recommenders()
        
        # 收集所有推荐器的输出
        all_recommendations = defaultdict(lambda: {
            "scores": {},
            "info": None
        })
        
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
            # 加权融合
            final_score = 0.0
            component_scores = data["scores"]
            
            if "collaborative" in component_scores:
                final_score += self.weights[RecommenderType.COLLABORATIVE] * component_scores["collaborative"]
            if "knowledge_graph" in component_scores:
                final_score += self.weights[RecommenderType.KNOWLEDGE_GRAPH] * component_scores["knowledge_graph"]
            if "rl" in component_scores:
                final_score += self.weights[RecommenderType.REINFORCEMENT_LEARNING] * component_scores["rl"]
            if "content" in component_scores:
                final_score += self.weights[RecommenderType.CONTENT] * component_scores["content"]
            
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
                    explanation=self._generate_explanation(component_scores, concept),
                    confidence=float(confidence)
                )
                results.append(result)
        
        # 按最终分数排序
        results.sort(key=lambda x: x.final_score, reverse=True)
        return results[:n_recommendations]
    
    def _generate_explanation(self, component_scores: Dict[str, float], concept) -> str:
        """生成推荐解释"""
        explanations = []
        
        # 找出最强的推荐来源
        if component_scores:
            strongest = max(component_scores, key=component_scores.get)
            
            explanations_map = {
                "collaborative": f"与{component_scores['collaborative']:.0%}相似用户的学习路径匹配",
                "knowledge_graph": f"知识图谱语义相似度: {component_scores['knowledge_graph']:.2f}",
                "rl": f"强化学习预期收益: {component_scores['rl']:.2f}",
                "content": f"内容匹配度: {component_scores['content']:.2f}"
            }
            
            explanations.append(strongest)
            if strongest in explanations_map:
                explanations.append(explanations_map[strongest])
        
        # 添加难度信息
        if concept:
            explanations.append(f"难度: {concept.difficulty.value}")
        
        return " | ".join(explanations)
    
    def get_explainable_recommendation(
        self,
        user_id: int,
        concept_id: str
    ) -> Optional[Dict[str, Any]]:
        """
        获取单个推荐的可解释详情
        """
        recommendations = self.recommend(user_id, n_recommendations=50)
        
        for rec in recommendations:
            if rec.concept_id == concept_id:
                return {
                    "concept_id": rec.concept_id,
                    "name": rec.name,
                    "final_score": rec.final_score,
                    "component_breakdown": rec.component_scores,
                    "explanation": rec.explanation,
                    "confidence": rec.confidence,
                    "why_recommended": self._detailed_explanation(user_id, rec)
                }
        
        return None
    
    def _detailed_explanation(self, user_id: int, rec: RecommendationResult) -> str:
        """生成详细解释"""
        parts = []
        
        # 协同过滤解释
        if "collaborative" in rec.component_scores:
            cf = self.recommenders.get(RecommenderType.COLLABORATIVE)
            if cf:
                similar_users = cf.find_similar_users(user_id, k=3)
                if similar_users:
                    parts.append(f"与{len(similar_users)}位相似用户的学习兴趣匹配")
        
        # 知识图谱解释
        if "knowledge_graph" in rec.component_scores:
            kg = self.recommenders.get(RecommenderType.KNOWLEDGE_GRAPH)
            if kg:
                similar_concepts = kg.find_similar_concepts(rec.concept_id, top_k=3)
                if similar_concepts:
                    concept_names = [c["name"] for c in similar_concepts[:2]]
                    parts.append(f"与您已掌握的{'、'.join(concept_names)}概念相关")
        
        # 内容推荐解释
        if "content" in rec.component_scores:
            parts.append(f"适合您的{rec.component_scores['content']:.0%}难度水平")
        
        return "；".join(parts) if parts else "综合多维度匹配推荐"
    
    # ==================== A/B测试框架 ====================
    
    def ab_test_assign_group(self, user_id: int, test_name: str) -> str:
        """
        为A/B测试分配用户组
        
        使用一致性哈希确保同一用户始终在同一组
        """
        # 生成确定性分组
        hash_input = f"{test_name}:{user_id}"
        hash_value = int(hashlib.md5(hash_input.encode()).hexdigest(), 16)
        
        # 50/50分组
        group = "A" if hash_value % 2 == 0 else "B"
        
        # 记录
        if test_name not in self.ab_test_assignments:
            self.ab_test_assignments[test_name] = {"A": set(), "B": set()}
        self.ab_test_assignments[test_name][group].add(user_id)
        
        return group
    
    def recommend_with_ab_test(
        self,
        user_id: int,
        n_recommendations: int = 10,
        test_name: str = "default_test"
    ) -> Dict[str, Any]:
        """
        带A/B测试的推荐
        
        测试不同权重配置的效果
        """
        group = self.ab_test_assign_group(user_id, test_name)
        
        # A组: 均衡权重
        if group == "A":
            self.set_weights({
                RecommenderType.COLLABORATIVE: 0.25,
                RecommenderType.KNOWLEDGE_GRAPH: 0.25,
                RecommenderType.REINFORCEMENT_LEARNING: 0.25,
                RecommenderType.CONTENT: 0.25
            })
        # B组: 强调知识图谱
        else:
            self.set_weights({
                RecommenderType.COLLABORATIVE: 0.2,
                RecommenderType.KNOWLEDGE_GRAPH: 0.4,
                RecommenderType.REINFORCEMENT_LEARNING: 0.2,
                RecommenderType.CONTENT: 0.2
            })
        
        recommendations = self.recommend(user_id, n_recommendations)
        
        return {
            "recommendations": [
                {
                    "concept_id": r.concept_id,
                    "name": r.name,
                    "score": r.final_score,
                    "explanation": r.explanation
                }
                for r in recommendations
            ],
            "ab_test": {
                "test_name": test_name,
                "group": group,
                "weights": {k.value: v for k, v in self.weights.items()}
            }
        }
    
    def get_ab_test_results(self, test_name: str) -> Dict[str, Any]:
        """
        获取A/B测试结果统计
        """
        if test_name not in self.ab_test_assignments:
            return {"error": "测试不存在"}
        
        groups = self.ab_test_assignments[test_name]
        
        return {
            "test_name": test_name,
            "group_sizes": {
                "A": len(groups["A"]),
                "B": len(groups["B"])
            },
            "recommendations": {
                "A": "均衡权重配置",
                "B": "知识图谱强化配置"
            }
        }
    
    # ==================== 模型评估 ====================
    
    def evaluate_recommender(
        self,
        test_users: List[int],
        k_values: List[int] = [5, 10, 20]
    ) -> Dict[str, Any]:
        """
        评估推荐系统性能
        
        指标：
        - Precision@K
        - Recall@K
        - NDCG@K
        - 覆盖率
        """
        results = {
            "precision": {},
            "recall": {},
            "ndcg": {},
            "coverage": set()
        }
        
        for k in k_values:
            precisions = []
            recalls = []
            ndcgs = []
            
            for user_id in test_users:
                # 获取推荐
                recs = self.recommend(user_id, n_recommendations=k)
                rec_concepts = [r.concept_id for r in recs]
                
                # 获取用户实际学习的概念（模拟 ground truth）
                actual_concepts = self._get_ground_truth(user_id)
                
                if not actual_concepts:
                    continue
                
                # 计算指标
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
                
                # 覆盖率
                results["coverage"].update(rec_concepts)
            
            results["precision"][f"@{k}"] = np.mean(precisions) if precisions else 0
            results["recall"][f"@{k}"] = np.mean(recalls) if recalls else 0
            results["ndcg"][f"@{k}"] = np.mean(ndcgs) if ndcgs else 0
        
        # 计算覆盖率
        total_concepts = self.db.query(KnowledgeGraphNode).count()
        results["coverage"] = len(results["coverage"]) / total_concepts if total_concepts > 0 else 0
        
        return results
    
    def _get_ground_truth(self, user_id: int) -> List[str]:
        """获取用户的真实学习数据作为ground truth"""
        # 获取用户将要学习或计划学习的概念
        # 这里简化为获取低掌握度但已开始学习的概念
        progress = self.db.query(UserProgress).filter(
            UserProgress.user_id == user_id,
            UserProgress.mastery_level > 0,
            UserProgress.mastery_level < 0.9
        ).order_by(UserProgress.mastery_level.desc()).limit(20).all()
        
        return [p.concept_id for p in progress]
