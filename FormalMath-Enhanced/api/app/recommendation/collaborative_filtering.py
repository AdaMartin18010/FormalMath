"""
协同过滤推荐算法
- 基于用户相似度的学习路径推荐
- 矩阵分解算法 (SVD/NMF)
- 冷启动处理策略
"""
import numpy as np
import pandas as pd
from typing import Dict, List, Optional, Tuple, Any
from sqlalchemy.orm import Session
from sklearn.decomposition import NMF
from sklearn.metrics.pairwise import cosine_similarity
from scipy.sparse import csr_matrix
import logging
from datetime import datetime, timedelta

from ..models.models import User, LearningPath, UserProgress, KnowledgeGraphNode, UserActivity

logger = logging.getLogger(__name__)


class CollaborativeFiltering:
    """协同过滤推荐器"""
    
    def __init__(self, db: Session):
        self.db = db
        self.user_similarity_matrix = None
        self.item_similarity_matrix = None
        self.user_item_matrix = None
        self.nmf_model = None
        self.user_factors = None
        self.item_factors = None
        self.user_id_map = {}
        self.item_id_map = {}
        self.reverse_user_map = {}
        self.reverse_item_map = {}
        
    def build_user_item_matrix(self) -> csr_matrix:
        """
        构建用户-项目交互矩阵
        基于用户的学习进度和掌握程度
        """
        # 获取所有用户进度数据
        progresses = self.db.query(
            UserProgress.user_id,
            UserProgress.concept_id,
            UserProgress.mastery_level,
            UserProgress.study_time
        ).all()
        
        if not progresses:
            logger.warning("没有用户进度数据，无法构建矩阵")
            return csr_matrix((0, 0))
        
        # 创建用户和项目的映射
        user_ids = sorted(set(p.user_id for p in progresses))
        item_ids = sorted(set(p.concept_id for p in progresses))
        
        self.user_id_map = {uid: idx for idx, uid in enumerate(user_ids)}
        self.item_id_map = {iid: idx for idx, iid in enumerate(item_ids)}
        self.reverse_user_map = {v: k for k, v in self.user_id_map.items()}
        self.reverse_item_map = {v: k for k, v in self.item_id_map.items()}
        
        # 构建交互矩阵 (使用掌握程度和学习时间作为权重)
        rows = []
        cols = []
        data = []
        
        for p in progresses:
            user_idx = self.user_id_map[p.user_id]
            item_idx = self.item_id_map[p.concept_id]
            # 评分 = 掌握程度 * (1 + log(学习时间+1))
            score = p.mastery_level * (1 + np.log1p(p.study_time / 60))
            
            rows.append(user_idx)
            cols.append(item_idx)
            data.append(min(score, 5.0))  # 限制最大评分为5
        
        self.user_item_matrix = csr_matrix(
            (data, (rows, cols)),
            shape=(len(user_ids), len(item_ids))
        )
        
        logger.info(f"构建用户-项目矩阵: {self.user_item_matrix.shape}")
        return self.user_item_matrix
    
    def compute_user_similarity(self, k: int = 50) -> np.ndarray:
        """
        计算用户相似度矩阵
        
        Args:
            k: 保留的最近邻数量
        
        Returns:
            用户相似度矩阵
        """
        if self.user_item_matrix is None:
            self.build_user_item_matrix()
            
        if self.user_item_matrix.shape[0] == 0:
            return np.array([])
        
        # 计算余弦相似度
        similarity = cosine_similarity(self.user_item_matrix)
        
        # 保留Top-K相似用户
        for i in range(similarity.shape[0]):
            # 排除自身
            similarity[i, i] = 0
            # 获取Top-K索引
            top_k_idx = np.argsort(similarity[i])[-k:]
            # 保留Top-K，其他置0
            mask = np.zeros(similarity.shape[1], dtype=bool)
            mask[top_k_idx] = True
            similarity[i, ~mask] = 0
        
        self.user_similarity_matrix = similarity
        logger.info(f"计算用户相似度矩阵: {similarity.shape}")
        return similarity
    
    def train_matrix_factorization(self, n_components: int = 50, max_iter: int = 500):
        """
        训练矩阵分解模型 (NMF)
        
        Args:
            n_components: 隐因子维度
            max_iter: 最大迭代次数
        """
        if self.user_item_matrix is None:
            self.build_user_item_matrix()
            
        if self.user_item_matrix.shape[0] == 0 or self.user_item_matrix.shape[1] == 0:
            logger.warning("矩阵为空，无法训练")
            return
        
        # 转换为稠密矩阵进行NMF
        dense_matrix = self.user_item_matrix.toarray()
        
        # 使用NMF进行矩阵分解
        self.nmf_model = NMF(
            n_components=min(n_components, min(dense_matrix.shape) - 1),
            max_iter=max_iter,
            random_state=42,
            alpha_W=0.1,
            alpha_H=0.1
        )
        
        self.user_factors = self.nmf_model.fit_transform(dense_matrix)
        self.item_factors = self.nmf_model.components_.T
        
        logger.info(f"NMF训练完成: 用户因子{self.user_factors.shape}, 项目因子{self.item_factors.shape}")
    
    def recommend_for_user(
        self,
        user_id: int,
        n_recommendations: int = 10,
        method: str = "hybrid"
    ) -> List[Dict[str, Any]]:
        """
        为用户生成推荐
        
        Args:
            user_id: 用户ID
            n_recommendations: 推荐数量
            method: 推荐方法 (user_based/item_based/mf/hybrid)
        
        Returns:
            推荐列表，包含概念ID和预测分数
        """
        if user_id not in self.user_id_map:
            # 冷启动用户，使用基于内容的推荐
            return self._cold_start_recommendation(user_id, n_recommendations)
        
        user_idx = self.user_id_map[user_id]
        
        if method == "user_based":
            scores = self._user_based_predict(user_idx)
        elif method == "item_based":
            scores = self._item_based_predict(user_idx)
        elif method == "mf":
            scores = self._mf_predict(user_idx)
        else:  # hybrid
            scores = self._hybrid_predict(user_idx)
        
        # 获取用户已学习的概念
        user_progress = self.db.query(UserProgress.concept_id).filter(
            UserProgress.user_id == user_id
        ).all()
        studied_concepts = {p.concept_id for p in user_progress}
        
        # 过滤已学习的概念并排序
        recommendations = []
        for item_idx, score in enumerate(scores):
            concept_id = self.reverse_item_map.get(item_idx)
            if concept_id and concept_id not in studied_concepts:
                recommendations.append({
                    "concept_id": concept_id,
                    "score": float(score),
                    "reason": f"协同过滤推荐 (相似度: {score:.3f})"
                })
        
        # 按分数排序并返回Top-N
        recommendations.sort(key=lambda x: x["score"], reverse=True)
        return recommendations[:n_recommendations]
    
    def _user_based_predict(self, user_idx: int) -> np.ndarray:
        """基于用户的协同过滤预测"""
        if self.user_similarity_matrix is None:
            self.compute_user_similarity()
        
        # 预测评分 = 相似用户的加权平均
        similarity_vector = self.user_similarity_matrix[user_idx]
        predictions = similarity_vector @ self.user_item_matrix.toarray()
        
        # 归一化
        similarity_sum = np.sum(similarity_vector)
        if similarity_sum > 0:
            predictions = predictions / similarity_sum
        
        return predictions
    
    def _item_based_predict(self, user_idx: int) -> np.ndarray:
        """基于项目的协同过滤预测"""
        if self.item_similarity_matrix is None:
            # 计算项目相似度
            item_matrix = self.user_item_matrix.T
            self.item_similarity_matrix = cosine_similarity(item_matrix)
        
        # 获取用户的交互向量
        user_vector = self.user_item_matrix[user_idx].toarray().flatten()
        
        # 预测评分
        predictions = self.item_similarity_matrix @ user_vector
        
        return predictions
    
    def _mf_predict(self, user_idx: int) -> np.ndarray:
        """基于矩阵分解的预测"""
        if self.user_factors is None:
            self.train_matrix_factorization()
        
        if self.user_factors is None:
            return np.zeros(len(self.item_id_map))
        
        # 预测评分 = 用户因子 @ 项目因子.T
        predictions = self.user_factors[user_idx] @ self.item_factors.T
        return predictions
    
    def _hybrid_predict(self, user_idx: int, weights: Dict[str, float] = None) -> np.ndarray:
        """混合预测，融合多种方法"""
        if weights is None:
            weights = {"user_based": 0.3, "item_based": 0.3, "mf": 0.4}
        
        predictions = np.zeros(len(self.item_id_map))
        
        if weights.get("user_based", 0) > 0:
            predictions += weights["user_based"] * self._user_based_predict(user_idx)
        
        if weights.get("item_based", 0) > 0:
            predictions += weights["item_based"] * self._item_based_predict(user_idx)
        
        if weights.get("mf", 0) > 0:
            predictions += weights["mf"] * self._mf_predict(user_idx)
        
        return predictions
    
    def _cold_start_recommendation(
        self,
        user_id: int,
        n_recommendations: int
    ) -> List[Dict[str, Any]]:
        """
        冷启动用户推荐策略
        
        策略：
        1. 基于用户初始选择的兴趣领域
        2. 基于热门概念
        3. 基于基础概念
        """
        recommendations = []
        
        # 1. 获取用户活动记录分析兴趣
        activities = self.db.query(UserActivity).filter(
            UserActivity.user_id == user_id
        ).order_by(UserActivity.created_at.desc()).limit(50).all()
        
        interested_branches = set()
        for activity in activities:
            if activity.metadata and "branch" in activity.metadata:
                interested_branches.add(activity.metadata["branch"])
        
        # 2. 基于兴趣领域推荐
        if interested_branches:
            concepts = self.db.query(KnowledgeGraphNode).filter(
                KnowledgeGraphNode.branch.in_(interested_branches),
                KnowledgeGraphNode.difficulty == "basic"
            ).limit(n_recommendations // 2).all()
            
            for concept in concepts:
                recommendations.append({
                    "concept_id": concept.id,
                    "score": 0.8,
                    "reason": f"基于您感兴趣的{concept.branch}领域推荐的基础概念"
                })
        
        # 3. 补充热门概念
        popular_concepts = self._get_popular_concepts(
            n_recommendations - len(recommendations)
        )
        recommendations.extend(popular_concepts)
        
        return recommendations[:n_recommendations]
    
    def _get_popular_concepts(self, n: int) -> List[Dict[str, Any]]:
        """获取热门学习概念"""
        from sqlalchemy import func
        
        # 统计每个概念的学习人数
        popular = self.db.query(
            UserProgress.concept_id,
            func.count(UserProgress.user_id).label("user_count"),
            func.avg(UserProgress.mastery_level).label("avg_mastery")
        ).group_by(UserProgress.concept_id).order_by(
            func.count(UserProgress.user_id).desc()
        ).limit(n).all()
        
        recommendations = []
        for p in popular:
            score = min(p.user_count / 100, 1.0) * 0.5 + p.avg_mastery * 0.5
            recommendations.append({
                "concept_id": p.concept_id,
                "score": float(score),
                "reason": f"热门概念 ({p.user_count}人正在学习)"
            })
        
        return recommendations
    
    def find_similar_users(self, user_id: int, k: int = 10) -> List[Dict[str, Any]]:
        """
        找到与指定用户最相似的K个用户
        
        Returns:
            相似用户列表，包含用户ID和相似度分数
        """
        if user_id not in self.user_id_map:
            return []
        
        if self.user_similarity_matrix is None:
            self.compute_user_similarity(k=k)
        
        user_idx = self.user_id_map[user_id]
        similarity_vector = self.user_similarity_matrix[user_idx]
        
        # 获取Top-K相似用户
        top_k_idx = np.argsort(similarity_vector)[-k:][::-1]
        
        similar_users = []
        for idx in top_k_idx:
            if similarity_vector[idx] > 0:
                similar_users.append({
                    "user_id": self.reverse_user_map[idx],
                    "similarity": float(similarity_vector[idx])
                })
        
        return similar_users
    
    def evaluate_model(self, test_ratio: float = 0.2) -> Dict[str, float]:
        """
        评估模型性能
        
        Returns:
            包含各种评估指标的字典
        """
        from sklearn.metrics import mean_squared_error, mean_absolute_error
        
        if self.user_item_matrix is None:
            self.build_user_item_matrix()
        
        # 将矩阵转换为DataFrame以便进行训练/测试分割
        dense_matrix = self.user_item_matrix.toarray()
        
        # 创建掩码进行训练/测试分割
        mask = np.random.random(dense_matrix.shape) > test_ratio
        
        train_matrix = dense_matrix.copy()
        train_matrix[~mask] = 0
        
        test_matrix = dense_matrix.copy()
        test_matrix[mask] = 0
        
        # 训练NMF模型
        nmf = NMF(n_components=50, max_iter=300, random_state=42)
        user_factors = nmf.fit_transform(train_matrix)
        item_factors = nmf.components_.T
        
        # 预测
        predictions = user_factors @ item_factors.T
        
        # 只在测试集上评估
        test_mask = test_matrix > 0
        if np.sum(test_mask) == 0:
            return {"error": "测试集为空"}
        
        y_true = test_matrix[test_mask]
        y_pred = np.clip(predictions[test_mask], 0, 5)
        
        rmse = np.sqrt(mean_squared_error(y_true, y_pred))
        mae = mean_absolute_error(y_true, y_pred)
        
        return {
            "rmse": float(rmse),
            "mae": float(mae),
            "test_samples": int(np.sum(test_mask))
        }
