"""
强化学习推荐系统
- Multi-Armed Bandit算法 (UCB, Thompson Sampling)
- 上下文老虎机 (LinUCB)
- 长期收益优化
"""
import numpy as np
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, field
from collections import defaultdict
from sqlalchemy.orm import Session
import logging
from datetime import datetime, timedelta

from ..models.models import User, UserProgress, UserActivity, KnowledgeGraphNode

logger = logging.getLogger(__name__)


@dataclass
class ArmStatistics:
    """臂（选项）的统计信息"""
    arm_id: str
    n_pulls: int = 0
    total_reward: float = 0.0
    mean_reward: float = 0.0
    # 上下文相关
    context_sum: np.ndarray = field(default_factory=lambda: np.zeros(0))
    context_matrix: np.ndarray = field(default_factory=lambda: np.zeros((0, 0)))
    
    def update(self, reward: float, context: Optional[np.ndarray] = None):
        """更新统计信息"""
        self.n_pulls += 1
        self.total_reward += reward
        self.mean_reward = self.total_reward / self.n_pulls
        
        if context is not None and len(self.context_sum) > 0:
            self.context_sum += context
            self.context_matrix += np.outer(context, context)


class UCBRecommender:
    """
    Upper Confidence Bound (UCB) 算法
    平衡探索和利用
    """
    
    def __init__(self, c: float = 2.0):
        """
        Args:
            c: 探索参数，越大越倾向于探索
        """
        self.c = c
        self.arms: Dict[str, ArmStatistics] = {}
        self.total_pulls = 0
    
    def add_arm(self, arm_id: str):
        """添加臂"""
        if arm_id not in self.arms:
            self.arms[arm_id] = ArmStatistics(arm_id=arm_id)
    
    def select_arm(self) -> str:
        """选择臂 (UCB公式)"""
        if not self.arms:
            raise ValueError("没有可用的臂")
        
        # 从未被选择过的臂
        unexplored = [arm_id for arm_id, stats in self.arms.items() if stats.n_pulls == 0]
        if unexplored:
            return np.random.choice(unexplored)
        
        # UCB计算
        ucb_scores = {}
        for arm_id, stats in self.arms.items():
            exploitation = stats.mean_reward
            exploration = self.c * np.sqrt(np.log(self.total_pulls) / stats.n_pulls)
            ucb_scores[arm_id] = exploitation + exploration
        
        # 选择UCB分数最高的臂
        return max(ucb_scores, key=ucb_scores.get)
    
    def update(self, arm_id: str, reward: float):
        """更新臂的统计信息"""
        if arm_id in self.arms:
            self.arms[arm_id].update(reward)
            self.total_pulls += 1


class ThompsonSamplingRecommender:
    """
    Thompson Sampling 算法
    使用Beta分布进行贝叶斯推断
    """
    
    def __init__(self):
        self.arms: Dict[str, Tuple[float, float]] = {}  # (alpha, beta)
    
    def add_arm(self, arm_id: str, prior_alpha: float = 1.0, prior_beta: float = 1.0):
        """添加臂，使用Beta先验"""
        if arm_id not in self.arms:
            self.arms[arm_id] = (prior_alpha, prior_beta)
    
    def select_arm(self) -> str:
        """选择臂 (从Beta分布采样)"""
        if not self.arms:
            raise ValueError("没有可用的臂")
        
        samples = {}
        for arm_id, (alpha, beta) in self.arms.items():
            samples[arm_id] = np.random.beta(alpha, beta)
        
        return max(samples, key=samples.get)
    
    def update(self, arm_id: str, reward: float):
        """更新Beta分布参数"""
        if arm_id in self.arms:
            alpha, beta = self.arms[arm_id]
            # 假设reward在[0,1]之间
            if reward > 0.5:
                self.arms[arm_id] = (alpha + 1, beta)
            else:
                self.arms[arm_id] = (alpha, beta + 1)


class LinUCBRecommender:
    """
    Linear UCB (上下文老虎机)
    考虑用户上下文信息
    """
    
    def __init__(self, n_features: int, alpha: float = 1.0):
        """
        Args:
            n_features: 上下文特征维度
            alpha: 探索参数
        """
        self.n_features = n_features
        self.alpha = alpha
        self.arms: Dict[str, Dict] = {}
    
    def add_arm(self, arm_id: str):
        """添加臂，初始化LinUCB参数"""
        if arm_id not in self.arms:
            self.arms[arm_id] = {
                "A": np.eye(self.n_features),  # 设计矩阵
                "b": np.zeros(self.n_features),  # 响应向量
                "theta": np.zeros(self.n_features),  # 参数估计
            }
    
    def select_arm(self, context: np.ndarray) -> Tuple[str, float]:
        """
        选择臂
        
        Args:
            context: 上下文特征向量
        
        Returns:
            (选择的臂ID, 期望奖励)
        """
        if not self.arms:
            raise ValueError("没有可用的臂")
        
        p_values = {}
        for arm_id, params in self.arms.items():
            A_inv = np.linalg.inv(params["A"])
            theta = A_inv @ params["b"]
            
            # 期望奖励
            mean_reward = context @ theta
            
            # 置信区间
            std = np.sqrt(context @ A_inv @ context)
            
            # UCB分数
            p_values[arm_id] = mean_reward + self.alpha * std
        
        best_arm = max(p_values, key=p_values.get)
        return best_arm, p_values[best_arm]
    
    def update(self, arm_id: str, context: np.ndarray, reward: float):
        """更新臂的参数"""
        if arm_id in self.arms:
            self.arms[arm_id]["A"] += np.outer(context, context)
            self.arms[arm_id]["b"] += reward * context


class RLRecommender:
    """
    强化学习推荐器主类
    整合多种Bandit算法
    """
    
    def __init__(self, db: Session, algorithm: str = "linucb"):
        self.db = db
        self.algorithm = algorithm
        self.recommender = None
        self.concept_features = {}
        self.user_context_cache = {}
        
    def initialize(self, n_features: int = 10):
        """初始化推荐器"""
        if self.algorithm == "ucb":
            self.recommender = UCBRecommender(c=2.0)
        elif self.algorithm == "thompson":
            self.recommender = ThompsonSamplingRecommender()
        elif self.algorithm == "linucb":
            self.recommender = LinUCBRecommender(n_features=n_features, alpha=1.0)
        else:
            raise ValueError(f"不支持的算法: {self.algorithm}")
        
        # 加载所有概念作为臂
        concepts = self.db.query(KnowledgeGraphNode).all()
        for concept in concepts:
            if self.algorithm == "linucb":
                self.recommender.add_arm(concept.id)
            else:
                self.recommender.add_arm(concept.id)
        
        # 预计算概念特征
        self._precompute_concept_features()
        
        logger.info(f"RL推荐器初始化完成，算法: {self.algorithm}，共{len(concepts)}个臂")
    
    def _precompute_concept_features(self):
        """预计算概念特征向量"""
        concepts = self.db.query(KnowledgeGraphNode).all()
        
        # 构建分支编码
        branches = list(set(c.branch for c in concepts))
        branch_to_idx = {b: i for i, b in enumerate(branches)}
        
        for concept in concepts:
            # 特征: [难度编码, 分支独热编码, 前置概念数量, 平均掌握程度]
            difficulty_map = {"basic": 0, "intermediate": 1, "advanced": 2, "research": 3}
            difficulty_val = difficulty_map.get(concept.difficulty.value, 1)
            
            branch_onehot = np.zeros(len(branches))
            branch_onehot[branch_to_idx[concept.branch]] = 1
            
            prereq_count = len(concept.prerequisites) if concept.prerequisites else 0
            
            # 获取该概念的平均掌握程度
            avg_mastery = self.db.query(UserProgress).filter(
                UserProgress.concept_id == concept.id
            ).with_entities(func.avg(UserProgress.mastery_level)).scalar() or 0.5
            
            features = np.concatenate([
                [difficulty_val / 3.0, prereq_count / 10.0, avg_mastery],
                branch_onehot
            ])
            
            self.concept_features[concept.id] = features
    
    def get_user_context(self, user_id: int) -> np.ndarray:
        """获取用户上下文特征"""
        if user_id in self.user_context_cache:
            return self.user_context_cache[user_id]
        
        # 获取用户学习历史
        progress = self.db.query(UserProgress).filter(
            UserProgress.user_id == user_id
        ).all()
        
        if not progress:
            # 新用户，返回默认上下文
            context = np.zeros(len(self.concept_features.get(list(self.concept_features.keys())[0], [])))
            context[-1] = 1  # 默认分支
            return context
        
        # 构建用户特征
        avg_mastery = np.mean([p.mastery_level for p in progress])
        total_study_time = sum([p.study_time for p in progress])
        success_rate = sum([p.successes for p in progress]) / max(sum([p.attempts for p in progress]), 1)
        
        # 用户偏好分支
        branch_counts = defaultdict(int)
        for p in progress:
            concept = self.db.query(KnowledgeGraphNode).filter(
                KnowledgeGraphNode.id == p.concept_id
            ).first()
            if concept:
                branch_counts[concept.branch] += 1
        
        preferred_branch = max(branch_counts, key=branch_counts.get) if branch_counts else "algebra"
        
        context = np.array([
            avg_mastery,
            np.log1p(total_study_time) / 10.0,
            success_rate,
            len(progress) / 100.0
        ])
        
        self.user_context_cache[user_id] = context
        return context
    
    def recommend(
        self,
        user_id: int,
        n_recommendations: int = 5,
        available_concepts: Optional[List[str]] = None
    ) -> List[Dict[str, Any]]:
        """
        生成推荐
        
        Args:
            user_id: 用户ID
            n_recommendations: 推荐数量
            available_concepts: 可选概念列表
        
        Returns:
            推荐列表
        """
        if self.recommender is None:
            self.initialize()
        
        # 获取用户上下文
        context = self.get_user_context(user_id)
        
        # 获取已学习的概念
        studied = self.db.query(UserProgress.concept_id).filter(
            UserProgress.user_id == user_id
        ).all()
        studied_ids = {s[0] for s in studied}
        
        # 选择臂
        recommendations = []
        attempts = 0
        max_attempts = n_recommendations * 3
        
        while len(recommendations) < n_recommendations and attempts < max_attempts:
            attempts += 1
            
            if self.algorithm == "linucb":
                arm_id, expected_reward = self.recommender.select_arm(context)
            else:
                arm_id = self.recommender.select_arm()
                expected_reward = self.recommender.arms[arm_id].mean_reward
            
            # 检查是否已学习
            if arm_id in studied_ids:
                continue
            
            # 检查是否在可用列表中
            if available_concepts and arm_id not in available_concepts:
                continue
            
            # 获取概念详情
            concept = self.db.query(KnowledgeGraphNode).filter(
                KnowledgeGraphNode.id == arm_id
            ).first()
            
            if concept:
                recommendations.append({
                    "concept_id": arm_id,
                    "name": concept.name,
                    "branch": concept.branch,
                    "expected_reward": float(expected_reward),
                    "reason": f"RL {self.algorithm} 推荐 (探索vs利用平衡)"
                })
        
        return recommendations
    
    def feedback(
        self,
        user_id: int,
        concept_id: str,
        reward: float,
        context: Optional[np.ndarray] = None
    ):
        """
        接收反馈并更新模型
        
        Args:
            user_id: 用户ID
            concept_id: 概念ID
            reward: 奖励值 [0, 1]
            context: 上下文（可选）
        """
        if self.recommender is None:
            return
        
        if context is None:
            context = self.get_user_context(user_id)
        
        if self.algorithm == "linucb":
            self.recommender.update(concept_id, context, reward)
        else:
            self.recommender.update(concept_id, reward)
        
        # 记录反馈
        logger.debug(f"用户{user_id}对{concept_id}的反馈: {reward}")
    
    def calculate_reward(
        self,
        user_id: int,
        concept_id: str,
        action: str,
        metrics: Dict[str, Any]
    ) -> float:
        """
        计算奖励值
        
        奖励组成：
        - 学习完成度 (0.4)
        - 掌握程度提升 (0.3)
        - 学习时间 (0.2)
        - 互动次数 (0.1)
        """
        reward = 0.0
        
        if action == "complete":
            reward += 0.4
        
        if "mastery_gain" in metrics:
            reward += metrics["mastery_gain"] * 0.3
        
        if "study_time" in metrics:
            # 假设30分钟为理想学习时间
            time_score = min(metrics["study_time"] / 30.0, 1.0)
            reward += time_score * 0.2
        
        if "interactions" in metrics:
            reward += min(metrics["interactions"] / 10.0, 1.0) * 0.1
        
        return min(reward, 1.0)


# 从sqlalchemy导入func
from sqlalchemy import func
