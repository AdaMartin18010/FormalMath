"""
自适应内容推荐引擎
基于多维度特征的智能内容推荐
"""
import numpy as np
from typing import Dict, List, Optional, Tuple, Any, Set
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from collections import defaultdict
import heapq


@dataclass
class ContentItem:
    """内容项"""
    id: str
    concept_id: str
    content_type: str  # video, text, exercise, interactive
    difficulty: float
    duration: int  # 分钟
    
    # 内容特征
    features: Dict[str, float] = field(default_factory=dict)
    
    # 元数据
    quality_score: float = 0.5
    popularity: float = 0.0
    created_at: Optional[datetime] = None
    tags: List[str] = field(default_factory=list)
    
    def to_vector(self, feature_dims: List[str]) -> np.ndarray:
        """转换为特征向量"""
        return np.array([self.features.get(dim, 0) for dim in feature_dims])


@dataclass
class UserPreference:
    """用户偏好"""
    user_id: str
    
    # 内容类型偏好
    content_type_weights: Dict[str, float] = field(default_factory=dict)
    
    # 难度偏好
    preferred_difficulty_range: Tuple[float, float] = (0.3, 0.7)
    
    # 时长偏好（分钟）
    preferred_duration_range: Tuple[int, int] = (10, 30)
    
    # 特征偏好向量
    feature_preferences: Dict[str, float] = field(default_factory=dict)
    
    # 交互历史
    positive_items: Set[str] = field(default_factory=set)
    negative_items: Set[str] = field(default_factory=set)
    
    def update_from_interaction(self, item_id: str, feedback: float):
        """根据交互更新偏好"""
        if feedback > 0.5:
            self.positive_items.add(item_id)
            self.negative_items.discard(item_id)
        else:
            self.negative_items.add(item_id)
            self.positive_items.discard(item_id)


@dataclass
class RecommendationResult:
    """推荐结果"""
    item: ContentItem
    score: float
    reasons: List[str] = field(default_factory=list)
    
    def to_dict(self) -> Dict:
        return {
            'item_id': self.item.id,
            'concept_id': self.item.concept_id,
            'content_type': self.item.content_type,
            'difficulty': self.item.difficulty,
            'duration': self.item.duration,
            'score': self.score,
            'reasons': self.reasons
        }


class ContentRecommender:
    """
    内容推荐器
    
    结合协同过滤、内容基于和知识感知的多策略推荐
    """
    
    def __init__(self):
        self.content_items: Dict[str, ContentItem] = {}
        self.user_preferences: Dict[str, UserPreference] = {}
        
        # 用户-物品交互矩阵
        self.interaction_matrix: Dict[str, Dict[str, float]] = defaultdict(dict)
        
        # 相似度缓存
        self.item_similarity_cache: Dict[Tuple[str, str], float] = {}
        self.user_similarity_cache: Dict[Tuple[str, str], float] = {}
        
        # 特征维度
        self.feature_dimensions = [
            'visual_density',      # 视觉密度
            'interactivity',       # 交互性
            'abstraction_level',   # 抽象程度
            'practical_focus',     # 实践导向
            'depth',              # 内容深度
            'pace'                # 节奏
        ]
    
    def add_content(self, item: ContentItem):
        """添加内容"""
        self.content_items[item.id] = item
    
    def get_or_create_preference(self, user_id: str) -> UserPreference:
        """获取或创建用户偏好"""
        if user_id not in self.user_preferences:
            self.user_preferences[user_id] = UserPreference(user_id=user_id)
        return self.user_preferences[user_id]
    
    def record_interaction(
        self,
        user_id: str,
        item_id: str,
        feedback: float,  # 0-1
        interaction_type: str = 'view'
    ):
        """
        记录用户交互
        
        Args:
            user_id: 用户ID
            item_id: 内容ID
            feedback: 反馈分数 0-1
            interaction_type: 交互类型
        """
        # 根据交互类型调整反馈权重
        weights = {
            'view': 0.2,
            'complete': 0.5,
            'like': 0.8,
            'save': 0.9,
            'share': 1.0,
            'exercise_correct': 1.0,
            'exercise_incorrect': 0.1
        }
        
        adjusted_feedback = feedback * weights.get(interaction_type, 0.5)
        
        # 更新交互矩阵
        self.interaction_matrix[user_id][item_id] = adjusted_feedback
        
        # 更新用户偏好
        preference = self.get_or_create_preference(user_id)
        preference.update_from_interaction(item_id, adjusted_feedback)
        
        # 更新内容类型偏好
        if item_id in self.content_items:
            item = self.content_items[item_id]
            content_type = item.content_type
            
            # 指数移动平均更新
            current_weight = preference.content_type_weights.get(content_type, 0.5)
            alpha = 0.2
            preference.content_type_weights[content_type] = (
                alpha * adjusted_feedback + (1 - alpha) * current_weight
            )
    
    def calculate_item_similarity(
        self,
        item_a: ContentItem,
        item_b: ContentItem
    ) -> float:
        """
        计算内容相似度
        
        结合特征相似度和内容类型
        """
        cache_key = tuple(sorted([item_a.id, item_b.id]))
        if cache_key in self.item_similarity_cache:
            return self.item_similarity_cache[cache_key]
        
        # 特征余弦相似度
        vec_a = item_a.to_vector(self.feature_dimensions)
        vec_b = item_b.to_vector(self.feature_dimensions)
        
        norm_a = np.linalg.norm(vec_a)
        norm_b = np.linalg.norm(vec_b)
        
        if norm_a == 0 or norm_b == 0:
            feature_sim = 0
        else:
            feature_sim = np.dot(vec_a, vec_b) / (norm_a * norm_b)
        
        # 类型相似度
        type_sim = 1.0 if item_a.content_type == item_b.content_type else 0.3
        
        # 难度相似度
        diff_sim = 1 - abs(item_a.difficulty - item_b.difficulty)
        
        # 标签Jaccard相似度
        if item_a.tags and item_b.tags:
            intersection = len(set(item_a.tags) & set(item_b.tags))
            union = len(set(item_a.tags) | set(item_b.tags))
            tag_sim = intersection / union if union > 0 else 0
        else:
            tag_sim = 0
        
        # 加权综合
        similarity = (
            0.35 * feature_sim +
            0.25 * type_sim +
            0.25 * diff_sim +
            0.15 * tag_sim
        )
        
        self.item_similarity_cache[cache_key] = similarity
        return similarity
    
    def calculate_user_similarity(self, user_a: str, user_b: str) -> float:
        """
        计算用户相似度（基于交互历史）
        """
        cache_key = tuple(sorted([user_a, user_b]))
        if cache_key in self.user_similarity_cache:
            return self.user_similarity_cache[cache_key]
        
        # 获取共同交互的物品
        items_a = set(self.interaction_matrix[user_a].keys())
        items_b = set(self.interaction_matrix[user_b].keys())
        common_items = items_a & items_b
        
        if len(common_items) < 3:
            return 0.0
        
        # 计算评分的余弦相似度
        ratings_a = [self.interaction_matrix[user_a][item] for item in common_items]
        ratings_b = [self.interaction_matrix[user_b][item] for item in common_items]
        
        ratings_a = np.array(ratings_a)
        ratings_b = np.array(ratings_b)
        
        similarity = np.dot(ratings_a, ratings_b) / (
            np.linalg.norm(ratings_a) * np.linalg.norm(ratings_b) + 1e-8
        )
        
        self.user_similarity_cache[cache_key] = similarity
        return similarity
    
    def content_based_recommend(
        self,
        user_id: str,
        candidate_items: List[ContentItem],
        top_k: int = 5
    ) -> List[RecommendationResult]:
        """
        基于内容的推荐
        
        根据用户历史偏好推荐相似内容
        """
        preference = self.get_or_create_preference(user_id)
        
        if not preference.positive_items:
            # 无历史数据，返回热门内容
            return self._get_popular_items(candidate_items, top_k)
        
        # 获取用户喜欢的物品
        liked_items = [
            self.content_items[item_id]
            for item_id in preference.positive_items
            if item_id in self.content_items
        ]
        
        scores = []
        for candidate in candidate_items:
            if candidate.id in preference.positive_items:
                continue  # 已推荐过
            
            # 计算与用户喜欢物品的相似度
            similarities = [
                self.calculate_item_similarity(candidate, liked)
                for liked in liked_items
            ]
            
            # 取最大相似度作为分数
            score = max(similarities) if similarities else 0
            
            # 惩罚已不喜欢的
            if candidate.id in preference.negative_items:
                score *= 0.5
            
            scores.append((candidate, score))
        
        # 排序并返回top-k
        scores.sort(key=lambda x: x[1], reverse=True)
        
        return [
            RecommendationResult(
                item=item,
                score=score,
                reasons=['基于您喜欢的类似内容']
            )
            for item, score in scores[:top_k]
        ]
    
    def collaborative_recommend(
        self,
        user_id: str,
        candidate_items: List[ContentItem],
        top_k: int = 5,
        neighbor_count: int = 10
    ) -> List[RecommendationResult]:
        """
        协同过滤推荐
        
        基于相似用户的偏好
        """
        # 找到相似用户
        similarities = []
        for other_id in self.interaction_matrix.keys():
            if other_id == user_id:
                continue
            
            sim = self.calculate_user_similarity(user_id, other_id)
            if sim > 0:
                similarities.append((other_id, sim))
        
        # 取最相似的k个用户
        similarities.sort(key=lambda x: x[1], reverse=True)
        neighbors = similarities[:neighbor_count]
        
        if not neighbors:
            return []
        
        # 预测评分
        scores = []
        for candidate in candidate_items:
            weighted_sum = 0
            sim_sum = 0
            
            for neighbor_id, sim in neighbors:
                if candidate.id in self.interaction_matrix[neighbor_id]:
                    rating = self.interaction_matrix[neighbor_id][candidate.id]
                    weighted_sum += sim * rating
                    sim_sum += sim
            
            if sim_sum > 0:
                predicted_rating = weighted_sum / sim_sum
            else:
                predicted_rating = 0
            
            scores.append((candidate, predicted_rating))
        
        scores.sort(key=lambda x: x[1], reverse=True)
        
        return [
            RecommendationResult(
                item=item,
                score=score,
                reasons=['与您相似的用户喜欢']
            )
            for item, score in scores[:top_k]
        ]
    
    def knowledge_aware_recommend(
        self,
        user_id: str,
        candidate_items: List[ContentItem],
        knowledge_state: Optional[Dict] = None,
        target_concepts: Optional[List[str]] = None,
        top_k: int = 5
    ) -> List[RecommendationResult]:
        """
        知识感知推荐
        
        基于知识状态和学习目标
        """
        scores = []
        
        for item in candidate_items:
            score = 0.5  # 基础分
            reasons = []
            
            # 概念匹配
            if target_concepts and item.concept_id in target_concepts:
                score += 0.3
                reasons.append('符合学习目标')
            
            # 知识状态匹配
            if knowledge_state and item.concept_id in knowledge_state:
                mastery = knowledge_state[item.concept_id].get('mastery', 0)
                
                # 推荐掌握程度适中的内容（i+1原则）
                if 0.3 <= mastery < 0.7:
                    score += 0.25
                    reasons.append('适合当前掌握水平')
                elif mastery < 0.3:
                    score += 0.15  # 需要基础内容
                    reasons.append('巩固基础')
            
            # 前置知识检查（简化）
            # 假设有前置知识信息
            
            scores.append((item, score, reasons))
        
        scores.sort(key=lambda x: x[1], reverse=True)
        
        return [
            RecommendationResult(
                item=item,
                score=score,
                reasons=reasons
            )
            for item, score, reasons in scores[:top_k]
        ]
    
    def hybrid_recommend(
        self,
        user_id: str,
        concept_id: Optional[str] = None,
        content_types: Optional[List[str]] = None,
        difficulty_range: Optional[Tuple[float, float]] = None,
        duration_limit: Optional[int] = None,
        top_k: int = 5,
        strategy_weights: Optional[Dict[str, float]] = None
    ) -> List[RecommendationResult]:
        """
        混合推荐
        
        融合多种推荐策略
        """
        # 默认权重
        weights = strategy_weights or {
            'content_based': 0.35,
            'collaborative': 0.25,
            'knowledge_aware': 0.30,
            'diversity': 0.10
        }
        
        # 筛选候选内容
        candidates = self._filter_candidates(
            concept_id=concept_id,
            content_types=content_types,
            difficulty_range=difficulty_range,
            duration_limit=duration_limit,
            exclude_viewed=True,
            user_id=user_id
        )
        
        if not candidates:
            return []
        
        # 各策略推荐
        content_results = self.content_based_recommend(
            user_id, candidates, top_k * 2
        )
        collab_results = self.collaborative_recommend(
            user_id, candidates, top_k * 2
        )
        
        # 知识感知推荐（需要外部传入知识状态）
        knowledge_results = self.knowledge_aware_recommend(
            user_id, candidates, top_k=top_k * 2
        )
        
        # 合并分数
        item_scores: Dict[str, Tuple[ContentItem, float, Set[str]]] = {}
        
        # 加权合并
        for result, weight_key in [
            (content_results, 'content_based'),
            (collab_results, 'collaborative'),
            (knowledge_results, 'knowledge_aware')
        ]:
            for r in result:
                item_id = r.item.id
                weighted_score = r.score * weights[weight_key]
                
                if item_id in item_scores:
                    current_item, current_score, current_reasons = item_scores[item_id]
                    item_scores[item_id] = (
                        current_item,
                        current_score + weighted_score,
                        current_reasons | set(r.reasons)
                    )
                else:
                    item_scores[item_id] = (
                        r.item,
                        weighted_score,
                        set(r.reasons)
                    )
        
        # 转换为列表并排序
        merged = [
            (item, score, list(reasons))
            for item, score, reasons in item_scores.values()
        ]
        merged.sort(key=lambda x: x[1], reverse=True)
        
        # 多样性重排序
        if weights.get('diversity', 0) > 0:
            merged = self._diversity_rerank(merged, top_k)
        
        return [
            RecommendationResult(
                item=item,
                score=score,
                reasons=reasons
            )
            for item, score, reasons in merged[:top_k]
        ]
    
    def _filter_candidates(
        self,
        concept_id: Optional[str] = None,
        content_types: Optional[List[str]] = None,
        difficulty_range: Optional[Tuple[float, float]] = None,
        duration_limit: Optional[int] = None,
        exclude_viewed: bool = True,
        user_id: Optional[str] = None
    ) -> List[ContentItem]:
        """筛选候选内容"""
        candidates = []
        
        viewed_items = set()
        if exclude_viewed and user_id:
            viewed_items = set(self.interaction_matrix.get(user_id, {}).keys())
        
        for item in self.content_items.values():
            # 概念过滤
            if concept_id and item.concept_id != concept_id:
                continue
            
            # 类型过滤
            if content_types and item.content_type not in content_types:
                continue
            
            # 难度过滤
            if difficulty_range:
                min_diff, max_diff = difficulty_range
                if not (min_diff <= item.difficulty <= max_diff):
                    continue
            
            # 时长过滤
            if duration_limit and item.duration > duration_limit:
                continue
            
            # 排除已查看
            if item.id in viewed_items:
                continue
            
            candidates.append(item)
        
        return candidates
    
    def _diversity_rerank(
        self,
        items: List[Tuple[ContentItem, float, List[str]]],
        top_k: int
    ) -> List[Tuple[ContentItem, float, List[str]]]:
        """多样性重排序（MMR）"""
        if len(items) <= top_k:
            return items
        
        selected = []
        remaining = list(items)
        
        # 先选分数最高的
        remaining.sort(key=lambda x: x[1], reverse=True)
        selected.append(remaining.pop(0))
        
        lambda_param = 0.5  # 相关性vs多样性平衡
        
        while len(selected) < top_k and remaining:
            best_mmr_score = -float('inf')
            best_item = None
            best_idx = -1
            
            for idx, (item, relevance, reasons) in enumerate(remaining):
                # 计算与已选项目的最大相似度
                max_sim = max(
                    self.calculate_item_similarity(item, s[0])
                    for s in selected
                )
                
                # MMR分数
                mmr_score = lambda_param * relevance - (1 - lambda_param) * max_sim
                
                if mmr_score > best_mmr_score:
                    best_mmr_score = mmr_score
                    best_item = (item, relevance, reasons)
                    best_idx = idx
            
            if best_item:
                selected.append(best_item)
                remaining.pop(best_idx)
        
        return selected
    
    def _get_popular_items(
        self,
        candidates: List[ContentItem],
        top_k: int
    ) -> List[RecommendationResult]:
        """获取热门内容"""
        scored = [(item, item.popularity + item.quality_score) for item in candidates]
        scored.sort(key=lambda x: x[1], reverse=True)
        
        return [
            RecommendationResult(
                item=item,
                score=score,
                reasons=['热门推荐']
            )
            for item, score in scored[:top_k]
        ]
    
    def explain_recommendation(
        self,
        user_id: str,
        item_id: str
    ) -> Dict[str, Any]:
        """
        解释推荐原因
        """
        if item_id not in self.content_items:
            return {'error': 'Content not found'}
        
        item = self.content_items[item_id]
        preference = self.get_or_create_preference(user_id)
        
        explanations = {
            'item': {
                'id': item.id,
                'type': item.content_type,
                'difficulty': item.difficulty,
                'tags': item.tags
            },
            'reasons': [],
            'user_preferences': {}
        }
        
        # 内容类型偏好
        if item.content_type in preference.content_type_weights:
            weight = preference.content_type_weights[item.content_type]
            explanations['user_preferences']['content_type'] = {
                'type': item.content_type,
                'preference_score': weight
            }
            if weight > 0.7:
                explanations['reasons'].append(f'您偏好{item.content_type}类型的内容')
        
        # 相似内容
        similar_liked = []
        for liked_id in preference.positive_items:
            if liked_id in self.content_items:
                liked_item = self.content_items[liked_id]
                sim = self.calculate_item_similarity(item, liked_item)
                if sim > 0.6:
                    similar_liked.append((liked_id, sim))
        
        if similar_liked:
            similar_liked.sort(key=lambda x: x[1], reverse=True)
            explanations['reasons'].append(
                f'与您喜欢的内容 #{similar_liked[0][0]} 相似'
            )
        
        # 难度匹配
        min_pref, max_pref = preference.preferred_difficulty_range
        if min_pref <= item.difficulty <= max_pref:
            explanations['reasons'].append('难度符合您的偏好')
        
        return explanations


class RecommendationEngine:
    """
    推荐引擎（高层封装）
    
    整合认知模型和推荐算法
    """
    
    def __init__(
        self,
        knowledge_tracer=None,
        difficulty_manager=None,
        individual_model=None
    ):
        self.recommender = ContentRecommender()
        self.knowledge_tracer = knowledge_tracer
        self.difficulty_manager = difficulty_manager
        self.individual_model = individual_model
    
    def recommend_for_learning_session(
        self,
        user_id: str,
        session_duration: int = 30,
        target_concepts: Optional[List[str]] = None,
        focus_areas: Optional[List[str]] = None
    ) -> Dict[str, Any]:
        """
        为学习会话生成推荐
        
        Args:
            user_id: 用户ID
            session_duration: 会话时长（分钟）
            target_concepts: 目标概念
            focus_areas: 重点领域
        
        Returns:
            会话推荐计划
        """
        # 获取推荐难度
        recommended_difficulty = 0.5
        if self.difficulty_manager:
            recommended_difficulty = self.difficulty_manager.get_recommended_difficulty(
                user_id
            )
        
        # 获取知识状态
        knowledge_state = None
        if self.knowledge_tracer:
            knowledge_state = self.knowledge_tracer.knowledge_states
        
        # 难度范围
        difficulty_range = (
            max(0.1, recommended_difficulty - 0.15),
            min(1.0, recommended_difficulty + 0.15)
        )
        
        # 获取推荐
        recommendations = self.recommender.hybrid_recommend(
            user_id=user_id,
            concept_id=target_concepts[0] if target_concepts else None,
            difficulty_range=difficulty_range,
            duration_limit=session_duration,
            top_k=10
        )
        
        # 构建会话计划
        plan = {
            'user_id': user_id,
            'session_duration': session_duration,
            'recommended_difficulty': recommended_difficulty,
            'items': [],
            'total_estimated_duration': 0
        }
        
        current_duration = 0
        for rec in recommendations:
            if current_duration + rec.item.duration > session_duration:
                break
            
            plan['items'].append(rec.to_dict())
            current_duration += rec.item.duration
        
        plan['total_estimated_duration'] = current_duration
        plan['item_count'] = len(plan['items'])
        
        return plan
    
    def recommend_next_activity(
        self,
        user_id: str,
        current_concept: Optional[str] = None
    ) -> Optional[RecommendationResult]:
        """
        推荐下一个学习活动
        """
        # 获取推荐
        recommendations = self.recommender.hybrid_recommend(
            user_id=user_id,
            concept_id=current_concept,
            top_k=1
        )
        
        return recommendations[0] if recommendations else None
