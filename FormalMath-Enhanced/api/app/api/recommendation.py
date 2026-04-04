"""
推荐系统API
提供个性化推荐服务
"""
from fastapi import APIRouter, Depends, HTTPException, Query, BackgroundTasks
from sqlalchemy.orm import Session
from pydantic import BaseModel, Field
from typing import List, Optional, Dict, Any
from enum import Enum

from ..core.database import get_db
from ..core.config import settings
from ..cache.redis_cache import cache, cache_evict
from ..recommendation import (
    CollaborativeFiltering,
    KnowledgeGraphEmbedding,
    RLRecommender,
    ContentRecommender,
    HybridRecommender
)

router = APIRouter()


class RecommendationType(str, Enum):
    """推荐类型"""
    COLLABORATIVE = "collaborative"
    KNOWLEDGE_GRAPH = "knowledge_graph"
    REINFORCEMENT_LEARNING = "reinforcement_learning"
    CONTENT = "content"
    HYBRID = "hybrid"


class RecommendationRequest(BaseModel):
    """推荐请求"""
    user_id: int = Field(..., description="用户ID")
    n_recommendations: int = Field(default=10, ge=1, le=50, description="推荐数量")
    recommendation_type: RecommendationType = Field(
        default=RecommendationType.HYBRID, 
        description="推荐类型"
    )
    context: Optional[Dict[str, Any]] = Field(default=None, description="上下文信息")


class RecommendationItem(BaseModel):
    """推荐项"""
    concept_id: str
    name: str
    branch: str
    score: float
    explanation: str
    confidence: Optional[float] = None
    component_scores: Optional[Dict[str, float]] = None


class RecommendationResponse(BaseModel):
    """推荐响应"""
    user_id: int
    recommendations: List[RecommendationItem]
    total_count: int
    recommendation_type: str
    ab_test_group: Optional[str] = None


class FeedbackRequest(BaseModel):
    """反馈请求"""
    user_id: int = Field(..., description="用户ID")
    concept_id: str = Field(..., description="概念ID")
    reward: float = Field(..., ge=0, le=1, description="奖励值 0-1")
    action: str = Field(default="study", description="用户行为")
    metrics: Optional[Dict[str, Any]] = Field(default=None, description="详细指标")


class SimilarUsersRequest(BaseModel):
    """相似用户请求"""
    user_id: int = Field(..., description="用户ID")
    k: int = Field(default=10, ge=1, le=50, description="相似用户数量")


class SimilarUsersResponse(BaseModel):
    """相似用户响应"""
    user_id: int
    similar_users: List[Dict[str, Any]]


class ABTestConfig(BaseModel):
    """A/B测试配置"""
    test_name: str = Field(..., description="测试名称")
    user_id: int = Field(..., description="用户ID")


class ABTestResponse(BaseModel):
    """A/B测试响应"""
    test_name: str
    group: str
    recommendations: List[RecommendationItem]
    weights: Dict[str, float]


# ============ API端点 ============

@router.post("/recommend", response_model=RecommendationResponse)
async def get_recommendations(
    request: RecommendationRequest,
    db: Session = Depends(get_db)
):
    """
    获取个性化推荐
    
    支持多种推荐算法：
    - **collaborative**: 协同过滤
    - **knowledge_graph**: 知识图谱嵌入
    - **reinforcement_learning**: 强化学习
    - **content**: 内容推荐
    - **hybrid**: 混合推荐（默认）
    """
    # 尝试从缓存获取
    cache_key = f"rec:{request.user_id}:{request.recommendation_type.value}:{request.n_recommendations}"
    cached_result = await cache.get(cache_key, prefix="recommendation")
    
    if cached_result:
        return RecommendationResponse(**cached_result)
    
    # 根据推荐类型选择算法
    if request.recommendation_type == RecommendationType.COLLABORATIVE:
        recommender = CollaborativeFiltering(db)
        recommender.build_user_item_matrix()
        recommender.compute_user_similarity()
        recommender.train_matrix_factorization()
        
        raw_recs = recommender.recommend_for_user(
            request.user_id, 
            request.n_recommendations,
            method="hybrid"
        )
        
        recommendations = [
            RecommendationItem(
                concept_id=rec["concept_id"],
                name=rec.get("name", rec["concept_id"]),
                branch=rec.get("branch", "unknown"),
                score=rec["score"],
                explanation=rec.get("reason", "协同过滤推荐")
            )
            for rec in raw_recs
        ]
    
    elif request.recommendation_type == RecommendationType.KNOWLEDGE_GRAPH:
        kg = KnowledgeGraphEmbedding(db)
        kg.load_knowledge_graph()
        kg.build_model()
        
        raw_recs = kg.recommend_by_knowledge_graph(
            request.user_id,
            request.n_recommendations
        )
        
        recommendations = [
            RecommendationItem(
                concept_id=rec["concept_id"],
                name=rec["name"],
                branch=rec["branch"],
                score=rec["score"],
                explanation=rec["reason"]
            )
            for rec in raw_recs
        ]
    
    elif request.recommendation_type == RecommendationType.REINFORCEMENT_LEARNING:
        rl = RLRecommender(db)
        rl.initialize()
        
        raw_recs = rl.recommend(
            request.user_id,
            request.n_recommendations
        )
        
        recommendations = [
            RecommendationItem(
                concept_id=rec["concept_id"],
                name=rec["name"],
                branch=rec["branch"],
                score=rec.get("expected_reward", 0.5),
                explanation=rec["reason"]
            )
            for rec in raw_recs
        ]
    
    elif request.recommendation_type == RecommendationType.CONTENT:
        content = ContentRecommender(db)
        raw_recs = content.recommend(
            request.user_id,
            request.n_recommendations,
            strategy="hybrid"
        )
        
        recommendations = [
            RecommendationItem(
                concept_id=rec["concept_id"],
                name=rec.get("name", rec["concept_id"]),
                branch=rec.get("branch", "unknown"),
                score=rec["score"],
                explanation=rec["reason"]
            )
            for rec in raw_recs
        ]
    
    else:  # HYBRID
        hybrid = HybridRecommender(db)
        hybrid.initialize_recommenders()
        
        raw_recs = hybrid.recommend(
            request.user_id,
            request.n_recommendations
        )
        
        recommendations = [
            RecommendationItem(
                concept_id=rec.concept_id,
                name=rec.name,
                branch=rec.branch,
                score=rec.final_score,
                explanation=rec.explanation,
                confidence=rec.confidence,
                component_scores=rec.component_scores
            )
            for rec in raw_recs
        ]
    
    result = RecommendationResponse(
        user_id=request.user_id,
        recommendations=recommendations,
        total_count=len(recommendations),
        recommendation_type=request.recommendation_type.value
    )
    
    # 缓存结果
    await cache.set(cache_key, result.dict(), ttl=300, prefix="recommendation")
    
    return result


@router.post("/recommend/ab-test", response_model=ABTestResponse)
async def recommend_with_ab_test(
    config: ABTestConfig,
    n_recommendations: int = Query(default=10, ge=1, le=50),
    db: Session = Depends(get_db)
):
    """
    A/B测试推荐
    
    将用户分配到不同测试组，测试不同推荐策略的效果
    """
    hybrid = HybridRecommender(db)
    hybrid.initialize_recommenders()
    
    result = hybrid.recommend_with_ab_test(
        config.user_id,
        n_recommendations,
        config.test_name
    )
    
    return ABTestResponse(
        test_name=result["ab_test"]["test_name"],
        group=result["ab_test"]["group"],
        recommendations=[
            RecommendationItem(
                concept_id=r["concept_id"],
                name=r["name"],
                branch="unknown",
                score=r["score"],
                explanation=r["explanation"]
            )
            for r in result["recommendations"]
        ],
        weights=result["ab_test"]["weights"]
    )


@router.post("/feedback")
async def submit_feedback(
    request: FeedbackRequest,
    db: Session = Depends(get_db)
):
    """
    提交推荐反馈
    
    用于强化学习模型的更新
    """
    rl = RLRecommender(db)
    rl.initialize()
    
    # 计算奖励（如果没有提供）
    if request.metrics:
        reward = rl.calculate_reward(
            request.user_id,
            request.concept_id,
            request.action,
            request.metrics
        )
    else:
        reward = request.reward
    
    # 更新模型
    rl.feedback(request.user_id, request.concept_id, reward)
    
    return {
        "status": "success",
        "message": "反馈已接收",
        "user_id": request.user_id,
        "concept_id": request.concept_id,
        "reward": reward
    }


@router.post("/similar-users", response_model=SimilarUsersResponse)
async def find_similar_users(
    request: SimilarUsersRequest,
    db: Session = Depends(get_db)
):
    """
    找到与指定用户最相似的用户
    
    用于社交学习和协作推荐
    """
    cf = CollaborativeFiltering(db)
    cf.build_user_item_matrix()
    cf.compute_user_similarity(k=request.k)
    
    similar_users = cf.find_similar_users(request.user_id, request.k)
    
    return SimilarUsersResponse(
        user_id=request.user_id,
        similar_users=similar_users
    )


@router.get("/explain/{user_id}/{concept_id}")
async def explain_recommendation(
    user_id: int,
    concept_id: str,
    db: Session = Depends(get_db)
):
    """
    解释推荐原因
    
    提供详细的推荐解释，增加透明度
    """
    hybrid = HybridRecommender(db)
    hybrid.initialize_recommenders()
    
    explanation = hybrid.get_explainable_recommendation(user_id, concept_id)
    
    if not explanation:
        raise HTTPException(status_code=404, detail="未找到该推荐的解释")
    
    return explanation


@router.get("/user-profile/{user_id}")
async def get_user_profile(
    user_id: int,
    db: Session = Depends(get_db)
):
    """
    获取用户画像
    
    分析用户的学习风格和偏好
    """
    content = ContentRecommender(db)
    profile = content.analyze_user_profile(user_id)
    
    return {
        "user_id": profile.user_id,
        "learning_style": {
            style.value: score 
            for style, score in profile.learning_style.items()
        },
        "preferred_difficulty": profile.preferred_difficulty,
        "avg_study_session": profile.avg_study_session,
        "preferred_branches": profile.preferred_branches,
        "weak_areas": profile.weak_areas,
        "strong_areas": profile.strong_areas
    }


@router.post("/ab-test/results")
async def get_ab_test_results(
    test_name: str,
    db: Session = Depends(get_db)
):
    """
    获取A/B测试结果
    """
    hybrid = HybridRecommender(db)
    results = hybrid.get_ab_test_results(test_name)
    
    return results


@router.post("/evaluate")
async def evaluate_recommender(
    test_user_count: int = Query(default=100, ge=10, le=1000),
    db: Session = Depends(get_db)
):
    """
    评估推荐系统性能
    
    计算Precision@K, Recall@K, NDCG@K等指标
    """
    from sqlalchemy import func
    from ..models.models import User
    
    # 随机选择测试用户
    test_users = db.query(User.id).order_by(func.random()).limit(test_user_count).all()
    test_user_ids = [u[0] for u in test_users]
    
    hybrid = HybridRecommender(db)
    hybrid.initialize_recommenders()
    
    results = hybrid.evaluate_recommender(
        test_user_ids,
        k_values=[5, 10, 20]
    )
    
    return {
        "test_users": len(test_user_ids),
        "metrics": results
    }
