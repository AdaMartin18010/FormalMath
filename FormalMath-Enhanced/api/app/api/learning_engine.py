"""
个性化学习引擎2.0 API
"""
from fastapi import APIRouter, HTTPException, Depends
from pydantic import BaseModel, Field
from typing import List, Dict, Optional, Any
from datetime import datetime

from ..ml.learning_engine import get_learning_engine, PersonalizedLearningEngine
from ..recommendation.adaptive_difficulty import AdaptiveDifficultyManager, DifficultyCalibration
from ..recommendation.content_recommender import RecommendationEngine
from ..recommendation.multi_objective import create_default_objective_balance
from ..social.peer_matching import PeerMatcher, StudyPartnerProfile
from ..social.group_recommendation import GroupRecommender, StudyGroup
from ..social.competition_system import GamificationEngine
from ..gamification.badges import BadgeSystem
from ..gamification.challenges import ChallengeSystem
from ..gamification.progress_visualization import ProgressTracker, MilestoneManager, generate_progress_report

router = APIRouter()

# ============ 请求/响应模型 ============

class InitializeUserRequest(BaseModel):
    user_id: str
    initial_assessment: Optional[Dict[str, Any]] = None

class LearningInteractionRequest(BaseModel):
    user_id: str
    concept_id: str
    interaction_type: str = Field(..., description="交互类型: exercise, video, reading")
    result: Dict[str, Any] = Field(..., description="结果数据")
    context: Optional[Dict[str, Any]] = None

class GeneratePathRequest(BaseModel):
    user_id: str
    target_concepts: List[str]
    constraints: Optional[Dict[str, Any]] = None

class GetRecommendationRequest(BaseModel):
    user_id: str
    session_duration: int = Field(default=30, ge=5, le=180)
    target_concepts: Optional[List[str]] = None

class PeerMatchRequest(BaseModel):
    user_id: str
    purpose: str = Field(default='study', description="匹配目的: study, project, mentorship")
    top_k: int = Field(default=5, ge=1, le=20)

class GroupRecommendRequest(BaseModel):
    user_id: str
    top_k: int = 5

class UpdateDifficultyRequest(BaseModel):
    user_id: str
    performance: float = Field(..., ge=0, le=1)
    time_spent: Optional[int] = None
    expected_time: Optional[int] = None

class AcceptChallengeRequest(BaseModel):
    user_id: str
    challenge_id: str

# ============ API端点 ============

@router.post("/users/initialize")
async def initialize_user(request: InitializeUserRequest):
    """
    初始化用户学习档案
    
    - 设置个体差异模型
    - 导入初始评估数据
    - 准备学习引擎
    """
    engine = get_learning_engine()
    result = engine.initialize_user(request.user_id, request.initial_assessment)
    return result


@router.post("/interactions/record")
async def record_interaction(request: LearningInteractionRequest):
    """
    记录学习交互
    
    处理用户的学习活动，更新所有认知模型
    """
    engine = get_learning_engine()
    result = engine.process_learning_interaction(
        user_id=request.user_id,
        concept_id=request.concept_id,
        interaction_type=request.interaction_type,
        result=request.result,
        context=request.context
    )
    return result


@router.get("/users/{user_id}/next-steps")
async def get_next_steps(user_id: str, current_concept: Optional[str] = None):
    """
    获取下一步学习建议
    
    基于知识追踪和遗忘曲线提供个性化建议
    """
    engine = get_learning_engine()
    suggestions = engine.get_next_steps(user_id, current_concept)
    return {
        'user_id': user_id,
        'suggestions': suggestions
    }


@router.post("/paths/generate")
async def generate_learning_path(request: GeneratePathRequest):
    """
    生成个性化学习路径
    
    结合知识图谱和用户特点生成最优路径
    """
    engine = get_learning_engine()
    path = engine.generate_learning_path(
        user_id=request.user_id,
        target_concepts=request.target_concepts,
        constraints=request.constraints
    )
    return path


@router.get("/users/{user_id}/spaced-repetition")
async def get_spaced_repetition_schedule(user_id: str, days_ahead: int = 7):
    """
    获取间隔重复复习计划
    
    基于遗忘曲线算法生成最优复习时间表
    """
    engine = get_learning_engine()
    schedule = engine.get_spaced_repetition_schedule(user_id, days_ahead)
    return {
        'user_id': user_id,
        'schedule': schedule,
        'total_reviews': len(schedule)
    }


@router.get("/users/{user_id}/analytics")
async def get_user_analytics(user_id: str):
    """
    获取用户学习分析
    
    综合分析报告：知识状态、遗忘曲线、个体差异
    """
    engine = get_learning_engine()
    analytics = engine.get_user_analytics(user_id)
    return analytics


@router.get("/users/{user_id}/predict/{concept_id}")
async def predict_performance(
    user_id: str,
    concept_id: str,
    difficulty: float = 0.5
):
    """
    预测学习表现
    
    使用DNC知识追踪模型预测在特定概念上的表现
    """
    engine = get_learning_engine()
    prediction = engine.predict_performance(user_id, concept_id, difficulty)
    return prediction


# ============ 动态难度调整 API ============

difficulty_manager = AdaptiveDifficultyManager()

@router.post("/difficulty/adjust")
async def adjust_difficulty(request: UpdateDifficultyRequest):
    """
    调整学习难度
    
    根据用户表现动态调整推荐难度
    """
    new_difficulty = difficulty_manager.adjust_difficulty(
        user_id=request.user_id,
        performance=request.performance,
        time_spent=request.time_spent,
        expected_time=request.expected_time
    )
    
    zone = difficulty_manager.assess_performance_zone(request.user_id)
    
    return {
        'user_id': request.user_id,
        'new_difficulty': new_difficulty,
        'performance_zone': zone.value,
        'recommendations': difficulty_manager.get_learning_zone_recommendation(request.user_id)
    }


@router.get("/difficulty/{user_id}/recommended")
async def get_recommended_difficulty(user_id: str):
    """获取推荐难度"""
    difficulty = difficulty_manager.get_recommended_difficulty(user_id)
    return {
        'user_id': user_id,
        'recommended_difficulty': difficulty
    }


@router.get("/difficulty/{user_id}/progression")
async def get_difficulty_progression(user_id: str, num_steps: int = 10):
    """获取难度进阶路径"""
    path = difficulty_manager.get_difficulty_progression_path(user_id, num_steps)
    return {
        'user_id': user_id,
        'progression_path': path
    }


# ============ 推荐系统 API ============

recommendation_engine = RecommendationEngine()

@router.post("/recommendations/session")
async def get_session_recommendations(request: GetRecommendationRequest):
    """
    获取学习会话推荐
    
    为学习会话推荐最合适的内容
    """
    plan = recommendation_engine.recommend_for_learning_session(
        user_id=request.user_id,
        session_duration=request.session_duration,
        target_concepts=request.target_concepts
    )
    return plan


# ============ 社交学习 API ============

peer_matcher = PeerMatcher()
group_recommender = GroupRecommender()

@router.post("/social/peers/match")
async def find_peers(request: PeerMatchRequest):
    """
    寻找学习伙伴
    
    基于多维度匹配算法推荐最佳学习伙伴
    """
    matches = peer_matcher.find_matches(
        user_id=request.user_id,
        purpose=request.purpose,
        top_k=request.top_k
    )
    
    return {
        'user_id': request.user_id,
        'matches': [
            {
                'user_id': match.user_b,
                'overall_score': match.overall_score,
                'component_scores': match.component_scores,
                'reasons': match.match_reasons,
                'challenges': match.potential_challenges
            }
            for match in matches
        ]
    }


@router.get("/social/groups/recommend/{user_id}")
async def recommend_groups(user_id: str, top_k: int = 5):
    """
    推荐学习小组
    
    推荐最适合用户的学习小组
    """
    recommendations = group_recommender.recommend_groups(user_id, top_k)
    
    return {
        'user_id': user_id,
        'recommendations': [
            {
                'group_id': rec.group_id,
                'overall_score': rec.overall_score,
                'fit_scores': rec.fit_scores,
                'reasons': rec.reasons,
                'concerns': rec.concerns
            }
            for rec in recommendations
        ]
    }


# ============ 游戏化 API ============

gamification_engine = GamificationEngine()
badge_system = BadgeSystem()
challenge_system = ChallengeSystem()
progress_tracker = ProgressTracker()
milestone_manager = MilestoneManager()

@router.get("/gamification/{user_id}/summary")
async def get_gamification_summary(user_id: str):
    """
    获取游戏化摘要
    
    整合成就、等级、竞赛等所有游戏化数据
    """
    return gamification_engine.get_user_gamification_summary(user_id)


@router.get("/gamification/{user_id}/achievements")
async def get_user_achievements(user_id: str):
    """获取用户成就"""
    return badge_system.get_user_badges(user_id)


@router.get("/gamification/{user_id}/badges/next")
async def get_next_badges(user_id: str, limit: int = 5):
    """获取即将解锁的徽章"""
    return {
        'user_id': user_id,
        'next_badges': badge_system.get_next_badges(user_id, limit)
    }


@router.get("/gamification/challenges/available/{user_id}")
async def get_available_challenges(user_id: str, user_level: int = 0):
    """获取可用挑战"""
    challenges = challenge_system.get_available_challenges(user_id, user_level)
    return {
        'user_id': user_id,
        'challenges': challenges
    }


@router.post("/gamification/challenges/accept")
async def accept_challenge(request: AcceptChallengeRequest):
    """接受挑战"""
    result = challenge_system.accept_challenge(
        user_id=request.user_id,
        challenge_id=request.challenge_id
    )
    return result


@router.get("/gamification/challenges/{user_id}")
async def get_user_challenges(user_id: str, status: str = 'active'):
    """获取用户挑战"""
    return challenge_system.get_user_challenges(user_id, status)


@router.get("/gamification/progress/{user_id}")
async def get_progress_visualization(
    user_id: str,
    days: int = 30
):
    """
    获取进度可视化数据
    
    生成图表展示所需的数据
    """
    data = progress_tracker.get_progress_visualization_data(user_id, days)
    return data


@router.get("/gamification/heatmap/{user_id}")
async def get_learning_heatmap(user_id: str, year: Optional[int] = None):
    """获取学习热力图数据"""
    heatmap = progress_tracker.generate_heatmap_data(user_id, year)
    return {
        'user_id': user_id,
        'heatmap': heatmap
    }


@router.get("/gamification/milestones/{user_id}")
async def get_user_milestones(user_id: str):
    """获取用户里程碑"""
    return milestone_manager.get_user_milestones(user_id)


@router.get("/gamification/report/{user_id}")
async def get_progress_report(user_id: str, days: int = 30):
    """获取综合进度报告"""
    report = generate_progress_report(user_id, progress_tracker, milestone_manager, days)
    return report


# ============ 系统状态 API ============

@router.get("/system/status")
async def get_system_status():
    """获取学习引擎系统状态"""
    engine = get_learning_engine()
    
    return {
        'status': 'operational',
        'components': {
            'knowledge_tracing': 'active',
            'forgetting_curve': 'active',
            'individual_model': 'active',
            'difficulty_manager': 'active',
            'recommendation_engine': 'active',
            'social_matching': 'active',
            'gamification': 'active'
        },
        'timestamp': datetime.utcnow().isoformat()
    }


@router.post("/system/export/{user_id}")
async def export_user_model(user_id: str):
    """
    导出用户模型
    
    导出完整的用户学习模型用于备份或迁移
    """
    engine = get_learning_engine()
    model_data = engine.export_user_model(user_id)
    return model_data
