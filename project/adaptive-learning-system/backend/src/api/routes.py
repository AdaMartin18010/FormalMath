"""
API路由定义
FastAPI路由配置
"""

from typing import List, Optional, Dict, Any
from datetime import datetime
from fastapi import APIRouter, HTTPException, Query, Body
from pydantic import BaseModel, Field

from models.learner import LearnerProfile, LearningStyleProfile, GoalSetting
from models.learning_path import LearningPath, PathConstraints
from services.learner_service import LearnerService
from services.path_service import PathService
from services.support_service import (
    ResourceRecommendationService, PeerMatchingService,
    DifficultyWarningService, AchievementSystem
)
from algorithms.adaptive_engine import RealTimeMonitor
from models.knowledge_graph import KnowledgeGraph


# 请求/响应模型
class LearnerCreateRequest(BaseModel):
    name: str = Field(..., description="学习者姓名")
    email: str = Field(..., description="学习者邮箱")


class LearningStyleAssessmentRequest(BaseModel):
    answers: Dict[str, str] = Field(..., description="问卷答案 {question_id: selected_style}")


class PriorKnowledgeRequest(BaseModel):
    concept_checks: Dict[str, bool] = Field(..., description="概念熟悉度 {concept_id: is_familiar}")


class LearningGoalRequest(BaseModel):
    target_concepts: List[str] = Field(..., description="目标概念列表")
    deadline: Optional[datetime] = Field(None, description="目标截止日期")
    target_level: int = Field(1, ge=0, le=3, description="目标能力层次")
    description: str = Field("", description="目标描述")


class TimeAvailabilityRequest(BaseModel):
    daily_hours: float = Field(..., ge=0.5, le=12, description="每日可用小时数")
    weekly_days: int = Field(..., ge=1, le=7, description="每周可用天数")
    preferred_time: str = Field("evening", description="偏好学习时间")
    max_session: int = Field(60, description="单次最大学习时长（分钟）")


class PathGenerateRequest(BaseModel):
    learner_id: str = Field(..., description="学习者ID")
    goal_concepts: List[str] = Field(..., description="目标概念列表")
    max_time_hours: float = Field(100.0, description="最大总时长")
    difficulty_range_min: float = Field(0.5, ge=0, le=2, description="难度范围最小值")
    difficulty_range_max: float = Field(1.5, ge=0, le=2, description="难度范围最大值")
    diversity_weight: float = Field(0.2, ge=0, le=1, description="多样性权重")


class ProgressUpdateRequest(BaseModel):
    node_id: str = Field(..., description="节点ID")
    progress: float = Field(..., ge=0, le=1, description="学习进度")
    mastery: float = Field(..., ge=0, le=1, description="掌握水平")


class LearningRecordRequest(BaseModel):
    concept_id: str = Field(..., description="概念ID")
    duration: int = Field(..., description="学习时长（分钟）")
    performance: float = Field(..., ge=0, le=1, description="表现分数")
    feedback: str = Field("", description="学习反馈")


class PeerMatchRequest(BaseModel):
    current_concepts: List[str] = Field(..., description="当前学习概念")
    available_times: List[str] = Field(default_factory=list, description="可用时间")


# 创建路由
router = APIRouter()

# 全局服务实例（将在应用启动时初始化）
learner_service: Optional[LearnerService] = None
path_service: Optional[PathService] = None
resource_service: Optional[ResourceRecommendationService] = None
peer_service: Optional[PeerMatchingService] = None
warning_service: Optional[DifficultyWarningService] = None
achievement_system: Optional[AchievementSystem] = None
knowledge_graph: Optional[KnowledgeGraph] = None


def initialize_services(kg: KnowledgeGraph, data_dir: str = "data"):
    """初始化服务"""
    global learner_service, path_service, resource_service
    global peer_service, warning_service, achievement_system, knowledge_graph
    
    knowledge_graph = kg
    learner_service = LearnerService(f"{data_dir}/learner_profiles")
    path_service = PathService(kg, f"{data_dir}/learning_paths")
    resource_service = ResourceRecommendationService(kg)
    peer_service = PeerMatchingService()
    warning_service = DifficultyWarningService(kg)
    achievement_system = AchievementSystem()


# ==================== 学习者API ====================

@router.post("/learners", response_model=Dict[str, str], tags=["learners"])
async def create_learner(request: LearnerCreateRequest):
    """创建新学习者"""
    if not learner_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    learner = learner_service.create_learner(request.name, request.email)
    return {
        "learner_id": learner.learner_id,
        "message": "学习者创建成功"
    }


@router.get("/learners/{learner_id}", response_model=Dict[str, Any], tags=["learners"])
async def get_learner(learner_id: str):
    """获取学习者信息"""
    if not learner_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    summary = learner_service.get_learner_summary(learner_id)
    if not summary:
        raise HTTPException(status_code=404, detail="学习者不存在")
    
    return summary


@router.get("/learners", response_model=List[Dict[str, str]], tags=["learners"])
async def list_learners():
    """列出所有学习者"""
    if not learner_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    return learner_service.list_learners()


@router.post("/learners/{learner_id}/learning-style", response_model=Dict[str, Any], tags=["learners"])
async def assess_learning_style(learner_id: str, request: LearningStyleAssessmentRequest):
    """评估学习风格"""
    if not learner_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    style = learner_service.assess_learning_style(learner_id, request.answers)
    if not style:
        raise HTTPException(status_code=404, detail="学习者不存在")
    
    return {
        "dominant_style": style.dominant_style.value,
        "scores": {
            "visual": style.visual_score,
            "auditory": style.auditory_score,
            "kinesthetic": style.kinesthetic_score,
            "reading": style.reading_score
        }
    }


@router.get("/learning-style/questions", response_model=List[Dict[str, Any]], tags=["learners"])
async def get_learning_style_questions():
    """获取学习风格评估问卷"""
    if not learner_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    return learner_service.get_learning_style_questions()


@router.post("/learners/{learner_id}/prior-knowledge", response_model=Dict[str, float], tags=["learners"])
async def assess_prior_knowledge(learner_id: str, request: PriorKnowledgeRequest):
    """评估先验知识"""
    if not learner_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    prior = learner_service.assess_prior_knowledge(learner_id, request.concept_checks)
    if not prior:
        raise HTTPException(status_code=404, detail="学习者不存在")
    
    return prior


@router.post("/learners/{learner_id}/goals", response_model=Dict[str, Any], tags=["learners"])
async def set_learning_goal(learner_id: str, request: LearningGoalRequest):
    """设置学习目标"""
    if not learner_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    goal = learner_service.set_learning_goal(
        learner_id,
        request.target_concepts,
        request.deadline,
        request.target_level,
        request.description
    )
    if not goal:
        raise HTTPException(status_code=404, detail="学习者不存在")
    
    return {
        "goal_id": goal.goal_id,
        "target_concepts": goal.target_concepts,
        "message": "学习目标设置成功"
    }


@router.post("/learners/{learner_id}/time-availability", response_model=Dict[str, Any], tags=["learners"])
async def set_time_availability(learner_id: str, request: TimeAvailabilityRequest):
    """设置可用时间"""
    if not learner_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    availability = learner_service.set_time_availability(
        learner_id,
        request.daily_hours,
        request.weekly_days,
        request.preferred_time,
        request.max_session
    )
    if not availability:
        raise HTTPException(status_code=404, detail="学习者不存在")
    
    return {
        "daily_available_hours": availability.daily_available_hours,
        "weekly_available_hours": availability.daily_available_hours * availability.weekly_available_days,
        "message": "时间可用性设置成功"
    }


@router.post("/learners/{learner_id}/diagnosis-import", response_model=Dict[str, Any], tags=["learners"])
async def import_diagnosis_result(learner_id: str, diagnosis_result: Dict[str, Any] = Body(...)):
    """从认知诊断系统导入结果"""
    if not learner_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    learner = learner_service.import_diagnosis_result(learner_id, diagnosis_result)
    if not learner:
        raise HTTPException(status_code=404, detail="学习者不存在")
    
    return {
        "message": "诊断结果导入成功",
        "knowledge_state_updated": len(learner.knowledge_state),
        "ability_level_updated": len(learner.ability_level)
    }


# ==================== 学习路径API ====================

@router.post("/learning-path/generate", response_model=Dict[str, Any], tags=["learning-paths"])
async def generate_learning_path(request: PathGenerateRequest):
    """生成学习路径"""
    if not learner_service or not path_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    learner = learner_service.get_learner(request.learner_id)
    if not learner:
        raise HTTPException(status_code=404, detail="学习者不存在")
    
    constraints = PathConstraints(
        max_total_time_hours=request.max_time_hours,
        preferred_difficulty_range=(request.difficulty_range_min, request.difficulty_range_max),
        diversity_weight=request.diversity_weight
    )
    
    recommendation = path_service.generate_path(
        learner,
        request.goal_concepts,
        constraints
    )
    
    return {
        "recommendation_id": recommendation.recommendation_id,
        "paths": [
            {
                "path_id": path.path_id,
                "name": path.name,
                "description": path.description,
                "total_nodes": len(path.nodes),
                "estimated_hours": path.total_estimated_hours,
                "match_score": recommendation.match_scores.get(path.path_id, 0),
                "reason": recommendation.reasons.get(path.path_id, "")
            }
            for path in recommendation.paths
        ]
    }


@router.get("/learning-path/{path_id}", response_model=Dict[str, Any], tags=["learning-paths"])
async def get_learning_path(path_id: str):
    """获取学习路径详情"""
    if not path_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    path = path_service.get_path(path_id)
    if not path:
        raise HTTPException(status_code=404, detail="学习路径不存在")
    
    return {
        "path_id": path_id,
        "name": path.name,
        "description": path.description,
        "status": path.status.value,
        "progress": path.calculate_overall_progress(),
        "total_nodes": len(path.nodes),
        "completed_nodes": len(path.get_completed_nodes()),
        "remaining_hours": path.get_remaining_time(),
        "nodes": [
            {
                "node_id": node.node_id,
                "concept_id": node.concept_id,
                "sequence": node.sequence_number,
                "status": node.status.value,
                "estimated_duration": node.estimated_duration,
                "completion": node.completion_percentage,
                "mastery": node.mastery_level
            }
            for node_id in path.node_order
            for node in [path.nodes[node_id]]
        ]
    }


@router.post("/learning-path/{path_id}/start", response_model=Dict[str, Any], tags=["learning-paths"])
async def start_learning_path(path_id: str):
    """开始学习路径"""
    if not path_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    path = path_service.start_path(path_id)
    if not path:
        raise HTTPException(status_code=404, detail="学习路径不存在")
    
    return {
        "path_id": path_id,
        "status": path.status.value,
        "started_at": path.started_at.isoformat() if path.started_at else None,
        "message": "学习路径已开始"
    }


@router.post("/learning-path/{path_id}/progress", response_model=Dict[str, Any], tags=["learning-paths"])
async def update_progress(path_id: str, request: ProgressUpdateRequest):
    """更新学习进度"""
    if not path_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    path = path_service.update_progress(path_id, request.node_id, request.progress, request.mastery)
    if not path:
        raise HTTPException(status_code=404, detail="学习路径不存在")
    
    return {
        "path_id": path_id,
        "progress": path.calculate_overall_progress(),
        "status": path.status.value,
        "message": "进度更新成功"
    }


@router.get("/learning-path/{path_id}/adjust", response_model=Dict[str, Any], tags=["learning-paths"])
async def get_path_adjustment(path_id: str, adjustment_type: str = "auto"):
    """获取路径调整建议"""
    if not path_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    adjustment = path_service.adjust_path(path_id, adjustment_type)
    if not adjustment:
        return {"message": "当前无需调整"}
    
    return {
        "adjustment_id": adjustment.adjustment_id,
        "reason": adjustment.reason,
        "trigger_type": adjustment.trigger_type,
        "adjustments": adjustment.adjustments_made,
        "nodes_added": len(adjustment.nodes_added),
        "nodes_removed": len(adjustment.nodes_removed)
    }


@router.get("/learning-path/{path_id}/statistics", response_model=Dict[str, Any], tags=["learning-paths"])
async def get_path_statistics(path_id: str):
    """获取路径统计信息"""
    if not path_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    stats = path_service.get_path_statistics(path_id)
    if not stats:
        raise HTTPException(status_code=404, detail="学习路径不存在")
    
    return stats


@router.get("/learning-paths", response_model=List[Dict[str, Any]], tags=["learning-paths"])
async def list_learning_paths(learner_id: Optional[str] = Query(None, description="学习者ID过滤")):
    """列出学习路径"""
    if not path_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    return path_service.list_paths(learner_id)


# ==================== 资源推荐API ====================

@router.get("/resources/recommend", response_model=List[Dict[str, Any]], tags=["resources"])
async def recommend_resources(
    learner_id: str = Query(..., description="学习者ID"),
    concept_id: str = Query(..., description="概念ID"),
    count: int = Query(3, ge=1, le=10, description="推荐数量")
):
    """推荐学习资源"""
    if not learner_service or not resource_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    learner = learner_service.get_learner(learner_id)
    if not learner:
        raise HTTPException(status_code=404, detail="学习者不存在")
    
    return resource_service.recommend_resources(learner, concept_id, count)


@router.get("/resources/search", response_model=List[Dict[str, Any]], tags=["resources"])
async def search_resources(
    query: str = Query(..., description="搜索关键词"),
    concept_id: Optional[str] = Query(None, description="概念ID过滤"),
    resource_type: Optional[str] = Query(None, description="资源类型过滤")
):
    """搜索资源"""
    if not resource_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    from services.support_service import ResourceType
    
    rtype = None
    if resource_type:
        try:
            rtype = ResourceType(resource_type)
        except ValueError:
            pass
    
    results = resource_service.search_resources(query, concept_id, rtype)
    
    return [
        {
            "resource_id": r.resource_id,
            "title": r.title,
            "description": r.description,
            "type": r.resource_type.value,
            "difficulty": r.difficulty,
            "rating": r.rating
        }
        for r in results
    ]


# ==================== 学习伙伴API ====================

@router.post("/peers/register", response_model=Dict[str, Any], tags=["peers"])
async def register_peer(
    learner_id: str = Query(..., description="学习者ID"),
    request: PeerMatchRequest = Body(...)
):
    """注册学习伙伴匹配"""
    if not learner_service or not peer_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    learner = learner_service.get_learner(learner_id)
    if not learner:
        raise HTTPException(status_code=404, detail="学习者不存在")
    
    peer_service.register_learner(
        learner_id,
        request.current_concepts,
        learner.learning_style.dominant_style,
        learner.calculate_overall_ability(),
        request.available_times
    )
    
    return {"message": "学习伙伴匹配注册成功"}


@router.get("/peers/match", response_model=List[Dict[str, Any]], tags=["peers"])
async def find_peers(
    learner_id: str = Query(..., description="学习者ID"),
    max_results: int = Query(5, ge=1, le=20, description="最大结果数")
):
    """寻找学习伙伴"""
    if not peer_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    return peer_service.find_peers(learner_id, max_results)


# ==================== 难点预警API ====================

@router.get("/warnings/analyze", response_model=Dict[str, Any], tags=["warnings"])
async def analyze_warnings(
    learner_id: str = Query(..., description="学习者ID"),
    concept_id: str = Query(..., description="概念ID")
):
    """分析概念难点并生成预警"""
    if not learner_service or not warning_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    learner = learner_service.get_learner(learner_id)
    if not learner:
        raise HTTPException(status_code=404, detail="学习者不存在")
    
    return warning_service.analyze_concept_difficulty(concept_id, learner)


@router.get("/warnings/statistics", response_model=Dict[str, Any], tags=["warnings"])
async def get_warning_statistics(learner_id: Optional[str] = Query(None, description="学习者ID过滤")):
    """获取预警统计信息"""
    if not warning_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    return warning_service.get_warning_statistics(learner_id)


# ==================== 成就系统API ====================

@router.get("/achievements", response_model=Dict[str, Any], tags=["achievements"])
async def get_learner_achievements(learner_id: str = Query(..., description="学习者ID")):
    """获取学习者成就"""
    if not achievement_system:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    return achievement_system.get_learner_achievements(learner_id)


@router.post("/achievements/check", response_model=Dict[str, Any], tags=["achievements"])
async def check_achievements(
    learner_id: str = Query(..., description="学习者ID"),
    stats: Dict[str, Any] = Body(..., description="学习统计数据")
):
    """检查并解锁成就"""
    if not achievement_system:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    unlocked = achievement_system.check_achievements(learner_id, stats)
    
    return {
        "new_achievements": [
            {
                "id": a.achievement_id,
                "name": a.name,
                "description": a.description,
                "icon": a.icon,
                "points": a.points
            }
            for a in unlocked
        ],
        "unlocked_count": len(unlocked)
    }


@router.get("/achievements/leaderboard", response_model=List[Dict[str, Any]], tags=["achievements"])
async def get_achievement_leaderboard(top_n: int = Query(10, ge=5, le=50)):
    """获取成就排行榜"""
    if not achievement_system:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    return achievement_system.get_leaderboard(top_n)


# ==================== 知识图谱API ====================

@router.get("/knowledge-graph/concepts", response_model=List[Dict[str, Any]], tags=["knowledge-graph"])
async def list_concepts(
    difficulty: Optional[int] = Query(None, ge=1, le=4, description="难度级别过滤"),
    msc_prefix: Optional[str] = Query(None, description="MSC编码前缀过滤")
):
    """列出知识图谱中的概念"""
    if not knowledge_graph:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    concepts = []
    for cid, node in knowledge_graph.nodes.items():
        if difficulty and node.difficulty.value != difficulty:
            continue
        if msc_prefix and not node.msc_code.startswith(msc_prefix):
            continue
        
        concepts.append({
            "concept_id": cid,
            "name": node.name,
            "msc_code": node.msc_code,
            "difficulty": node.difficulty.value,
            "estimated_time": node.estimated_time_minutes,
            "description": node.description
        })
    
    return concepts


@router.get("/knowledge-graph/concept/{concept_id}", response_model=Dict[str, Any], tags=["knowledge-graph"])
async def get_concept_detail(concept_id: str):
    """获取概念详情"""
    if not knowledge_graph:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    node = knowledge_graph.get_node(concept_id)
    if not node:
        # 尝试通过名称查找
        for cid, n in knowledge_graph.nodes.items():
            if n.name == concept_id:
                node = n
                concept_id = cid
                break
    
    if not node:
        raise HTTPException(status_code=404, detail="概念不存在")
    
    prerequisites = knowledge_graph.get_prerequisites(concept_id)
    neighbors = knowledge_graph.get_neighbors(concept_id)
    
    return {
        "concept_id": concept_id,
        "name": node.name,
        "msc_code": node.msc_code,
        "difficulty": node.difficulty.value,
        "estimated_time": node.estimated_time_minutes,
        "description": node.description,
        "prerequisites": prerequisites,
        "related_concepts": neighbors,
        "resources": node.resources
    }


@router.get("/knowledge-graph/prerequisites/{concept_id}", response_model=List[str], tags=["knowledge-graph"])
async def get_prerequisites(concept_id: str, recursive: bool = Query(False, description="是否递归获取")):
    """获取概念的先修概念"""
    if not knowledge_graph:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    if recursive:
        prereqs = knowledge_graph.get_prerequisite_graph(concept_id)
        return list(prereqs)
    else:
        return knowledge_graph.get_prerequisites(concept_id)


@router.post("/knowledge-gaps/analyze", response_model=Dict[str, Any], tags=["knowledge-graph"])
async def analyze_knowledge_gaps(
    learner_id: str = Query(..., description="学习者ID"),
    goal_concepts: List[str] = Body(..., description="目标概念列表")
):
    """分析知识缺口"""
    if not learner_service or not path_service:
        raise HTTPException(status_code=503, detail="服务未初始化")
    
    learner = learner_service.get_learner(learner_id)
    if not learner:
        raise HTTPException(status_code=404, detail="学习者不存在")
    
    return path_service.analyze_knowledge_gaps(learner, goal_concepts)
