"""
自适应学习系统 API 路由
"""
from fastapi import APIRouter, HTTPException, Depends, Query
from typing import List, Optional, Dict, Any
from datetime import datetime

from ..schemas import (
    GeneratePathRequest, GeneratePathResponse,
    AdjustPathRequest, AdjustPathResponse,
    RecommendationsResponse, ProgressUpdateRequest,
    MasteryUpdateRequest, LearningPath, PathAdjustment,
    ResourceRecommendation, UserProfile
)
from ..adaptive import (
    generate_learning_path, adjust_learning_path,
    recommend_resources, LearnerProfiler, PathGenerator
)
from ..knowledge_graph import get_knowledge_graph
from ..core.config import settings

router = APIRouter(prefix="/adaptive", tags=["adaptive"])


# ========== 内存存储（实际项目中应使用数据库）==========
# 模拟数据存储
users_db: Dict[str, UserProfile] = {}
paths_db: Dict[str, LearningPath] = {}
adjustments_db: Dict[str, PathAdjustment] = {}


# ========== 辅助函数 ==========

def get_or_create_user(user_id: str) -> UserProfile:
    """获取或创建用户"""
    if user_id not in users_db:
        users_db[user_id] = UserProfile(user_id=user_id)
    return users_db[user_id]


# ========== API 端点 ==========

@router.post("/path", response_model=GeneratePathResponse)
async def generate_path(request: GeneratePathRequest):
    """
    生成个性化学习路径
    
    基于用户画像和目标概念生成最优学习路径
    
    - **user_id**: 用户唯一标识
    - **target_concepts**: 目标概念列表
    - **algorithm**: 路径规划算法 (astar, dp, rl)
    - **constraints**: 可选约束条件
    """
    try:
        # 获取用户画像
        user_profile = get_or_create_user(request.user_id)
        
        # 更新约束和偏好
        if request.constraints:
            if 'max_time' in request.constraints:
                user_profile.metadata['max_time'] = request.constraints['max_time']
        
        if request.preferences:
            if 'interest_areas' in request.preferences:
                user_profile.interest_areas.extend(
                    request.preferences['interest_areas']
                )
        
        # 验证目标概念
        kg = get_knowledge_graph()
        valid_targets = []
        invalid_targets = []
        
        for concept_id in request.target_concepts:
            if kg.get_concept(concept_id):
                valid_targets.append(concept_id)
            else:
                invalid_targets.append(concept_id)
        
        if not valid_targets:
            return GeneratePathResponse(
                success=False,
                message=f"无效的目标概念: {invalid_targets}"
            )
        
        # 生成路径
        path = generate_learning_path(
            user_profile=user_profile,
            target_concepts=valid_targets,
            algorithm=request.algorithm
        )
        
        if not path:
            return GeneratePathResponse(
                success=False,
                message="无法生成有效路径，请检查目标概念的先修关系"
            )
        
        # 保存路径
        paths_db[path.path_id] = path
        
        # 生成备选路径
        generator = PathGenerator(user_profile)
        alternatives = generator.generate_multiple_paths(
            valid_targets, num_paths=2
        )
        
        return GeneratePathResponse(
            success=True,
            path=path,
            message="路径生成成功",
            alternatives=alternatives
        )
        
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/path/{user_id}", response_model=List[LearningPath])
async def get_user_paths(
    user_id: str,
    status: Optional[str] = None
):
    """
    获取用户的所有学习路径
    
    - **user_id**: 用户唯一标识
    - **status**: 可选的状态筛选 (pending, in_progress, completed, adjusted)
    """
    user_paths = [
        path for path in paths_db.values() 
        if path.user_id == user_id
    ]
    
    if status:
        user_paths = [
            path for path in user_paths 
            if path.status.value == status
        ]
    
    # 按创建时间倒序
    user_paths.sort(key=lambda p: p.created_at, reverse=True)
    
    return user_paths


@router.get("/path/detail/{path_id}", response_model=LearningPath)
async def get_path_detail(path_id: str):
    """
    获取学习路径详情
    
    - **path_id**: 路径唯一标识
    """
    if path_id not in paths_db:
        raise HTTPException(status_code=404, detail="路径不存在")
    
    return paths_db[path_id]


@router.post("/adjust", response_model=AdjustPathResponse)
async def adjust_path(request: AdjustPathRequest):
    """
    根据学习表现调整路径
    
    分析学习者的表现数据，动态调整学习路径
    
    - **user_id**: 用户唯一标识
    - **path_id**: 需要调整的路径ID
    - **performance_data**: 表现数据（包含各概念的学习情况）
    - **reason**: 调整原因
    """
    try:
        # 获取路径
        if request.path_id not in paths_db:
            return AdjustPathResponse(
                success=False,
                message="路径不存在"
            )
        
        path = paths_db[request.path_id]
        
        # 获取用户画像
        user_profile = get_or_create_user(request.user_id)
        
        # 构建学习活动记录
        from ..schemas import LearningActivity
        activities = []
        
        # 从 performance_data 构建活动记录
        if 'activities' in request.performance_data:
            for act_data in request.performance_data['activities']:
                activity = LearningActivity(
                    activity_id=act_data.get('id', f"act_{datetime.now().timestamp()}"),
                    user_id=request.user_id,
                    concept_id=act_data['concept_id'],
                    activity_type=act_data.get('type', 'study'),
                    start_time=datetime.fromisoformat(act_data.get('start_time', datetime.now().isoformat())),
                    duration=act_data.get('duration', 0),
                    score=act_data.get('score'),
                    performance_data=act_data.get('details', {})
                )
                activities.append(activity)
        
        # 执行路径调整
        adjustment = adjust_learning_path(
            user_profile=user_profile,
            path=path,
            activities=activities
        )
        
        if not adjustment:
            return AdjustPathResponse(
                success=True,
                message="当前学习表现良好，无需调整路径"
            )
        
        # 保存调整记录
        adjustments_db[adjustment.adjustment_id] = adjustment
        
        # 更新路径
        paths_db[path.path_id] = path
        
        return AdjustPathResponse(
            success=True,
            adjustment=adjustment,
            updated_path=path,
            message=f"路径已调整: {adjustment.trigger_reason}"
        )
        
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.get("/recommendations/{user_id}", response_model=RecommendationsResponse)
async def get_recommendations(
    user_id: str,
    concept_id: Optional[str] = None,
    num: int = Query(default=5, ge=1, le=20)
):
    """
    获取学习资源推荐
    
    基于用户画像和当前学习概念推荐资源
    
    - **user_id**: 用户唯一标识
    - **concept_id**: 可选的概念ID（如未提供则推荐当前路径中的下一概念）
    - **num**: 推荐资源数量
    """
    try:
        user_profile = get_or_create_user(user_id)
        
        # 如果没有指定概念，找用户当前正在学习的概念
        if not concept_id:
            user_paths = [
                p for p in paths_db.values() 
                if p.user_id == user_id and p.status.value in ['in_progress', 'pending']
            ]
            
            if user_paths:
                current_path = user_paths[0]
                # 找第一个未完成的概念
                for node in current_path.nodes:
                    if node.status.value in ['pending', 'in_progress']:
                        concept_id = node.concept.id
                        break
        
        if not concept_id:
            return RecommendationsResponse(
                user_id=user_id,
                message="未找到推荐概念，请先创建学习路径"
            )
        
        # 获取推荐
        recommendations = recommend_resources(
            user_profile=user_profile,
            concept_id=concept_id,
            num_recommendations=num
        )
        
        return RecommendationsResponse(
            user_id=user_id,
            concept_id=concept_id,
            recommendations=recommendations,
            message=f"成功获取 {len(recommendations)} 个资源推荐"
        )
        
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


@router.post("/progress/update")
async def update_progress(request: ProgressUpdateRequest):
    """
    更新学习进度
    
    - **user_id**: 用户唯一标识
    - **path_id**: 路径ID
    - **node_id**: 节点ID
    - **status**: 新状态
    - **score**: 可选的得分
    - **time_spent**: 可选的学习时间
    """
    if request.path_id not in paths_db:
        raise HTTPException(status_code=404, detail="路径不存在")
    
    path = paths_db[request.path_id]
    
    # 更新节点状态
    for node in path.nodes:
        if node.node_id == request.node_id:
            node.status = request.status
            
            if request.score is not None:
                node.metadata['score'] = request.score
            
            if request.time_spent is not None:
                node.metadata['time_spent'] = request.time_spent
            
            break
    
    # 重新计算进度
    completed = sum(1 for n in path.nodes if n.status.value == 'completed')
    path.completed_nodes = completed
    path.progress_percentage = (completed / len(path.nodes) * 100) if path.nodes else 0
    
    # 检查是否完成
    if path.progress_percentage >= 100:
        path.status = PathStatus("completed")
        path.completed_at = datetime.now()
    
    path.updated_at = datetime.now()
    
    return {
        "success": True,
        "path_id": request.path_id,
        "progress": path.progress_percentage,
        "status": path.status.value
    }


@router.post("/mastery/update")
async def update_mastery(request: MasteryUpdateRequest):
    """
    更新概念掌握度
    
    - **user_id**: 用户唯一标识
    - **concept_id**: 概念ID
    - **mastery_score**: 掌握度分数 (0-1)
    - **assessment_method**: 评估方法
    """
    user_profile = get_or_create_user(request.user_id)
    
    # 更新掌握度
    user_profile.mastered_concepts[request.concept_id] = request.mastery_score
    user_profile.updated_at = datetime.now()
    
    # 如果掌握度高，标记为已完成
    if request.mastery_score >= settings.MASTERY_THRESHOLD:
        # 更新相关路径
        for path in paths_db.values():
            if path.user_id == request.user_id:
                for node in path.nodes:
                    if node.concept.id == request.concept_id:
                        node.status = PathStatus("completed")
    
    return {
        "success": True,
        "user_id": request.user_id,
        "concept_id": request.concept_id,
        "mastery_score": request.mastery_score
    }


@router.get("/suggest/{user_id}")
async def suggest_next_action(
    user_id: str,
    current_concept: Optional[str] = None
):
    """
    建议下一步学习行动
    
    基于用户当前状态给出即时学习建议
    
    - **user_id**: 用户唯一标识
    - **current_concept**: 当前学习的概念（可选）
    """
    from ..adaptive import PathAdjuster
    
    user_profile = get_or_create_user(user_id)
    
    # 获取用户当前路径
    active_paths = [
        p for p in paths_db.values()
        if p.user_id == user_id and p.status.value in ['in_progress', 'adjusted']
    ]
    
    if not active_paths and not current_concept:
        return {
            "action": "create_path",
            "message": "您还没有学习路径，建议先创建一条学习路径",
            "suggestions": ["选择感兴趣的数学领域", "设定学习目标"]
        }
    
    # 构建最近的活动数据（简化版）
    recent_activities = []
    
    # 使用 PathAdjuster 给出建议
    adjuster = PathAdjuster(user_profile)
    suggestion = adjuster.suggest_immediate_action(
        current_concept or "",
        recent_activities
    )
    
    return suggestion


@router.get("/concepts/search")
async def search_concepts(
    query: str,
    branch: Optional[str] = None,
    difficulty: Optional[str] = None,
    limit: int = Query(default=10, ge=1, le=50)
):
    """
    搜索数学概念
    
    - **query**: 搜索关键词
    - **branch**: 可选的分支筛选
    - **difficulty**: 可选的难度筛选
    - **limit**: 返回结果数量限制
    """
    kg = get_knowledge_graph()
    
    # 搜索概念
    results = kg.search_concepts(query)
    
    # 应用筛选
    if branch:
        results = [r for r in results if r.branch == branch]
    
    if difficulty:
        results = [r for r in results if r.difficulty.value == difficulty]
    
    # 限制数量
    results = results[:limit]
    
    return {
        "query": query,
        "total": len(results),
        "concepts": [
            {
                "id": c.id,
                "name": c.name,
                "branch": c.branch,
                "difficulty": c.difficulty.value,
                "description": c.description
            }
            for c in results
        ]
    }


@router.get("/concepts/{concept_id}")
async def get_concept_detail(concept_id: str):
    """
    获取概念详情
    
    - **concept_id**: 概念唯一标识
    """
    kg = get_knowledge_graph()
    concept = kg.get_concept(concept_id)
    
    if not concept:
        raise HTTPException(status_code=404, detail="概念不存在")
    
    # 获取相关信息
    prerequisites = kg.get_prerequisites(concept_id, recursive=False)
    successors = kg.get_successors(concept_id)
    related = kg.get_related_concepts(concept_id)
    complexity = kg.calculate_complexity(concept_id)
    
    return {
        "id": concept.id,
        "name": concept.name,
        "description": concept.description,
        "branch": concept.branch,
        "difficulty": concept.difficulty.value,
        "estimated_time": concept.estimated_time,
        "complexity_score": round(complexity, 2),
        "prerequisites": prerequisites,
        "successors": successors,
        "related_concepts": related
    }


@router.get("/stats/{user_id}")
async def get_user_stats(user_id: str):
    """
    获取用户学习统计
    
    - **user_id**: 用户唯一标识
    """
    user_profile = get_or_create_user(user_id)
    
    user_paths = [p for p in paths_db.values() if p.user_id == user_id]
    
    return {
        "user_id": user_id,
        "current_level": user_profile.current_level.value,
        "cognitive_style": user_profile.cognitive_style.value,
        "learning_preference": user_profile.learning_preference.value,
        "statistics": {
            "total_study_time": user_profile.total_study_time,
            "completed_concepts": len(user_profile.mastered_concepts),
            "average_score": user_profile.average_score,
            "total_paths": len(user_paths),
            "completed_paths": sum(1 for p in user_paths if p.status.value == 'completed'),
            "in_progress_paths": sum(1 for p in user_paths if p.status.value == 'in_progress')
        },
        "mastered_concepts": list(user_profile.mastered_concepts.keys())[:20],
        "interest_areas": user_profile.interest_areas
    }
