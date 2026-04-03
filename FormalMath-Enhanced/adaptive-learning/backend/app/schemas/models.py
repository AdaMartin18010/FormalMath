"""
Pydantic 数据模型定义
"""
from pydantic import BaseModel, Field
from typing import List, Dict, Optional, Any, Set
from datetime import datetime
from enum import Enum


# ========== 枚举类型定义 ==========

class CognitiveStyle(str, Enum):
    """认知风格类型"""
    VISUAL = "visual"           # 视觉型
    AUDITORY = "auditory"       # 听觉型
    READING = "reading"         # 阅读型
    KINESTHETIC = "kinesthetic" # 动觉型
    MIXED = "mixed"             # 混合型


class LearningPreference(str, Enum):
    """学习偏好类型"""
    THEORY_FIRST = "theory_first"     # 理论优先
    EXAMPLE_FIRST = "example_first"   # 例子优先
    PRACTICE_FIRST = "practice_first" # 练习优先
    BALANCED = "balanced"             # 平衡型


class DifficultyLevel(str, Enum):
    """难度等级"""
    BEGINNER = "beginner"
    INTERMEDIATE = "intermediate"
    ADVANCED = "advanced"
    EXPERT = "expert"


class ConceptRelationType(str, Enum):
    """概念关系类型"""
    PREREQUISITE = "先修"       # 先修关系
    SUCCESSOR = "后继"          # 后继关系
    RELATED = "相关"            # 相关关系
    CROSS = "交叉"              # 交叉关系
    APPLICATION = "应用"        # 应用关系
    EXTENSION = "推广"          # 推广关系


class PathStatus(str, Enum):
    """学习路径状态"""
    PENDING = "pending"         # 待开始
    IN_PROGRESS = "in_progress" # 进行中
    COMPLETED = "completed"     # 已完成
    ADJUSTED = "adjusted"       # 已调整
    ABANDONED = "abandoned"     # 已放弃


class ResourceType(str, Enum):
    """资源类型"""
    TEXT = "text"               # 文本
    VIDEO = "video"             # 视频
    INTERACTIVE = "interactive" # 交互式
    EXERCISE = "exercise"       # 练习
    PROOF = "proof"             # 证明
    EXAMPLE = "example"         # 示例


# ========== 基础模型 ==========

class ConceptNode(BaseModel):
    """知识图谱概念节点"""
    id: str = Field(..., description="概念唯一标识")
    name: str = Field(..., description="概念名称")
    description: str = Field(default="", description="概念描述")
    branch: str = Field(..., description="所属数学分支")
    difficulty: DifficultyLevel = Field(default=DifficultyLevel.INTERMEDIATE)
    estimated_time: int = Field(default=30, description="预计学习时间(分钟)")
    prerequisites: List[str] = Field(default_factory=list)
    successors: List[str] = Field(default_factory=list)
    related: List[str] = Field(default_factory=list)
    resources: List[Dict[str, Any]] = Field(default_factory=list)
    metadata: Dict[str, Any] = Field(default_factory=dict)


class ConceptRelation(BaseModel):
    """概念间关系"""
    source: str = Field(..., description="源概念ID")
    target: str = Field(..., description="目标概念ID")
    type: ConceptRelationType
    strength: float = Field(default=1.0, ge=0.0, le=1.0, description="关系强度")
    description: str = Field(default="")


class UserProfile(BaseModel):
    """学习者画像"""
    user_id: str = Field(..., description="用户唯一标识")
    cognitive_style: CognitiveStyle = Field(default=CognitiveStyle.MIXED)
    learning_preference: LearningPreference = Field(default=LearningPreference.BALANCED)
    current_level: DifficultyLevel = Field(default=DifficultyLevel.BEGINNER)
    
    # 已掌握概念 (concept_id -> mastery_score)
    mastered_concepts: Dict[str, float] = Field(default_factory=dict)
    
    # 学习中概念
    learning_concepts: List[str] = Field(default_factory=list)
    
    # 学习历史
    learning_history: List[Dict[str, Any]] = Field(default_factory=list)
    
    # 兴趣领域
    interest_areas: List[str] = Field(default_factory=list)
    
    # 学习统计
    total_study_time: int = Field(default=0, description="总学习时间(分钟)")
    completed_concepts: int = Field(default=0)
    average_score: float = Field(default=0.0)
    
    created_at: datetime = Field(default_factory=datetime.now)
    updated_at: datetime = Field(default_factory=datetime.now)


class LearningActivity(BaseModel):
    """学习活动记录"""
    activity_id: str
    user_id: str
    concept_id: str
    activity_type: str  # study, exercise, quiz, review
    start_time: datetime
    end_time: Optional[datetime] = None
    duration: int = Field(default=0, description="持续时间(分钟)")
    score: Optional[float] = None
    performance_data: Dict[str, Any] = Field(default_factory=dict)


class PathNode(BaseModel):
    """学习路径节点"""
    node_id: str
    concept: ConceptNode
    order: int = Field(..., description="在路径中的顺序")
    status: PathStatus = Field(default=PathStatus.PENDING)
    recommended_resources: List[Dict[str, Any]] = Field(default_factory=list)
    estimated_time: int = Field(default=30)
    suggested_start_date: Optional[datetime] = None
    suggested_end_date: Optional[datetime] = None
    
    # 自适应参数
    difficulty_adjustment: float = Field(default=0.0)
    priority_score: float = Field(default=1.0)


class LearningPath(BaseModel):
    """学习路径"""
    path_id: str
    user_id: str
    name: str
    description: str = ""
    target_concepts: List[str] = Field(default_factory=list)
    nodes: List[PathNode] = Field(default_factory=list)
    
    # 路径统计
    total_concepts: int = Field(default=0)
    total_estimated_time: int = Field(default=0)
    completed_nodes: int = Field(default=0)
    progress_percentage: float = Field(default=0.0)
    
    # 状态
    status: PathStatus = Field(default=PathStatus.PENDING)
    created_at: datetime = Field(default_factory=datetime.now)
    updated_at: datetime = Field(default_factory=datetime.now)
    started_at: Optional[datetime] = None
    completed_at: Optional[datetime] = None
    
    # 元数据
    metadata: Dict[str, Any] = Field(default_factory=dict)


class ResourceRecommendation(BaseModel):
    """资源推荐"""
    resource_id: str
    title: str
    type: ResourceType
    url: Optional[str] = None
    description: str = ""
    difficulty: DifficultyLevel
    estimated_time: int
    
    # 推荐参数
    relevance_score: float = Field(..., ge=0.0, le=1.0)
    match_reason: str = ""
    
    # 适用性
    suitable_for: List[CognitiveStyle] = Field(default_factory=list)


class PathAdjustment(BaseModel):
    """路径调整记录"""
    adjustment_id: str
    path_id: str
    user_id: str
    
    # 调整原因
    trigger_concept: Optional[str] = None
    trigger_reason: str = ""
    performance_data: Dict[str, Any] = Field(default_factory=dict)
    
    # 调整内容
    old_nodes: List[PathNode] = Field(default_factory=list)
    new_nodes: List[PathNode] = Field(default_factory=list)
    
    # 调整类型
    adjustment_type: str  # add, remove, reorder, modify
    
    # 时间戳
    created_at: datetime = Field(default_factory=datetime.now)
    applied: bool = Field(default=False)


# ========== API 请求/响应模型 ==========

class GeneratePathRequest(BaseModel):
    """生成学习路径请求"""
    user_id: str
    target_concepts: List[str]
    algorithm: str = Field(default="astar", description="算法类型: astar, dp, rl")
    constraints: Optional[Dict[str, Any]] = Field(default=None)
    preferences: Optional[Dict[str, Any]] = Field(default=None)


class GeneratePathResponse(BaseModel):
    """生成学习路径响应"""
    success: bool
    path: Optional[LearningPath] = None
    message: str = ""
    alternatives: List[LearningPath] = Field(default_factory=list)


class AdjustPathRequest(BaseModel):
    """调整学习路径请求"""
    user_id: str
    path_id: str
    performance_data: Dict[str, Any]
    reason: str = ""


class AdjustPathResponse(BaseModel):
    """调整学习路径响应"""
    success: bool
    adjustment: Optional[PathAdjustment] = None
    updated_path: Optional[LearningPath] = None
    message: str = ""


class RecommendationsResponse(BaseModel):
    """资源推荐响应"""
    user_id: str
    concept_id: Optional[str] = None
    recommendations: List[ResourceRecommendation] = Field(default_factory=list)
    

class ProgressUpdateRequest(BaseModel):
    """进度更新请求"""
    user_id: str
    path_id: str
    node_id: str
    status: PathStatus
    score: Optional[float] = None
    time_spent: Optional[int] = None
    feedback: Optional[str] = None


class MasteryUpdateRequest(BaseModel):
    """掌握度更新请求"""
    user_id: str
    concept_id: str
    mastery_score: float = Field(..., ge=0.0, le=1.0)
    assessment_method: str = "quiz"  # quiz, exercise, self_report
