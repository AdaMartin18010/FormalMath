"""
Pydantic数据模型
"""
from pydantic import BaseModel, Field
from typing import List, Dict, Optional, Any, Literal
from datetime import datetime
from enum import Enum


# ============ 枚举类型 ============

class QuestionType(str, Enum):
    """题目类型"""
    SINGLE_CHOICE = "SC"
    MULTIPLE_CHOICE = "MC"
    FILL_BLANK = "FB"
    SHORT_ANSWER = "SA"
    PROOF = "PR"


class KnowledgeLevel(int, Enum):
    """知识层次"""
    L0 = 0  # 基础概念
    L1 = 1  # 定义理解
    L2 = 2  # 定理应用
    L3 = 3  # 综合证明


class TestStatus(str, Enum):
    """测试状态"""
    PENDING = "pending"
    IN_PROGRESS = "in_progress"
    COMPLETED = "completed"
    ABORTED = "aborted"


class AbilityLevel(str, Enum):
    """能力等级"""
    BEGINNER = "beginner"
    DEVELOPING = "developing"
    INTERMEDIATE = "intermediate"
    ADVANCED = "advanced"


# ============ 基础模型 ============

class QuestionBase(BaseModel):
    """题目基础模型"""
    content: str = Field(..., description="题目内容")
    type: QuestionType = Field(..., description="题目类型")
    level: KnowledgeLevel = Field(..., description="知识层次")
    difficulty: int = Field(..., ge=1, le=5, description="难度等级")
    branch: str = Field(..., description="数学分支")
    concepts: List[str] = Field(default=[], description="关联知识点")
    skills: List[str] = Field(default=[], description="考察技能")
    time_estimate: int = Field(default=60, description="预估用时(秒)")
    score: float = Field(default=5.0, description="分值")


class QuestionCreate(QuestionBase):
    """创建题目模型"""
    options: Optional[Dict[str, str]] = Field(None, description="选项(选择题)")
    answer: Optional[str] = Field(None, description="正确答案")
    explanation: Optional[str] = Field(None, description="解析")
    prerequisite_concepts: List[str] = Field(default=[], description="先修知识点")


class QuestionResponse(QuestionBase):
    """题目响应模型（不含答案）"""
    id: str
    preview: str = Field(..., description="题目预览")
    
    class Config:
        from_attributes = True


class QuestionDetail(QuestionResponse):
    """题目详情（含选项，不含答案）"""
    options: Optional[Dict[str, str]] = None


# ============ 测试相关模型 ============

class StartDiagnosisRequest(BaseModel):
    """开始诊断请求"""
    student_id: Optional[str] = None
    target_level: Optional[KnowledgeLevel] = None
    focus_areas: List[str] = Field(default=[], description="重点领域")
    question_count: int = Field(default=30, ge=10, le=50, description="题目数量")


class StartDiagnosisResponse(BaseModel):
    """开始诊断响应"""
    test_id: str
    questions: List[QuestionDetail]
    time_limit: int = Field(..., description="时间限制(秒)")


class AnswerSubmission(BaseModel):
    """答案提交"""
    question_id: str
    answer: str
    time_spent: int = Field(..., description="用时(秒)")


class SubmitAnswersRequest(BaseModel):
    """提交答案请求"""
    test_id: str
    responses: List[AnswerSubmission]


class SubmitAnswersResponse(BaseModel):
    """提交答案响应"""
    test_id: str
    status: str
    completed_count: int
    total_count: int
    message: str


# ============ 诊断结果模型 ============

class ConceptMastery(BaseModel):
    """概念掌握度"""
    level: float = Field(..., ge=0, le=1, description="掌握度")
    confidence: float = Field(..., ge=0, le=1, description="置信度")


class AbilityInfo(BaseModel):
    """能力信息"""
    score: float = Field(..., ge=0, le=1, description="得分")
    level: AbilityLevel = Field(..., description="等级")
    description: str = Field(..., description="描述")
    concept_count: Optional[int] = None
    mastered_concepts: Optional[int] = None


class WeakArea(BaseModel):
    """薄弱环节"""
    concept_id: str
    concept_name: str
    current_level: float
    target_level: float = 0.7
    improvement_needed: float
    recommended_action: Optional[str] = None


class StrongArea(BaseModel):
    """优势领域"""
    concept_id: str
    concept_name: str
    current_level: float


class Suggestion(BaseModel):
    """学习建议"""
    type: str = Field(..., description="建议类型")
    priority: int = Field(..., ge=1, le=10, description="优先级")
    title: str
    description: str
    action: Optional[str] = None
    estimated_time: Optional[str] = None
    target_concept: Optional[str] = None
    resources: List[str] = Field(default=[])


class DiagnosisResultResponse(BaseModel):
    """诊断结果响应"""
    test_id: str
    student_id: str
    knowledge_state: Dict[str, ConceptMastery]
    ability_level: Dict[str, AbilityInfo]
    weak_areas: List[WeakArea]
    strong_areas: List[StrongArea]
    suggestions: List[Suggestion]
    report_summary: str
    overall_confidence: float
    created_at: datetime


# ============ 学生档案模型 ============

class StudentProfile(BaseModel):
    """学生档案"""
    student_id: str
    username: str
    email: Optional[str] = None
    current_level: int
    overall_level: float
    knowledge_radar: Dict[str, float]
    learning_trajectory: List[Dict[str, Any]]
    recent_diagnoses: List[Dict[str, Any]]
    recommended_next_steps: List[Suggestion]


# ============ 学习路径模型 ============

class LearningNode(BaseModel):
    """学习节点"""
    id: str
    title: str
    concept_id: str
    estimated_time: str
    prerequisites: List[str]
    status: str = "pending"  # pending/in_progress/completed


class LearningPathResponse(BaseModel):
    """学习路径响应"""
    path_id: str
    student_id: str
    nodes: List[LearningNode]
    current_node: str
    progress: float


# ============ API响应包装 ============

class APIResponse(BaseModel):
    """API标准响应"""
    success: bool = True
    message: str = "操作成功"
    data: Optional[Any] = None
    error: Optional[str] = None


class PaginatedResponse(BaseModel):
    """分页响应"""
    total: int
    page: int
    page_size: int
    items: List[Any]
