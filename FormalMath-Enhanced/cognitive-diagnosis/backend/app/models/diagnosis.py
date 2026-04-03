"""
诊断记录模型
"""

from datetime import datetime
from enum import Enum
from typing import Dict, List, Optional, Any
from pydantic import BaseModel, Field


class DiagnosisStatus(str, Enum):
    """诊断状态"""
    PENDING = "pending"      # 待开始
    IN_PROGRESS = "in_progress"  # 进行中
    COMPLETED = "completed"  # 已完成
    ABORTED = "aborted"      # 已中止


class DiagnosisResponse(BaseModel):
    """诊断答题响应"""
    question_id: str = Field(..., description="题目ID")
    answer: Any = Field(..., description="用户答案")
    is_correct: Optional[bool] = None  # 是否正确
    time_spent: int = Field(..., description="答题用时(秒)")
    confidence: Optional[float] = Field(None, ge=0.0, le=1.0, description="置信度")
    submitted_at: datetime = Field(default_factory=datetime.now)


class DiagnosisSession(BaseModel):
    """诊断会话模型"""
    id: str = Field(..., description="诊断会话ID")
    user_id: str = Field(..., description="用户ID")
    status: DiagnosisStatus = DiagnosisStatus.PENDING
    
    # 诊断配置
    question_count: int = Field(20, description="题目数量")
    time_limit: int = Field(1800, description="时间限制(秒)")
    
    # 题目相关
    question_ids: List[str] = Field(default_factory=list, description="题目ID列表")
    current_question_index: int = Field(0, description="当前题目索引")
    
    # 答题响应
    responses: List[DiagnosisResponse] = Field(default_factory=list)
    
    # 时间记录
    started_at: Optional[datetime] = None
    completed_at: Optional[datetime] = None
    created_at: datetime = Field(default_factory=datetime.now)
    
    class Config:
        json_schema_extra = {
            "example": {
                "id": "diag_001",
                "user_id": "user_001",
                "status": "in_progress",
                "question_count": 20,
                "time_limit": 1800,
                "question_ids": ["q_001", "q_002", "q_003"],
                "current_question_index": 1,
                "responses": []
            }
        }


class AbilityAssessment(BaseModel):
    """能力评估结果"""
    level: int = Field(..., ge=0, le=3, description="层次")
    score: float = Field(..., ge=0.0, le=1.0, description="能力得分")
    description: str = Field(..., description="能力描述")
    mastered_concepts: List[str] = Field(default_factory=list, description="已掌握概念")
    weak_concepts: List[str] = Field(default_factory=list, description="薄弱概念")


class LearningSuggestion(BaseModel):
    """学习建议"""
    type: str = Field(..., description="建议类型")
    title: str = Field(..., description="建议标题")
    content: str = Field(..., description="建议内容")
    priority: int = Field(1, ge=1, le=5, description="优先级")
    related_concepts: List[str] = Field(default_factory=list, description="相关概念")
    recommended_resources: List[Dict[str, Any]] = Field(default_factory=list)


class DiagnosisReport(BaseModel):
    """诊断报告模型"""
    id: str = Field(..., description="报告ID")
    diagnosis_id: str = Field(..., description="诊断会话ID")
    user_id: str = Field(..., description="用户ID")
    
    # 知识状态
    knowledge_state: Dict[str, float] = Field(
        default_factory=dict,
        description="知识点掌握概率"
    )
    
    # 能力水平评估
    ability_level: Dict[int, float] = Field(
        default_factory=dict,
        description="L0-L3各层次能力水平"
    )
    
    ability_assessments: List[AbilityAssessment] = Field(
        default_factory=list,
        description="各层次详细评估"
    )
    
    # 学习建议
    suggestions: List[LearningSuggestion] = Field(default_factory=list)
    
    # 统计信息
    total_questions: int = Field(0, description="总题数")
    correct_count: int = Field(0, description="正确数")
    accuracy: float = Field(0.0, description="正确率")
    avg_time_per_question: float = Field(0.0, description="平均每题用时")
    
    # 可视化数据
    visualization_data: Dict[str, Any] = Field(
        default_factory=dict,
        description="可视化图表数据"
    )
    
    created_at: datetime = Field(default_factory=datetime.now)
    
    class Config:
        json_schema_extra = {
            "example": {
                "id": "report_001",
                "diagnosis_id": "diag_001",
                "user_id": "user_001",
                "knowledge_state": {"set_theory_001": 0.85, "logic_001": 0.72},
                "ability_level": {0: 0.8, 1: 0.65, 2: 0.4, 3: 0.15},
                "total_questions": 20,
                "correct_count": 14,
                "accuracy": 0.7
            }
        }
