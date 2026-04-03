"""
题目模型 - 知识标签、难度、区分度
"""

from datetime import datetime
from enum import Enum
from typing import Dict, List, Optional, Any
from pydantic import BaseModel, Field


class QuestionType(str, Enum):
    """题目类型"""
    SINGLE_CHOICE = "single_choice"      # 单选题
    MULTIPLE_CHOICE = "multiple_choice"  # 多选题
    FILL_BLANK = "fill_blank"            # 填空题
    TRUE_FALSE = "true_false"            # 判断题
    PROOF = "proof"                      # 证明题
    CALCULATION = "calculation"          # 计算题


class KnowledgeLevel(int, Enum):
    """知识层次 (L0-L3)"""
    L0 = 0  # 基础层
    L1 = 1  # 中级层
    L2 = 2  # 高级层
    L3 = 3  # 研究层


class KnowledgeTag(BaseModel):
    """知识标签"""
    id: str = Field(..., description="知识点ID")
    name: str = Field(..., description="知识点名称")
    level: KnowledgeLevel = Field(..., description="知识层次")
    parent_id: Optional[str] = None  # 父知识点ID
    description: Optional[str] = None
    
    class Config:
        json_schema_extra = {
            "example": {
                "id": "set_theory_001",
                "name": "集合的基本概念",
                "level": 0,
                "parent_id": None,
                "description": "集合的直观理解"
            }
        }


class Question(BaseModel):
    """题目模型"""
    id: str = Field(..., description="题目ID")
    type: QuestionType = Field(..., description="题目类型")
    
    # 题目内容
    content: str = Field(..., description="题目内容")
    options: Optional[List[Dict[str, Any]]] = None  # 选择题选项
    correct_answer: Any = Field(..., description="正确答案")
    explanation: Optional[str] = None  # 答案解析
    
    # 知识标签
    knowledge_tags: List[str] = Field(..., description="关联知识点ID列表")
    knowledge_level: KnowledgeLevel = Field(..., description="知识层次")
    
    # 题目参数 (IRT模型)
    difficulty: float = Field(0.0, ge=-3.0, le=3.0, description="难度参数")
    discrimination: float = Field(1.0, ge=0.0, le=3.0, description="区分度参数")
    guessing: float = Field(0.25, ge=0.0, le=0.5, description="猜测参数")
    
    # Q矩阵 (知识点与题目的关联)
    q_matrix: Dict[str, float] = Field(
        default_factory=dict,
        description="知识点关联强度"
    )
    
    # 元数据
    category: Optional[str] = None  # 题目分类
    estimated_time: int = Field(60, description="预估答题时间(秒)")
    score: float = Field(1.0, description="题目分值")
    
    created_at: datetime = Field(default_factory=datetime.now)
    updated_at: datetime = Field(default_factory=datetime.now)
    
    class Config:
        json_schema_extra = {
            "example": {
                "id": "q_001",
                "type": "single_choice",
                "content": "集合的基本性质包括哪些？",
                "options": [
                    {"id": "A", "text": "确定性"},
                    {"id": "B", "text": "互异性"},
                    {"id": "C", "text": "无序性"},
                    {"id": "D", "text": "以上都是"}
                ],
                "correct_answer": "D",
                "explanation": "集合具有确定性、互异性和无序性三个基本性质",
                "knowledge_tags": ["set_theory_001"],
                "knowledge_level": 0,
                "difficulty": -0.5,
                "discrimination": 1.2,
                "guessing": 0.25,
                "q_matrix": {"set_theory_001": 1.0}
            }
        }
