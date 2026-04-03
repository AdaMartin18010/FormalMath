"""
用户模型 - 学习者特征
"""

from datetime import datetime
from enum import Enum
from typing import Dict, List, Optional
from pydantic import BaseModel, Field


class LearningStyle(str, Enum):
    """学习风格类型"""
    VISUAL = "visual"      # 视觉型
    AUDITORY = "auditory"  # 听觉型
    KINESTHETIC = "kinesthetic"  # 动觉型
    READING = "reading"    # 阅读型
    MIXED = "mixed"        # 混合型


class UserProfile(BaseModel):
    """用户画像"""
    nickname: Optional[str] = None
    grade: Optional[str] = None  # 年级/水平
    major: Optional[str] = None  # 专业/领域
    learning_style: LearningStyle = LearningStyle.MIXED
    learning_goal: Optional[str] = None  # 学习目标
    created_at: datetime = Field(default_factory=datetime.now)
    updated_at: datetime = Field(default_factory=datetime.now)


class User(BaseModel):
    """用户模型"""
    id: str = Field(..., description="用户ID")
    username: str = Field(..., description="用户名")
    email: Optional[str] = None
    profile: UserProfile = Field(default_factory=UserProfile)
    
    # 能力水平 (L0-L3)
    ability_level: Dict[int, float] = Field(
        default_factory=lambda: {0: 0.0, 1: 0.0, 2: 0.0, 3: 0.0},
        description="各层次能力水平"
    )
    
    # 知识状态 (知识点ID -> 掌握概率)
    knowledge_state: Dict[str, float] = Field(
        default_factory=dict,
        description="知识点掌握状态"
    )
    
    # 学习历史
    diagnosis_history: List[str] = Field(
        default_factory=list,
        description="诊断历史记录ID列表"
    )
    
    created_at: datetime = Field(default_factory=datetime.now)
    updated_at: datetime = Field(default_factory=datetime.now)
    
    class Config:
        json_schema_extra = {
            "example": {
                "id": "user_001",
                "username": "math_learner",
                "email": "learner@example.com",
                "profile": {
                    "nickname": "数学爱好者",
                    "grade": "大学",
                    "major": "数学",
                    "learning_style": "visual",
                    "learning_goal": "掌握基础数学概念"
                },
                "ability_level": {0: 0.7, 1: 0.5, 2: 0.3, 3: 0.1},
                "knowledge_state": {"set_theory": 0.8, "logic": 0.6}
            }
        }
