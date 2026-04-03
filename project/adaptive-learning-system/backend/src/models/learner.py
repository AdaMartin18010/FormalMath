"""
学习者特征分析模型
定义学习者画像、学习风格、能力水平等数据结构
"""

from datetime import datetime
from typing import Dict, List, Optional, Any
from dataclasses import dataclass, field
from enum import Enum
import uuid


class LearningStyle(Enum):
    """学习风格类型"""
    VISUAL = "visual"          # 视觉型
    AUDITORY = "auditory"      # 听觉型
    KINESTHETIC = "kinesthetic"  # 动手型
    READING = "reading"        # 阅读型
    MULTIMODAL = "multimodal"  # 多模态


class AbilityLevel(Enum):
    """能力层次"""
    L0 = 0  # 基础层
    L1 = 1  # 中级层
    L2 = 2  # 高级层
    L3 = 3  # 研究层


@dataclass
class LearningStyleProfile:
    """学习风格画像"""
    visual_score: float = 0.0      # 视觉型得分 (0-1)
    auditory_score: float = 0.0    # 听觉型得分 (0-1)
    kinesthetic_score: float = 0.0  # 动手型得分 (0-1)
    reading_score: float = 0.0     # 阅读型得分 (0-1)
    
    @property
    def dominant_style(self) -> LearningStyle:
        """获取主导学习风格"""
        scores = {
            LearningStyle.VISUAL: self.visual_score,
            LearningStyle.AUDITORY: self.auditory_score,
            LearningStyle.KINESTHETIC: self.kinesthetic_score,
            LearningStyle.READING: self.reading_score
        }
        max_style = max(scores, key=scores.get)
        
        # 如果最高分数低于0.4，返回多模态
        if scores[max_style] < 0.4:
            return LearningStyle.MULTIMODAL
        return max_style


@dataclass
class GoalSetting:
    """学习目标设定"""
    goal_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    target_concepts: List[str] = field(default_factory=list)  # 目标概念列表
    deadline: Optional[datetime] = None  # 目标截止日期
    target_level: AbilityLevel = AbilityLevel.L1  # 目标能力层次
    description: str = ""  # 目标描述
    priority: int = 1  # 优先级 (1-5)


@dataclass
class TimeAvailability:
    """可用时间评估"""
    daily_available_hours: float = 2.0  # 每日可用小时数
    weekly_available_days: int = 5  # 每周可用天数
    preferred_study_time: str = "evening"  # 偏好学习时间 (morning/afternoon/evening)
    max_session_duration: int = 60  # 单次最大学习时长（分钟）
    weekly_schedule: Dict[str, List[int]] = field(default_factory=dict)  # 每周日程安排


@dataclass
class LearnerProfile:
    """学习者画像"""
    learner_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    name: str = ""
    email: str = ""
    
    # 认知诊断结果（从T2.1系统导入）
    knowledge_state: Dict[str, float] = field(default_factory=dict)  # 概念掌握度
    ability_level: Dict[int, float] = field(default_factory=dict)  # L0-L3能力水平
    
    # 学习风格评估
    learning_style: LearningStyleProfile = field(default_factory=LearningStyleProfile)
    
    # 先验知识评估
    prior_knowledge: Dict[str, float] = field(default_factory=dict)  # 先验知识水平
    
    # 学习目标
    learning_goals: List[GoalSetting] = field(default_factory=list)
    
    # 可用时间
    time_availability: TimeAvailability = field(default_factory=TimeAvailability)
    
    # 学习历史
    learning_history: List[Dict[str, Any]] = field(default_factory=list)
    
    # 偏好设置
    preferences: Dict[str, Any] = field(default_factory=dict)
    
    # 元数据
    created_at: datetime = field(default_factory=datetime.now)
    updated_at: datetime = field(default_factory=datetime.now)
    
    def update_from_diagnosis(self, diagnosis_result: Dict[str, Any]):
        """从认知诊断结果更新学习者画像"""
        if "knowledge_state" in diagnosis_result:
            self.knowledge_state = diagnosis_result["knowledge_state"]
        if "ability_level" in diagnosis_result:
            self.ability_level = diagnosis_result["ability_level"]
        self.updated_at = datetime.now()
    
    def calculate_overall_ability(self) -> float:
        """计算整体能力水平"""
        if not self.ability_level:
            return 0.0
        return sum(self.ability_level.values()) / len(self.ability_level)
    
    def get_concept_mastery(self, concept_id: str) -> float:
        """获取特定概念的掌握度"""
        return self.knowledge_state.get(concept_id, 0.0)
    
    def is_concept_mastered(self, concept_id: str, threshold: float = 0.7) -> bool:
        """判断概念是否已掌握"""
        return self.get_concept_mastery(concept_id) >= threshold
    
    def get_weekly_study_hours(self) -> float:
        """获取每周学习小时数"""
        return self.time_availability.daily_available_hours * self.time_availability.weekly_available_days


@dataclass
class LearningRecord:
    """学习记录"""
    record_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    learner_id: str = ""
    concept_id: str = ""
    start_time: datetime = field(default_factory=datetime.now)
    end_time: Optional[datetime] = None
    duration_minutes: int = 0
    progress_percentage: float = 0.0  # 学习进度百分比
    performance_score: float = 0.0  # 学习表现分数
    difficulty_rating: float = 0.0  # 难度评分
    feedback: str = ""  # 学习者反馈
    resources_used: List[str] = field(default_factory=list)  # 使用的资源
    
    def calculate_duration(self):
        """计算学习时长"""
        if self.end_time:
            delta = self.end_time - self.start_time
            self.duration_minutes = int(delta.total_seconds() / 60)


@dataclass
class LearnerProgress:
    """学习者进度"""
    learner_id: str = ""
    total_concepts_learned: int = 0
    total_study_time_hours: float = 0.0
    average_mastery_rate: float = 0.0
    current_streak_days: int = 0  # 当前连续学习天数
    longest_streak_days: int = 0  # 最长连续学习天数
    achievements: List[str] = field(default_factory=list)  # 获得的成就
    
    def calculate_mastery_rate(self, total_concepts: int) -> float:
        """计算掌握率"""
        if total_concepts == 0:
            return 0.0
        return self.total_concepts_learned / total_concepts


# 学习风格评估问卷
LEARNING_STYLE_QUESTIONS = [
    {
        "id": "visual_1",
        "question": "当你学习新概念时，你更喜欢：",
        "options": [
            {"text": "查看图表、思维导图或可视化表示", "style": "visual", "weight": 1.0},
            {"text": "听讲座或讨论", "style": "auditory", "weight": 1.0},
            {"text": "动手实践或做实验", "style": "kinesthetic", "weight": 1.0},
            {"text": "阅读教科书或文档", "style": "reading", "weight": 1.0}
        ]
    },
    {
        "id": "visual_2",
        "question": "在解决问题时，你倾向于：",
        "options": [
            {"text": "在脑海中形成图像或可视化问题", "style": "visual", "weight": 0.8},
            {"text": "通过讨论理清思路", "style": "auditory", "weight": 0.8},
            {"text": "尝试不同的解决方法", "style": "kinesthetic", "weight": 0.8},
            {"text": "列出步骤和程序", "style": "reading", "weight": 0.8}
        ]
    },
    {
        "id": "visual_3",
        "question": "你最喜欢的学习资源类型是：",
        "options": [
            {"text": "视频教程、信息图表", "style": "visual", "weight": 1.0},
            {"text": "播客、有声书", "style": "auditory", "weight": 1.0},
            {"text": "互动练习、模拟器", "style": "kinesthetic", "weight": 1.0},
            {"text": "书籍、文章、文档", "style": "reading", "weight": 1.0}
        ]
    },
    {
        "id": "kinesthetic_1",
        "question": "当你在学数学证明时，你更喜欢：",
        "options": [
            {"text": "看证明的可视化流程图", "style": "visual", "weight": 0.8},
            {"text": "听老师讲解证明过程", "style": "auditory", "weight": 0.8},
            {"text": "自己尝试证明，边做边学", "style": "kinesthetic", "weight": 0.8},
            {"text": "仔细阅读证明的每一步", "style": "reading", "weight": 0.8}
        ]
    },
    {
        "id": "reading_1",
        "question": "你如何记录学习内容：",
        "options": [
            {"text": "使用颜色编码、思维导图", "style": "visual", "weight": 0.8},
            {"text": "录音或口头复述", "style": "auditory", "weight": 0.8},
            {"text": "通过实践项目记录", "style": "kinesthetic", "weight": 0.8},
            {"text": "做详细的文字笔记", "style": "reading", "weight": 0.8}
        ]
    }
]
