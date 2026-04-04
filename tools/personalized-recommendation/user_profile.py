"""
个性化学习路径推荐系统 - 用户画像模型
基于全局依赖图的个性化学习路径推荐

本模块定义了用户画像的数据结构，包括学习风格、能力水平、学习目标等
"""

from datetime import datetime, timedelta
from typing import Dict, List, Optional, Set, Tuple, Any, Callable
from dataclasses import dataclass, field
from enum import Enum
import uuid
import json


class LearningStyle(Enum):
    """学习风格类型 - 基于Felder-Silverman学习风格模型简化版"""
    VISUAL = "visual"          # 视觉型 - 偏好图表、图像、视频
    TEXTUAL = "textual"        # 文本型 - 偏好阅读、文字说明
    INTERACTIVE = "interactive"  # 交互型 - 偏好实践、交互、动手操作
    MULTIMODAL = "multimodal"  # 多模态 - 适应多种学习方式


class ProficiencyLevel(Enum):
    """熟练度等级"""
    NOVICE = 1         # 新手
    BEGINNER = 2       # 初学者
    INTERMEDIATE = 3   # 中级
    ADVANCED = 4       # 高级
    EXPERT = 5         # 专家


class LearningGoalPriority(Enum):
    """学习目标优先级"""
    LOW = 1
    MEDIUM = 2
    HIGH = 3
    CRITICAL = 4


@dataclass
class ConceptMastery:
    """概念掌握度记录"""
    concept_id: str
    mastery_level: float = 0.0  # 掌握程度 (0-1)
    confidence: float = 0.0      # 置信度 (0-1)
    last_studied: Optional[datetime] = None
    study_count: int = 0         # 学习次数
    test_scores: List[float] = field(default_factory=list)  # 测试成绩
    
    def update_mastery(self, new_score: float, weight: float = 0.3):
        """更新掌握度 - 使用指数移动平均"""
        self.mastery_level = (1 - weight) * self.mastery_level + weight * new_score
        self.study_count += 1
        self.last_studied = datetime.now()
        self.test_scores.append(new_score)
    
    def get_proficiency_level(self) -> ProficiencyLevel:
        """根据掌握度获取熟练度等级"""
        if self.mastery_level >= 0.9:
            return ProficiencyLevel.EXPERT
        elif self.mastery_level >= 0.75:
            return ProficiencyLevel.ADVANCED
        elif self.mastery_level >= 0.5:
            return ProficiencyLevel.INTERMEDIATE
        elif self.mastery_level >= 0.25:
            return ProficiencyLevel.BEGINNER
        return ProficiencyLevel.NOVICE


@dataclass
class LearningPreference:
    """学习偏好设置"""
    # 学习风格权重
    style_weights: Dict[LearningStyle, float] = field(default_factory=lambda: {
        LearningStyle.VISUAL: 0.25,
        LearningStyle.TEXTUAL: 0.25,
        LearningStyle.INTERACTIVE: 0.25,
        LearningStyle.MULTIMODAL: 0.25
    })
    
    # 内容偏好
    prefer_examples: bool = True           # 偏好示例
    prefer_proofs: bool = True             # 偏好证明
    prefer_applications: bool = True       # 偏好应用
    prefer_intuition: bool = True          # 偏好直观解释
    
    # 学习节奏
    pace_preference: str = "moderate"      # slow/moderate/fast
    difficulty_tolerance: float = 0.3      # 可接受的难度波动范围
    
    # 复习偏好
    review_frequency: str = "adaptive"     # 复习频率: daily/adaptive/weekly
    review_method: str = "spaced"          # 复习方法: spaced/active/passive
    
    def get_dominant_style(self) -> LearningStyle:
        """获取主导学习风格"""
        return max(self.style_weights.items(), key=lambda x: x[1])[0]
    
    def update_style_weights(self, style_scores: Dict[LearningStyle, float]):
        """更新学习风格权重"""
        total = sum(style_scores.values())
        if total > 0:
            self.style_weights = {
                style: score / total 
                for style, score in style_scores.items()
            }


@dataclass
class TimePreference:
    """时间偏好设置"""
    daily_hours: float = 2.0                    # 每日学习时间（小时）
    weekly_days: int = 5                        # 每周学习天数
    preferred_time_slots: List[str] = field(default_factory=lambda: ["evening"])
    # 可选: morning/afternoon/evening/night
    
    session_duration: int = 45                  # 单次学习时长（分钟）
    break_duration: int = 10                    # 休息时长（分钟）
    max_continuous_sessions: int = 3            # 最大连续学习段数
    
    def get_weekly_hours(self) -> float:
        """获取每周总学习时间"""
        return self.daily_hours * self.weekly_days
    
    def get_daily_sessions(self) -> int:
        """获取每日学习段数"""
        total_minutes = self.daily_hours * 60
        session_with_break = self.session_duration + self.break_duration
        return max(1, int(total_minutes / session_with_break))
    
    def estimate_completion_days(self, total_hours: float) -> int:
        """估算完成所需天数"""
        weekly_hours = self.get_weekly_hours()
        if weekly_hours <= 0:
            return float('inf')
        weeks = total_hours / weekly_hours
        return int(weeks * 7)


@dataclass
class LearningGoal:
    """学习目标定义"""
    goal_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    name: str = ""                              # 目标名称
    target_concepts: List[str] = field(default_factory=list)  # 目标概念ID列表
    deadline: Optional[datetime] = None         # 截止日期
    priority: LearningGoalPriority = LearningGoalPriority.MEDIUM
    required_mastery: float = 0.7               # 要求的掌握度阈值
    description: str = ""                       # 目标描述
    created_at: datetime = field(default_factory=datetime.now)
    
    def get_days_remaining(self) -> Optional[int]:
        """获取剩余天数"""
        if not self.deadline:
            return None
        delta = self.deadline - datetime.now()
        return max(0, delta.days)
    
    def is_urgent(self) -> bool:
        """判断是否紧急（剩余时间少于7天）"""
        days = self.get_days_remaining()
        return days is not None and days < 7
    
    def estimate_required_hours(self, concept_graph: Any) -> float:
        """估算所需总学习时间"""
        total_time = 0.0
        for concept_id in self.target_concepts:
            # 这里简化处理，实际应从知识图谱获取
            total_time += 2.0  # 假设每个概念平均2小时
        return total_time


@dataclass
class LearningHistory:
    """学习历史记录"""
    session_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    concept_id: str = ""
    start_time: datetime = field(default_factory=datetime.now)
    end_time: Optional[datetime] = None
    duration_minutes: int = 0
    completion_rate: float = 0.0               # 完成率
    performance_score: float = 0.0             # 表现分数
    difficulty_rating: int = 3                 # 难度评分 (1-5)
    satisfaction_rating: int = 3               # 满意度评分 (1-5)
    resources_used: List[str] = field(default_factory=list)
    notes: str = ""
    
    def finalize_session(self):
        """结束学习会话"""
        self.end_time = datetime.now()
        if self.start_time:
            delta = self.end_time - self.start_time
            self.duration_minutes = int(delta.total_seconds() / 60)


@dataclass
class UserProfile:
    """
    用户画像 - 个性化学习路径推荐的核心数据结构
    
    包含用户的学习特征、目标、偏好和历史记录
    """
    user_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    name: str = ""
    email: str = ""
    created_at: datetime = field(default_factory=datetime.now)
    updated_at: datetime = field(default_factory=datetime.now)
    
    # 核心特征
    mastered_concepts: Dict[str, ConceptMastery] = field(default_factory=dict)
    weak_concepts: List[str] = field(default_factory=list)
    learning_preference: LearningPreference = field(default_factory=LearningPreference)
    time_preference: TimePreference = field(default_factory=TimePreference)
    
    # 学习目标
    active_goals: List[LearningGoal] = field(default_factory=list)
    completed_goals: List[LearningGoal] = field(default_factory=list)
    
    # 学习历史
    learning_history: List[LearningHistory] = field(default_factory=list)
    
    # 统计信息
    total_study_time_hours: float = 0.0
    total_concepts_learned: int = 0
    current_streak_days: int = 0
    longest_streak_days: int = 0
    
    # 元数据
    tags: List[str] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def update_mastery(self, concept_id: str, score: float):
        """更新概念掌握度"""
        if concept_id not in self.mastered_concepts:
            self.mastered_concepts[concept_id] = ConceptMastery(concept_id=concept_id)
        
        self.mastered_concepts[concept_id].update_mastery(score)
        
        # 更新薄弱概念列表
        if score < 0.5 and concept_id not in self.weak_concepts:
            self.weak_concepts.append(concept_id)
        elif score >= 0.7 and concept_id in self.weak_concepts:
            self.weak_concepts.remove(concept_id)
        
        self.updated_at = datetime.now()
    
    def get_concept_mastery(self, concept_id: str) -> float:
        """获取概念掌握度"""
        if concept_id in self.mastered_concepts:
            return self.mastered_concepts[concept_id].mastery_level
        return 0.0
    
    def is_concept_mastered(self, concept_id: str, threshold: float = 0.7) -> bool:
        """判断概念是否已掌握"""
        return self.get_concept_mastery(concept_id) >= threshold
    
    def get_mastered_concept_ids(self, threshold: float = 0.7) -> Set[str]:
        """获取已掌握的概念ID集合"""
        return {
            cid for cid, mastery in self.mastered_concepts.items()
            if mastery.mastery_level >= threshold
        }
    
    def get_target_concepts(self) -> List[str]:
        """获取所有目标概念"""
        targets = set()
        for goal in self.active_goals:
            targets.update(goal.target_concepts)
        return list(targets)
    
    def add_goal(self, goal: LearningGoal):
        """添加学习目标"""
        self.active_goals.append(goal)
        self.updated_at = datetime.now()
    
    def complete_goal(self, goal_id: str):
        """完成学习目标"""
        for goal in self.active_goals:
            if goal.goal_id == goal_id:
                self.active_goals.remove(goal)
                self.completed_goals.append(goal)
                break
        self.updated_at = datetime.now()
    
    def record_learning_session(self, session: LearningHistory):
        """记录学习会话"""
        self.learning_history.append(session)
        self.total_study_time_hours += session.duration_minutes / 60
        
        if session.completion_rate >= 0.8:
            self.total_concepts_learned += 1
        
        self.updated_at = datetime.now()
    
    def get_learning_statistics(self) -> Dict[str, Any]:
        """获取学习统计信息"""
        if not self.learning_history:
            return {
                "total_sessions": 0,
                "average_session_duration": 0,
                "average_performance": 0,
                "study_consistency": 0
            }
        
        total_sessions = len(self.learning_history)
        avg_duration = sum(h.duration_minutes for h in self.learning_history) / total_sessions
        avg_performance = sum(h.performance_score for h in self.learning_history) / total_sessions
        
        # 计算学习一致性（最近7天学习天数占比）
        recent_days = set()
        week_ago = datetime.now() - timedelta(days=7)
        for h in self.learning_history:
            if h.start_time > week_ago:
                recent_days.add(h.start_time.date())
        consistency = len(recent_days) / 7.0
        
        return {
            "total_sessions": total_sessions,
            "average_session_duration": round(avg_duration, 2),
            "average_performance": round(avg_performance, 2),
            "study_consistency": round(consistency, 2),
            "total_study_hours": round(self.total_study_time_hours, 2),
            "concepts_mastered": len(self.get_mastered_concept_ids()),
            "weak_concepts_count": len(self.weak_concepts)
        }
    
    def to_dict(self) -> Dict[str, Any]:
        """转换为字典"""
        return {
            "user_id": self.user_id,
            "name": self.name,
            "email": self.email,
            "created_at": self.created_at.isoformat(),
            "updated_at": self.updated_at.isoformat(),
            "mastered_concepts": {
                cid: {
                    "mastery_level": m.mastery_level,
                    "study_count": m.study_count,
                    "last_studied": m.last_studied.isoformat() if m.last_studied else None
                }
                for cid, m in self.mastered_concepts.items()
            },
            "weak_concepts": self.weak_concepts,
            "learning_style": self.learning_preference.get_dominant_style().value,
            "daily_hours": self.time_preference.daily_hours,
            "active_goals": len(self.active_goals),
            "statistics": self.get_learning_statistics()
        }
    
    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'UserProfile':
        """从字典创建用户画像"""
        profile = cls(
            user_id=data.get("user_id", str(uuid.uuid4())),
            name=data.get("name", ""),
            email=data.get("email", "")
        )
        
        # 恢复掌握度信息
        for cid, mdata in data.get("mastered_concepts", {}).items():
            mastery = ConceptMastery(
                concept_id=cid,
                mastery_level=mdata.get("mastery_level", 0),
                study_count=mdata.get("study_count", 0)
            )
            if mdata.get("last_studied"):
                mastery.last_studied = datetime.fromisoformat(mdata["last_studied"])
            profile.mastered_concepts[cid] = mastery
        
        profile.weak_concepts = data.get("weak_concepts", [])
        return profile


# 预设用户画像模板
PRESET_PROFILES = {
    "beginner_student": {
        "name": "初学者学生",
        "description": "刚接触高等数学的学生，需要打好基础",
        "learning_preference": {
            "style_weights": {
                LearningStyle.VISUAL: 0.4,
                LearningStyle.TEXTUAL: 0.3,
                LearningStyle.INTERACTIVE: 0.2,
                LearningStyle.MULTIMODAL: 0.1
            },
            "prefer_examples": True,
            "prefer_intuition": True,
            "pace_preference": "slow"
        },
        "time_preference": {
            "daily_hours": 1.5,
            "weekly_days": 5,
            "session_duration": 30
        }
    },
    "advanced_learner": {
        "name": "进阶学习者",
        "description": "有一定基础，希望深入学习特定领域",
        "learning_preference": {
            "style_weights": {
                LearningStyle.TEXTUAL: 0.4,
                LearningStyle.VISUAL: 0.2,
                LearningStyle.INTERACTIVE: 0.3,
                LearningStyle.MULTIMODAL: 0.1
            },
            "prefer_proofs": True,
            "prefer_applications": True,
            "pace_preference": "moderate"
        },
        "time_preference": {
            "daily_hours": 3.0,
            "weekly_days": 6,
            "session_duration": 60
        }
    },
    "researcher": {
        "name": "研究者",
        "description": "专注于前沿研究，需要快速掌握新概念",
        "learning_preference": {
            "style_weights": {
                LearningStyle.TEXTUAL: 0.5,
                LearningStyle.VISUAL: 0.3,
                LearningStyle.INTERACTIVE: 0.1,
                LearningStyle.MULTIMODAL: 0.1
            },
            "prefer_proofs": True,
            "pace_preference": "fast"
        },
        "time_preference": {
            "daily_hours": 4.0,
            "weekly_days": 7,
            "session_duration": 90
        }
    },
    "visual_learner": {
        "name": "视觉型学习者",
        "description": "偏好通过图表和可视化内容学习",
        "learning_preference": {
            "style_weights": {
                LearningStyle.VISUAL: 0.7,
                LearningStyle.TEXTUAL: 0.1,
                LearningStyle.INTERACTIVE: 0.1,
                LearningStyle.MULTIMODAL: 0.1
            },
            "prefer_examples": True,
            "prefer_intuition": True
        },
        "time_preference": {
            "daily_hours": 2.0,
            "weekly_days": 5,
            "session_duration": 45
        }
    },
    "practical_learner": {
        "name": "实践型学习者",
        "description": "偏好通过练习和应用来学习",
        "learning_preference": {
            "style_weights": {
                LearningStyle.INTERACTIVE: 0.6,
                LearningStyle.VISUAL: 0.2,
                LearningStyle.TEXTUAL: 0.1,
                LearningStyle.MULTIMODAL: 0.1
            },
            "prefer_applications": True,
            "prefer_examples": True
        },
        "time_preference": {
            "daily_hours": 2.5,
            "weekly_days": 5,
            "session_duration": 50
        }
    }
}


def create_preset_profile(preset_type: str, name: str = "", email: str = "") -> UserProfile:
    """从预设模板创建用户画像"""
    if preset_type not in PRESET_PROFILES:
        raise ValueError(f"Unknown preset type: {preset_type}")
    
    preset = PRESET_PROFILES[preset_type]
    profile = UserProfile(name=name or preset["name"], email=email)
    
    # 应用预设偏好
    lp_data = preset.get("learning_preference", {})
    profile.learning_preference.style_weights = lp_data.get("style_weights", profile.learning_preference.style_weights)
    profile.learning_preference.prefer_examples = lp_data.get("prefer_examples", True)
    profile.learning_preference.prefer_proofs = lp_data.get("prefer_proofs", True)
    profile.learning_preference.prefer_applications = lp_data.get("prefer_applications", True)
    profile.learning_preference.prefer_intuition = lp_data.get("prefer_intuition", True)
    profile.learning_preference.pace_preference = lp_data.get("pace_preference", "moderate")
    
    tp_data = preset.get("time_preference", {})
    profile.time_preference.daily_hours = tp_data.get("daily_hours", 2.0)
    profile.time_preference.weekly_days = tp_data.get("weekly_days", 5)
    profile.time_preference.session_duration = tp_data.get("session_duration", 45)
    
    return profile


# 用户画像评估问卷
USER_PROFILE_QUESTIONS = [
    {
        "id": "learning_style_1",
        "category": "learning_style",
        "question": "当你学习新的数学概念时，你更倾向于：",
        "options": [
            {"text": "查看图表、可视化表示和图形演示", "style": LearningStyle.VISUAL, "weight": 1.0},
            {"text": "阅读详细的文字说明和数学定义", "style": LearningStyle.TEXTUAL, "weight": 1.0},
            {"text": "通过实际操作、练习和互动来学习", "style": LearningStyle.INTERACTIVE, "weight": 1.0},
            {"text": "结合多种方式，根据需要灵活选择", "style": LearningStyle.MULTIMODAL, "weight": 1.0}
        ]
    },
    {
        "id": "learning_style_2",
        "category": "learning_style",
        "question": "在理解数学证明时，你最看重：",
        "options": [
            {"text": "证明过程的直观可视化表示", "style": LearningStyle.VISUAL, "weight": 0.8},
            {"text": "严谨的符号推导和逻辑链条", "style": LearningStyle.TEXTUAL, "weight": 0.8},
            {"text": "自己动手尝试证明", "style": LearningStyle.INTERACTIVE, "weight": 0.8},
            {"text": "多种理解方式结合", "style": LearningStyle.MULTIMODAL, "weight": 0.8}
        ]
    },
    {
        "id": "content_preference_1",
        "category": "content",
        "question": "你更喜欢哪种类型的学习内容：",
        "options": [
            {"text": "大量的具体例子和应用场景", "preference": "examples"},
            {"text": "严格的定义、定理和证明", "preference": "proofs"},
            {"text": "实际问题的解决方法", "preference": "applications"},
            {"text": "直观的解释和概念说明", "preference": "intuition"}
        ]
    },
    {
        "id": "pace_preference",
        "category": "pace",
        "question": "你希望的学习节奏是：",
        "options": [
            {"text": "缓慢而深入，确保完全理解", "pace": "slow"},
            {"text": "适中，平衡深度和进度", "pace": "moderate"},
            {"text": "快速，快速建立整体框架", "pace": "fast"}
        ]
    },
    {
        "id": "time_availability",
        "category": "time",
        "question": "你每天可用于学习的时间是：",
        "options": [
            {"text": "少于1小时", "daily_hours": 0.5},
            {"text": "1-2小时", "daily_hours": 1.5},
            {"text": "2-3小时", "daily_hours": 2.5},
            {"text": "3小时以上", "daily_hours": 4.0}
        ]
    }
]


if __name__ == "__main__":
    # 测试代码
    print("=== 用户画像模型测试 ===")
    
    # 创建用户画像
    user = UserProfile(name="张三", email="zhangsan@example.com")
    print(f"\n创建用户: {user.name} (ID: {user.user_id})")
    
    # 更新掌握度
    user.update_mastery("set_theory", 0.85)
    user.update_mastery("group_theory", 0.45)
    user.update_mastery("topology", 0.2)
    print(f"\n掌握度更新:")
    print(f"  - 集合论: {user.get_concept_mastery('set_theory'):.2f}")
    print(f"  - 群论: {user.get_concept_mastery('group_theory'):.2f}")
    print(f"  - 拓扑学: {user.get_concept_mastery('topology'):.2f}")
    print(f"  - 薄弱概念: {user.weak_concepts}")
    
    # 添加学习目标
    goal = LearningGoal(
        name="掌握代数拓扑基础",
        target_concepts=["homology", "homotopy", "fundamental_group"],
        priority=LearningGoalPriority.HIGH,
        deadline=datetime.now() + timedelta(days=30)
    )
    user.add_goal(goal)
    print(f"\n添加学习目标: {goal.name}")
    print(f"  - 目标概念: {goal.target_concepts}")
    print(f"  - 剩余天数: {goal.get_days_remaining()}")
    
    # 记录学习会话
    session = LearningHistory(
        concept_id="set_theory",
        duration_minutes=60,
        completion_rate=0.9,
        performance_score=0.85
    )
    user.record_learning_session(session)
    
    # 获取统计信息
    stats = user.get_learning_statistics()
    print(f"\n学习统计:")
    for key, value in stats.items():
        print(f"  - {key}: {value}")
    
    # 测试预设模板
    print("\n\n=== 预设模板测试 ===")
    for preset_type in PRESET_PROFILES.keys():
        preset_user = create_preset_profile(preset_type, name=f"{preset_type}_user")
        print(f"\n{preset_type}:")
        print(f"  - 主导学习风格: {preset_user.learning_preference.get_dominant_style().value}")
        print(f"  - 每日学习时间: {preset_user.time_preference.daily_hours}小时")
    
    print("\n=== 测试完成 ===")
