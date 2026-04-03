"""
学习者特征分析服务
提供学习者画像管理、学习风格评估、先验知识评估等功能
"""

from typing import Dict, List, Optional, Any
from datetime import datetime
import json
import os

from models.learner import (
    LearnerProfile, LearningStyleProfile, GoalSetting, TimeAvailability,
    LearningStyle, AbilityLevel, LearningRecord, LearnerProgress,
    LEARNING_STYLE_QUESTIONS
)


class LearnerService:
    """学习者服务"""
    
    def __init__(self, data_dir: str = "data/learner_profiles"):
        self.data_dir = data_dir
        self.learners: Dict[str, LearnerProfile] = {}
        self._ensure_data_dir()
        self._load_learners()
    
    def _ensure_data_dir(self):
        """确保数据目录存在"""
        os.makedirs(self.data_dir, exist_ok=True)
    
    def _load_learners(self):
        """加载学习者数据"""
        if not os.path.exists(self.data_dir):
            return
        
        for filename in os.listdir(self.data_dir):
            if filename.endswith('.json'):
                filepath = os.path.join(self.data_dir, filename)
                try:
                    with open(filepath, 'r', encoding='utf-8') as f:
                        data = json.load(f)
                        learner = self._dict_to_learner(data)
                        self.learners[learner.learner_id] = learner
                except Exception as e:
                    print(f"Error loading learner from {filename}: {e}")
    
    def _save_learner(self, learner: LearnerProfile):
        """保存学习者数据"""
        filepath = os.path.join(self.data_dir, f"{learner.learner_id}.json")
        with open(filepath, 'w', encoding='utf-8') as f:
            json.dump(self._learner_to_dict(learner), f, ensure_ascii=False, indent=2)
    
    def _learner_to_dict(self, learner: LearnerProfile) -> Dict[str, Any]:
        """将学习者对象转换为字典"""
        return {
            "learner_id": learner.learner_id,
            "name": learner.name,
            "email": learner.email,
            "knowledge_state": learner.knowledge_state,
            "ability_level": learner.ability_level,
            "learning_style": {
                "visual_score": learner.learning_style.visual_score,
                "auditory_score": learner.learning_style.auditory_score,
                "kinesthetic_score": learner.learning_style.kinesthetic_score,
                "reading_score": learner.learning_style.reading_score
            },
            "prior_knowledge": learner.prior_knowledge,
            "learning_goals": [
                {
                    "goal_id": g.goal_id,
                    "target_concepts": g.target_concepts,
                    "deadline": g.deadline.isoformat() if g.deadline else None,
                    "target_level": g.target_level.value,
                    "description": g.description,
                    "priority": g.priority
                }
                for g in learner.learning_goals
            ],
            "time_availability": {
                "daily_available_hours": learner.time_availability.daily_available_hours,
                "weekly_available_days": learner.time_availability.weekly_available_days,
                "preferred_study_time": learner.time_availability.preferred_study_time,
                "max_session_duration": learner.time_availability.max_session_duration,
                "weekly_schedule": learner.time_availability.weekly_schedule
            },
            "preferences": learner.preferences,
            "created_at": learner.created_at.isoformat(),
            "updated_at": learner.updated_at.isoformat()
        }
    
    def _dict_to_learner(self, data: Dict[str, Any]) -> LearnerProfile:
        """将字典转换为学习者对象"""
        learner = LearnerProfile(
            learner_id=data.get("learner_id", ""),
            name=data.get("name", ""),
            email=data.get("email", ""),
            knowledge_state=data.get("knowledge_state", {}),
            ability_level=data.get("ability_level", {}),
            prior_knowledge=data.get("prior_knowledge", {}),
            preferences=data.get("preferences", {})
        )
        
        # 恢复学习风格
        if "learning_style" in data:
            style_data = data["learning_style"]
            learner.learning_style = LearningStyleProfile(
                visual_score=style_data.get("visual_score", 0),
                auditory_score=style_data.get("auditory_score", 0),
                kinesthetic_score=style_data.get("kinesthetic_score", 0),
                reading_score=style_data.get("reading_score", 0)
            )
        
        # 恢复学习目标
        if "learning_goals" in data:
            for goal_data in data["learning_goals"]:
                goal = GoalSetting(
                    goal_id=goal_data.get("goal_id", ""),
                    target_concepts=goal_data.get("target_concepts", []),
                    deadline=datetime.fromisoformat(goal_data["deadline"]) if goal_data.get("deadline") else None,
                    target_level=AbilityLevel(goal_data.get("target_level", 1)),
                    description=goal_data.get("description", ""),
                    priority=goal_data.get("priority", 1)
                )
                learner.learning_goals.append(goal)
        
        # 恢复时间可用性
        if "time_availability" in data:
            ta_data = data["time_availability"]
            learner.time_availability = TimeAvailability(
                daily_available_hours=ta_data.get("daily_available_hours", 2.0),
                weekly_available_days=ta_data.get("weekly_available_days", 5),
                preferred_study_time=ta_data.get("preferred_study_time", "evening"),
                max_session_duration=ta_data.get("max_session_duration", 60),
                weekly_schedule=ta_data.get("weekly_schedule", {})
            )
        
        # 恢复时间戳
        if "created_at" in data:
            learner.created_at = datetime.fromisoformat(data["created_at"])
        if "updated_at" in data:
            learner.updated_at = datetime.fromisoformat(data["updated_at"])
        
        return learner
    
    def create_learner(self, name: str, email: str) -> LearnerProfile:
        """创建新学习者"""
        learner = LearnerProfile(name=name, email=email)
        self.learners[learner.learner_id] = learner
        self._save_learner(learner)
        return learner
    
    def get_learner(self, learner_id: str) -> Optional[LearnerProfile]:
        """获取学习者"""
        return self.learners.get(learner_id)
    
    def update_learner(self, learner_id: str, updates: Dict[str, Any]) -> Optional[LearnerProfile]:
        """更新学习者信息"""
        learner = self.learners.get(learner_id)
        if not learner:
            return None
        
        for key, value in updates.items():
            if hasattr(learner, key):
                setattr(learner, key, value)
        
        learner.updated_at = datetime.now()
        self._save_learner(learner)
        return learner
    
    def import_diagnosis_result(self, learner_id: str, diagnosis_result: Dict[str, Any]) -> Optional[LearnerProfile]:
        """从认知诊断系统导入结果"""
        learner = self.learners.get(learner_id)
        if not learner:
            return None
        
        learner.update_from_diagnosis(diagnosis_result)
        self._save_learner(learner)
        return learner
    
    def assess_learning_style(self, learner_id: str, answers: Dict[str, str]) -> Optional[LearningStyleProfile]:
        """
        评估学习风格
        answers: {question_id: selected_option_style}
        """
        learner = self.learners.get(learner_id)
        if not learner:
            return None
        
        # 计算各风格得分
        scores = {"visual": 0, "auditory": 0, "kinesthetic": 0, "reading": 0}
        
        for question_id, selected_style in answers.items():
            # 查找问题权重
            for question in LEARNING_STYLE_QUESTIONS:
                if question["id"] == question_id:
                    for option in question["options"]:
                        if option["style"] == selected_style:
                            scores[selected_style] += option["weight"]
                            break
        
        # 归一化得分
        total = sum(scores.values())
        if total > 0:
            for style in scores:
                scores[style] /= total
        
        # 更新学习者画像
        learner.learning_style = LearningStyleProfile(
            visual_score=scores["visual"],
            auditory_score=scores["auditory"],
            kinesthetic_score=scores["kinesthetic"],
            reading_score=scores["reading"]
        )
        
        self._save_learner(learner)
        return learner.learning_style
    
    def get_learning_style_questions(self) -> List[Dict[str, Any]]:
        """获取学习风格评估问卷"""
        return LEARNING_STYLE_QUESTIONS
    
    def assess_prior_knowledge(
        self,
        learner_id: str,
        concept_checks: Dict[str, bool]
    ) -> Dict[str, float]:
        """
        评估先验知识
        concept_checks: {concept_id: is_familiar}
        """
        learner = self.learners.get(learner_id)
        if not learner:
            return {}
        
        prior_knowledge = {}
        for concept_id, is_familiar in concept_checks.items():
            if is_familiar:
                # 如果熟悉，假设掌握度为0.6
                prior_knowledge[concept_id] = 0.6
            else:
                prior_knowledge[concept_id] = 0.0
        
        learner.prior_knowledge = prior_knowledge
        self._save_learner(learner)
        return prior_knowledge
    
    def set_learning_goal(
        self,
        learner_id: str,
        target_concepts: List[str],
        deadline: Optional[datetime] = None,
        target_level: int = 1,
        description: str = ""
    ) -> Optional[GoalSetting]:
        """设置学习目标"""
        learner = self.learners.get(learner_id)
        if not learner:
            return None
        
        goal = GoalSetting(
            target_concepts=target_concepts,
            deadline=deadline,
            target_level=AbilityLevel(target_level),
            description=description
        )
        
        learner.learning_goals.append(goal)
        self._save_learner(learner)
        return goal
    
    def set_time_availability(
        self,
        learner_id: str,
        daily_hours: float,
        weekly_days: int,
        preferred_time: str = "evening",
        max_session: int = 60
    ) -> Optional[TimeAvailability]:
        """设置可用时间"""
        learner = self.learners.get(learner_id)
        if not learner:
            return None
        
        learner.time_availability = TimeAvailability(
            daily_available_hours=daily_hours,
            weekly_available_days=weekly_days,
            preferred_study_time=preferred_time,
            max_session_duration=max_session
        )
        
        self._save_learner(learner)
        return learner.time_availability
    
    def add_learning_record(
        self,
        learner_id: str,
        concept_id: str,
        duration: int,
        performance: float,
        feedback: str = ""
    ) -> Optional[LearningRecord]:
        """添加学习记录"""
        learner = self.learners.get(learner_id)
        if not learner:
            return None
        
        record = LearningRecord(
            learner_id=learner_id,
            concept_id=concept_id,
            duration_minutes=duration,
            performance_score=performance,
            feedback=feedback
        )
        
        learner.learning_history.append({
            "concept_id": concept_id,
            "duration": duration,
            "performance": performance,
            "timestamp": datetime.now().isoformat()
        })
        
        self._save_learner(learner)
        return record
    
    def get_learner_summary(self, learner_id: str) -> Optional[Dict[str, Any]]:
        """获取学习者摘要信息"""
        learner = self.learners.get(learner_id)
        if not learner:
            return None
        
        return {
            "learner_id": learner.learner_id,
            "name": learner.name,
            "overall_ability": learner.calculate_overall_ability(),
            "learning_style": learner.learning_style.dominant_style.value,
            "learning_style_scores": {
                "visual": learner.learning_style.visual_score,
                "auditory": learner.learning_style.auditory_score,
                "kinesthetic": learner.learning_style.kinesthetic_score,
                "reading": learner.learning_style.reading_score
            },
            "weekly_study_hours": learner.get_weekly_study_hours(),
            "goals_count": len(learner.learning_goals),
            "concepts_mastered": sum(
                1 for mastery in learner.knowledge_state.values()
                if mastery >= 0.7
            ),
            "total_concepts_attempted": len(learner.knowledge_state)
        }
    
    def list_learners(self) -> List[Dict[str, str]]:
        """列出所有学习者"""
        return [
            {
                "learner_id": learner.learner_id,
                "name": learner.name,
                "email": learner.email
            }
            for learner in self.learners.values()
        ]
