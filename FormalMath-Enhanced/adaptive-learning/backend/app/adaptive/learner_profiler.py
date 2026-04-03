"""
学习者特征分析模块
分析学习者的认知风格、先验知识和学习偏好
"""
from typing import Dict, List, Any, Optional, Tuple
from collections import defaultdict
import numpy as np
from datetime import datetime, timedelta

from ..schemas import (
    UserProfile, LearningActivity, CognitiveStyle, 
    LearningPreference, DifficultyLevel
)
from ..knowledge_graph import get_knowledge_graph


class LearnerProfiler:
    """学习者画像分析器"""
    
    def __init__(self):
        self.kg = get_knowledge_graph()
    
    def analyze_cognitive_style(self, activities: List[LearningActivity]) -> CognitiveStyle:
        """
        分析认知风格
        
        基于学习活动模式推断认知风格
        """
        if not activities:
            return CognitiveStyle.MIXED
        
        # 统计不同资源类型的学习时间
        resource_time = defaultdict(int)
        
        for activity in activities:
            perf = activity.performance_data
            if 'resource_type' in perf:
                resource_time[perf['resource_type']] += activity.duration
        
        total_time = sum(resource_time.values())
        if total_time == 0:
            return CognitiveStyle.MIXED
        
        # 计算比例
        visual_ratio = (resource_time.get('video', 0) + 
                       resource_time.get('diagram', 0)) / total_time
        reading_ratio = resource_time.get('text', 0) / total_time
        kinesthetic_ratio = resource_time.get('interactive', 0) / total_time
        
        # 确定主导风格
        scores = {
            CognitiveStyle.VISUAL: visual_ratio,
            CognitiveStyle.READING: reading_ratio,
            CognitiveStyle.KINESTHETIC: kinesthetic_ratio,
        }
        
        dominant = max(scores, key=scores.get)
        
        # 如果最高比例小于40%，认为是混合型
        if scores[dominant] < 0.4:
            return CognitiveStyle.MIXED
        
        return dominant
    
    def analyze_learning_preference(self, activities: List[LearningActivity]) -> LearningPreference:
        """
        分析学习偏好
        
        基于学习顺序偏好推断
        """
        if len(activities) < 3:
            return LearningPreference.BALANCED
        
        # 分析学习顺序模式
        theory_first = 0
        example_first = 0
        practice_first = 0
        
        for i in range(len(activities) - 1):
            curr_type = activities[i].activity_type
            next_type = activities[i + 1].activity_type
            
            if curr_type == 'theory' and next_type in ['example', 'exercise']:
                theory_first += 1
            elif curr_type == 'example' and next_type in ['theory', 'exercise']:
                example_first += 1
            elif curr_type == 'exercise' and next_type in ['theory', 'example']:
                practice_first += 1
        
        total = theory_first + example_first + practice_first
        if total == 0:
            return LearningPreference.BALANCED
        
        # 确定主导偏好
        preferences = [
            (LearningPreference.THEORY_FIRST, theory_first),
            (LearningPreference.EXAMPLE_FIRST, example_first),
            (LearningPreference.PRACTICE_FIRST, practice_first),
        ]
        
        dominant = max(preferences, key=lambda x: x[1])
        
        # 需要明显领先
        if dominant[1] / total < 0.5:
            return LearningPreference.BALANCED
        
        return dominant[0]
    
    def assess_mastery(self, user_id: str, concept_id: str, 
                       activities: List[LearningActivity]) -> float:
        """
        评估概念掌握度
        
        基于学习活动和测试成绩综合评估
        
        Returns:
            0.0 - 1.0 的掌握度分数
        """
        concept_activities = [
            a for a in activities 
            if a.concept_id == concept_id
        ]
        
        if not concept_activities:
            return 0.0
        
        # 1. 基于测试成绩的掌握度
        quiz_scores = [
            a.score for a in concept_activities 
            if a.activity_type == 'quiz' and a.score is not None
        ]
        
        quiz_mastery = np.mean(quiz_scores) / 100 if quiz_scores else 0.0
        
        # 2. 基于练习表现的掌握度
        exercise_scores = [
            a.score for a in concept_activities 
            if a.activity_type == 'exercise' and a.score is not None
        ]
        
        exercise_mastery = np.mean(exercise_scores) / 100 if exercise_scores else 0.0
        
        # 3. 基于学习时间充足度的掌握度
        total_study_time = sum(
            a.duration for a in concept_activities 
            if a.activity_type in ['study', 'exercise']
        )
        
        concept = self.kg.get_concept(concept_id)
        expected_time = concept.estimated_time if concept else 30
        time_mastery = min(total_study_time / (expected_time * 1.5), 1.0)
        
        # 4. 基于复习次数的巩固度
        review_count = len([
            a for a in concept_activities 
            if a.activity_type == 'review'
        ])
        review_mastery = min(review_count * 0.1, 0.2)
        
        # 综合计算 (加权平均)
        mastery = (
            quiz_mastery * 0.35 +
            exercise_mastery * 0.30 +
            time_mastery * 0.25 +
            review_mastery * 0.10
        )
        
        return round(min(mastery, 1.0), 3)
    
    def detect_struggle_areas(self, user_id: str, 
                              activities: List[LearningActivity],
                              threshold: float = 0.4) -> List[Tuple[str, float]]:
        """
        检测学习困难领域
        
        Returns:
            困难概念列表 (concept_id, difficulty_score)
        """
        struggles = []
        
        # 按概念分组的活动
        concept_activities = defaultdict(list)
        for activity in activities:
            concept_activities[activity.concept_id].append(activity)
        
        for concept_id, acts in concept_activities.items():
            # 计算困难指标
            
            # 1. 低分率
            scores = [a.score for a in acts if a.score is not None]
            low_score_rate = sum(1 for s in scores if s < 60) / len(scores) if scores else 0
            
            # 2. 高重试率
            exercise_attempts = len([a for a in acts if a.activity_type == 'exercise'])
            retry_rate = min(exercise_attempts / 3, 1.0) if exercise_attempts > 3 else 0
            
            # 3. 长时间未掌握
            study_time = sum(a.duration for a in acts)
            concept = self.kg.get_concept(concept_id)
            expected_time = concept.estimated_time if concept else 30
            overtime_ratio = study_time / expected_time if expected_time > 0 else 0
            
            # 综合困难分数
            difficulty_score = (
                low_score_rate * 0.4 +
                retry_rate * 0.3 +
                min(overtime_ratio / 2, 0.3)
            )
            
            if difficulty_score > threshold:
                struggles.append((concept_id, difficulty_score))
        
        # 按困难程度排序
        struggles.sort(key=lambda x: x[1], reverse=True)
        return struggles
    
    def identify_gaps(self, user_id: str, 
                      target_concepts: List[str],
                      mastered_concepts: Dict[str, float]) -> List[str]:
        """
        识别知识缺口
        
        找出学习路径中缺少的先修知识
        """
        gaps = set()
        
        for target in target_concepts:
            # 获取所有先修
            prerequisites = self.kg.get_prerequisites(target, recursive=True)
            
            for prereq in prerequisites:
                # 检查是否已掌握
                if prereq not in mastered_concepts:
                    gaps.add(prereq)
                elif mastered_concepts[prereq] < 0.6:  # 掌握度不足
                    gaps.add(prereq)
        
        return list(gaps)
    
    def calculate_readiness(self, user_id: str, 
                           concept_id: str,
                           mastered_concepts: Dict[str, float]) -> float:
        """
        计算学习准备度
        
        评估学习者是否准备好学习某个概念
        
        Returns:
            0.0 - 1.0 的准备度分数
        """
        # 获取直接先修
        prerequisites = self.kg.get_prerequisites(concept_id, recursive=False)
        
        if not prerequisites:
            return 1.0
        
        # 计算先修掌握度
        readiness_scores = []
        for prereq in prerequisites:
            if prereq in mastered_concepts:
                readiness_scores.append(mastered_concepts[prereq])
            else:
                readiness_scores.append(0.0)
        
        # 最低掌握度决定准备度
        return min(readiness_scores) if readiness_scores else 0.0
    
    def generate_user_profile(self, user_id: str, 
                              activities: List[LearningActivity]) -> UserProfile:
        """
        生成完整用户画像
        """
        # 分析认知风格
        cognitive_style = self.analyze_cognitive_style(activities)
        
        # 分析学习偏好
        learning_preference = self.analyze_learning_preference(activities)
        
        # 评估已掌握概念
        mastered_concepts = {}
        concept_ids = set(a.concept_id for a in activities)
        for concept_id in concept_ids:
            mastery = self.assess_mastery(user_id, concept_id, activities)
            if mastery >= 0.6:  # 掌握度阈值
                mastered_concepts[concept_id] = mastery
        
        # 统计信息
        total_time = sum(a.duration for a in activities)
        completed = len(mastered_concepts)
        
        # 计算平均分数
        scores = [a.score for a in activities if a.score is not None]
        avg_score = np.mean(scores) if scores else 0.0
        
        # 确定当前水平
        if completed < 5:
            level = DifficultyLevel.BEGINNER
        elif completed < 15:
            level = DifficultyLevel.INTERMEDIATE
        elif completed < 30:
            level = DifficultyLevel.ADVANCED
        else:
            level = DifficultyLevel.EXPERT
        
        return UserProfile(
            user_id=user_id,
            cognitive_style=cognitive_style,
            learning_preference=learning_preference,
            current_level=level,
            mastered_concepts=mastered_concepts,
            learning_history=[a.model_dump() for a in activities[-20:]],  # 最近20条
            total_study_time=total_time,
            completed_concepts=completed,
            average_score=round(avg_score, 2)
        )
    
    def recommend_difficulty(self, user_profile: UserProfile, 
                            concept_id: str) -> Tuple[DifficultyLevel, float]:
        """
        推荐学习难度
        
        根据用户画像和概念复杂度推荐合适的难度级别
        
        Returns:
            (推荐难度, 置信度)
        """
        concept = self.kg.get_concept(concept_id)
        if not concept:
            return user_profile.current_level, 0.5
        
        # 计算概念复杂度
        complexity = self.kg.calculate_complexity(concept_id)
        
        # 基于历史表现调整
        recent_scores = []
        for activity_data in user_profile.learning_history[-10:]:
            if 'score' in activity_data and activity_data['score'] is not None:
                recent_scores.append(activity_data['score'])
        
        avg_recent = np.mean(recent_scores) if recent_scores else 70
        
        # 难度调整因子
        if avg_recent > 85:
            adjustment = 1  # 提升难度
        elif avg_recent < 60:
            adjustment = -1  # 降低难度
        else:
            adjustment = 0
        
        # 确定推荐难度
        levels = [DifficultyLevel.BEGINNER, DifficultyLevel.INTERMEDIATE,
                 DifficultyLevel.ADVANCED, DifficultyLevel.EXPERT]
        
        current_idx = levels.index(user_profile.current_level)
        target_idx = min(max(current_idx + adjustment, 0), len(levels) - 1)
        
        # 概念本身难度
        concept_idx = levels.index(concept.difficulty)
        
        # 综合 (取用户能力和概念难度的平衡)
        recommended_idx = int((target_idx + concept_idx) / 2)
        
        confidence = min(avg_recent / 100, 0.9) if recent_scores else 0.5
        
        return levels[recommended_idx], round(confidence, 2)
