"""
FormalMath 评估系统核心模块

Author: FormalMath Team
Version: 1.0
Date: 2026-04-02
"""

import numpy as np
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
from datetime import datetime, timedelta
from enum import Enum
import json


class EvaluationType(Enum):
    """评价类型"""
    PROCESS = "process"      # 过程性评价
    GROWTH = "growth"        # 增值评价
    PERFORMANCE = "performance"  # 表现性评价
    CREATIVE = "creative"    # 发散思维评价


@dataclass
class ParticipationScore:
    """参与度评分"""
    time: float
    coverage: float
    activity: float
    overall: float


@dataclass
class InitiativeScore:
    """主动性评分"""
    exploration: float
    questioning: float
    reflection: float
    extension: float
    overall: float


@dataclass
class PersistenceScore:
    """坚持性评分"""
    continuity: float
    regularity: float
    completion: float
    overall: float


@dataclass
class EvaluationResult:
    """评价结果"""
    learner_id: str
    evaluation_type: EvaluationType
    period: str
    participation: Optional[ParticipationScore] = None
    initiative: Optional[InitiativeScore] = None
    persistence: Optional[PersistenceScore] = None
    overall_score: float = 0.0
    summary: str = ""
    recommendations: List[Dict] = None
    
    def __post_init__(self):
        if self.recommendations is None:
            self.recommendations = []
    
    def to_dict(self) -> Dict:
        """转换为字典"""
        return {
            'learner_id': self.learner_id,
            'evaluation_type': self.evaluation_type.value,
            'period': self.period,
            'overall_score': self.overall_score,
            'summary': self.summary,
            'recommendations': self.recommendations
        }


@dataclass
class BehaviorData:
    """学习行为数据"""
    # 时间维度
    session_duration: int = 0
    daily_durations: List[int] = None
    weekly_frequency: int = 0
    days_count: int = 0
    
    # 内容维度
    contents_viewed: int = 0
    total_contents: int = 100
    videos_completed: int = 0
    total_videos: int = 20
    exercises_completed: int = 0
    total_exercises: int = 50
    
    # 交互维度
    discussions_joined: int = 0
    questions_asked: int = 0
    notes_created: int = 0
    searches: int = 0
    
    # 认知维度
    errors_made: int = 0
    error_reviews: int = 0
    
    # 连续学习
    consecutive_days: int = 0
    max_consecutive_days: int = 0
    
    def __post_init__(self):
        if self.daily_durations is None:
            self.daily_durations = []


class ProcessEvaluationSystem:
    """
    过程性评价系统
    
    核心功能：
    1. 学习参与度评估
    2. 学习主动性评估
    3. 学习坚持性评估
    4. 生成评价报告
    """
    
    def __init__(self):
        self.weights = {
            'participation': 0.30,
            'initiative': 0.25,
            'persistence': 0.25,
            'strategy': 0.20
        }
    
    def evaluate(self, learner_id: str, 
                 start_date: datetime,
                 end_date: datetime,
                 behavior_data: BehaviorData) -> EvaluationResult:
        """
        执行过程性评价
        
        Args:
            learner_id: 学习者ID
            start_date: 开始日期
            end_date: 结束日期
            behavior_data: 学习行为数据
        """
        print(f"[ProcessEvaluation] 评价学习者: {learner_id}")
        
        # 计算各维度得分
        participation = self._calc_participation(behavior_data)
        initiative = self._calc_initiative(behavior_data)
        persistence = self._calc_persistence(behavior_data)
        
        # 计算综合得分
        overall = (
            0.30 * participation.overall +
            0.25 * initiative.overall +
            0.25 * persistence.overall
        )
        
        # 生成总结和建议
        summary = self._generate_summary(
            participation, initiative, persistence
        )
        recommendations = self._generate_recommendations(
            participation, initiative, persistence
        )
        
        return EvaluationResult(
            learner_id=learner_id,
            evaluation_type=EvaluationType.PROCESS,
            period=f"{start_date.date()} to {end_date.date()}",
            participation=participation,
            initiative=initiative,
            persistence=persistence,
            overall_score=overall,
            summary=summary,
            recommendations=recommendations
        )
    
    def _calc_participation(self, data: BehaviorData) -> ParticipationScore:
        """计算参与度得分"""
        
        # 时间投入评分
        daily_avg = data.session_duration / max(data.days_count, 1)
        time_score = min(daily_avg / 3600, 1.0)  # 每天1小时满分
        
        # 学习频次评分
        frequency_score = min(data.weekly_frequency / 5, 1.0)  # 每周5次满分
        
        # 内容覆盖评分
        content_coverage = data.contents_viewed / max(data.total_contents, 1)
        coverage_score = min(content_coverage, 1.0)
        
        # 活动参与评分
        activity_score = (
            0.4 * min(data.discussions_joined / 3, 1.0) +
            0.3 * min(data.questions_asked / 2, 1.0) +
            0.3 * min(data.notes_created / 3, 1.0)
        )
        
        overall = 0.4 * time_score + 0.3 * coverage_score + 0.3 * activity_score
        
        return ParticipationScore(
            time=round(time_score, 2),
            coverage=round(coverage_score, 2),
            activity=round(activity_score, 2),
            overall=round(overall, 2)
        )
    
    def _calc_initiative(self, data: BehaviorData) -> InitiativeScore:
        """计算主动性得分"""
        
        # 主动探索
        exploration = (
            0.3 * min(data.searches / 5, 1.0) +
            0.4 * min(data.contents_viewed / max(data.total_contents * 1.5, 1), 1.0) +
            0.3 * min(data.notes_created / 3, 1.0)
        )
        
        # 主动提问
        questioning = min(data.questions_asked / 2, 1.0)
        
        # 主动反思
        reflection = (
            0.4 * min(data.notes_created / 3, 1.0) +
            0.35 * min(data.error_reviews / max(data.errors_made, 1), 1.0) +
            0.25 * 0.5  # 反思日志 (默认中等)
        )
        
        # 拓展学习
        extension = min(data.contents_viewed / max(data.total_contents, 1), 1.0)
        
        overall = 0.35 * exploration + 0.25 * questioning + 0.20 * reflection + 0.20 * extension
        
        return InitiativeScore(
            exploration=round(exploration, 2),
            questioning=round(questioning, 2),
            reflection=round(reflection, 2),
            extension=round(extension, 2),
            overall=round(overall, 2)
        )
    
    def _calc_persistence(self, data: BehaviorData) -> PersistenceScore:
        """计算坚持性得分"""
        
        # 持续学习
        continuity = (
            0.4 * min(data.max_consecutive_days / 7, 1.0) +
            0.3 * min(data.consecutive_days / 5, 1.0) +
            0.3 * min(data.days_count / 5, 1.0)
        )
        
        # 规律学习
        regularity = 0.7  # 简化计算
        
        # 目标完成
        exercise_completion = data.exercises_completed / max(data.total_exercises * 0.8, 1)
        video_completion = data.videos_completed / max(data.total_videos * 0.8, 1)
        completion = (exercise_completion + video_completion) / 2
        
        overall = 0.40 * continuity + 0.30 * regularity + 0.30 * completion
        
        return PersistenceScore(
            continuity=round(continuity, 2),
            regularity=round(regularity, 2),
            completion=round(min(completion, 1.0), 2),
            overall=round(overall, 2)
        )
    
    def _generate_summary(self, participation: ParticipationScore,
                         initiative: InitiativeScore,
                         persistence: PersistenceScore) -> str:
        """生成评价总结"""
        parts = []
        
        # 整体评价
        overall = (
            participation.overall * 0.30 +
            initiative.overall * 0.25 +
            persistence.overall * 0.25
        )
        
        if overall >= 0.8:
            parts.append("学习表现优秀")
        elif overall >= 0.6:
            parts.append("学习表现良好")
        else:
            parts.append("学习表现有待提升")
        
        # 强项
        strengths = []
        if participation.overall >= 0.7:
            strengths.append("学习参与度")
        if initiative.overall >= 0.7:
            strengths.append("学习主动性")
        if persistence.overall >= 0.7:
            strengths.append("学习坚持性")
        
        if strengths:
            parts.append(f"在{', '.join(strengths)}方面表现突出")
        
        # 弱项
        weaknesses = []
        if participation.overall < 0.5:
            weaknesses.append("学习参与度")
        if initiative.overall < 0.5:
            weaknesses.append("学习主动性")
        if persistence.overall < 0.5:
            weaknesses.append("学习坚持性")
        
        if weaknesses:
            parts.append(f"建议提升{', '.join(weaknesses)}")
        
        return "。".join(parts) + "。"
    
    def _generate_recommendations(self, participation: ParticipationScore,
                                  initiative: InitiativeScore,
                                  persistence: PersistenceScore) -> List[Dict]:
        """生成改进建议"""
        recommendations = []
        
        if participation.time < 0.5:
            recommendations.append({
                'type': 'time_management',
                'priority': 'high',
                'title': '增加学习时长',
                'description': '建议每天安排固定的学习时间，至少30分钟',
                'action': '制定学习计划，设置学习提醒'
            })
        
        if initiative.questioning < 0.5:
            recommendations.append({
                'type': 'questioning',
                'priority': 'medium',
                'title': '增强主动提问',
                'description': '遇到不理解的问题要及时提问',
                'action': '每周至少提出2个问题'
            })
        
        if persistence.continuity < 0.5:
            recommendations.append({
                'type': 'consistency',
                'priority': 'high',
                'title': '保持连续学习',
                'description': '建议每天都进行学习，形成习惯',
                'action': '设置每日学习目标，坚持打卡'
            })
        
        return recommendations


class GrowthEvaluationSystem:
    """
    增值评价系统
    
    评估学习者的成长和进步
    """
    
    def __init__(self):
        self.evaluation_history = {}
    
    def evaluate_growth(self, learner_id: str,
                       baseline_result: Dict,
                       current_result: Dict) -> Dict:
        """
        评估增值
        
        Args:
            learner_id: 学习者ID
            baseline_result: 基线评价结果
            current_result: 当前评价结果
        """
        growth = {}
        
        # 计算各维度增值
        dimensions = ['knowledge_mastery', 'skill_proficiency', 
                     'problem_solving', 'creative_thinking']
        
        for dim in dimensions:
            baseline = baseline_result.get(dim, 0)
            current = current_result.get(dim, 0)
            
            absolute_gain = current - baseline
            relative_gain = (absolute_gain / baseline * 100) if baseline > 0 else 0
            
            growth[dim] = {
                'baseline': baseline,
                'current': current,
                'absolute_gain': round(absolute_gain, 3),
                'relative_gain': f"{relative_gain:.1f}%",
                'growth_level': self._classify_growth(absolute_gain)
            }
        
        # 综合增值
        overall_baseline = baseline_result.get('cei', 0)
        overall_current = current_result.get('cei', 0)
        
        return {
            'learner_id': learner_id,
            'growth_by_dimension': growth,
            'overall_growth': {
                'baseline': overall_baseline,
                'current': overall_current,
                'gain': round(overall_current - overall_baseline, 3)
            },
            'evaluation_date': datetime.now().isoformat()
        }
    
    def _classify_growth(self, gain: float) -> str:
        """对增值进行分类"""
        if gain < -0.1:
            return "退步"
        elif gain < 0.05:
            return "停滞"
        elif gain < 0.15:
            return "缓慢增长"
        elif gain < 0.3:
            return "稳健增长"
        else:
            return "快速增长"


class FeedbackSystem:
    """
    反馈系统
    
    基于评价结果生成个性化反馈
    """
    
    def __init__(self):
        self.templates = self._load_templates()
    
    def generate_feedback(self, evaluation_result: EvaluationResult) -> Dict:
        """生成反馈"""
        feedback_parts = []
        
        # 开场白
        feedback_parts.append(self._generate_opening(evaluation_result))
        
        # 评价详情
        if evaluation_result.participation:
            feedback_parts.append(
                self._generate_dimension_feedback('参与度', 
                    evaluation_result.participation.overall)
            )
        
        if evaluation_result.initiative:
            feedback_parts.append(
                self._generate_dimension_feedback('主动性',
                    evaluation_result.initiative.overall)
            )
        
        # 建议
        if evaluation_result.recommendations:
            feedback_parts.append("改进建议：")
            for rec in evaluation_result.recommendations[:3]:
                feedback_parts.append(f"  - {rec['title']}: {rec['description']}")
        
        return {
            'summary': evaluation_result.summary,
            'detailed_feedback': '\n'.join(feedback_parts),
            'recommendations': evaluation_result.recommendations
        }
    
    def _generate_opening(self, result: EvaluationResult) -> str:
        """生成开场白"""
        score = result.overall_score
        if score >= 0.8:
            return f"恭喜！您的学习表现优秀（{score:.0%}）！"
        elif score >= 0.6:
            return f"您的学习表现良好（{score:.0%}），继续保持！"
        else:
            return f"您的学习表现还有提升空间（{score:.0%}），一起努力！"
    
    def _generate_dimension_feedback(self, dimension: str, score: float) -> str:
        """生成维度反馈"""
        if score >= 0.8:
            return f"{dimension}方面表现优秀（{score:.0%}）"
        elif score >= 0.6:
            return f"{dimension}方面表现良好（{score:.0%}）"
        else:
            return f"{dimension}方面需要加强（{score:.0%}）"
    
    def _load_templates(self) -> Dict:
        """加载模板"""
        return {
            'excellent': ['表现非常出色！', '继续保持！'],
            'good': ['表现不错，还有进步空间', '再接再厉！'],
            'improve': ['需要更多努力', '加油！']
        }


def demo():
    """评估系统演示"""
    print("=" * 60)
    print("FormalMath 评估系统演示")
    print("=" * 60)
    
    # 1. 过程性评价
    print("\n--- 过程性评价 ---")
    
    process_system = ProcessEvaluationSystem()
    
    # 模拟行为数据 (表现较好的学生)
    behavior_data = BehaviorData(
        session_duration=18000,  # 5小时
        days_count=6,
        weekly_frequency=6,
        contents_viewed=15,
        total_contents=20,
        videos_completed=4,
        total_videos=5,
        exercises_completed=25,
        total_exercises=30,
        discussions_joined=2,
        questions_asked=3,
        notes_created=4,
        searches=5,
        errors_made=5,
        error_reviews=5,
        consecutive_days=5,
        max_consecutive_days=6
    )
    
    result = process_system.evaluate(
        learner_id='student_001',
        start_date=datetime(2026, 3, 25),
        end_date=datetime(2026, 3, 31),
        behavior_data=behavior_data
    )
    
    print(f"学习者: {result.learner_id}")
    print(f"评价周期: {result.period}")
    print(f"综合得分: {result.overall_score:.2%}")
    print(f"参与度: {result.participation.overall:.2%}")
    print(f"主动性: {result.initiative.overall:.2%}")
    print(f"坚持性: {result.persistence.overall:.2%}")
    print(f"\n评价总结: {result.summary}")
    
    # 2. 增值评价
    print("\n--- 增值评价 ---")
    
    growth_system = GrowthEvaluationSystem()
    
    baseline = {
        'knowledge_mastery': 0.65,
        'skill_proficiency': 0.60,
        'problem_solving': 0.58,
        'creative_thinking': 0.55,
        'cei': 60
    }
    
    current = {
        'knowledge_mastery': 0.78,
        'skill_proficiency': 0.72,
        'problem_solving': 0.70,
        'creative_thinking': 0.65,
        'cei': 72
    }
    
    growth_result = growth_system.evaluate_growth(
        'student_001', baseline, current
    )
    
    print(f"学习者: {growth_result['learner_id']}")
    print(f"综合增值: {growth_result['overall_growth']['gain']:.3f}")
    print("\n各维度增值:")
    for dim, data in growth_result['growth_by_dimension'].items():
        print(f"  {dim}: {data['absolute_gain']:+.3f} ({data['growth_level']})")
    
    # 3. 反馈生成
    print("\n--- 反馈生成 ---")
    
    feedback_system = FeedbackSystem()
    feedback = feedback_system.generate_feedback(result)
    
    print(f"反馈摘要: {feedback['summary']}")
    print(f"\n详细反馈:\n{feedback['detailed_feedback']}")
    
    print("\n" + "=" * 60)


if __name__ == '__main__':
    demo()
