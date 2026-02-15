# -*- coding: utf-8 -*-
"""
assessment_system.py - FormalMath 评估系统核心模块

本模块是评估系统的核心，整合所有评估功能，提供统一的评估接口：
- 形成性评价
- 总结性评价
- 过程性评价
- 增值评价
- 表现性评价
- 发散思维评价

与认知诊断系统对接接口
"""

import uuid
from typing import Dict, List, Optional, Any, Union, Callable
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from enum import Enum

from evaluation_criteria import (
    LearnerProfile, MathematicalAbilityProfile, EvaluationCriteria, EvaluationLevel,
    AssessmentType, ConceptualUnderstanding, ProceduralFluency, StrategicCompetence,
    AdaptiveReasoning, ProductiveDisposition, ValueAddedMetrics
)
from scoring_engine import (
    ScoringEngine, ScoringAlgorithm, WeightedScoringModel,
    ValueAddedScoringModel, PerformanceScoringModel,
    DivergentThinkingScoringModel, ProcessScoringModel
)
from feedback_generator import (
    FeedbackGenerator, FeedbackReport, FeedbackType, FeedbackPriority,
    RealTimeFeedbackGenerator, FeedbackItem
)
from report_generator import (
    ReportGenerator, AssessmentReport, ReportType, ReportFormat,
    ProgressReportGenerator, AbilityReportGenerator, ValueAddedReportGenerator
)


# =============================================================================
# 评估配置
# =============================================================================

@dataclass
class AssessmentConfig:
    """评估配置"""
    # 评估权重配置
    ability_weights: Dict[str, float] = field(default_factory=lambda: {
        'conceptual_understanding': 0.20,
        'procedural_fluency': 0.20,
        'strategic_competence': 0.25,
        'adaptive_reasoning': 0.25,
        'productive_disposition': 0.10
    })
    
    # 评分阈值配置
    thresholds: Dict[str, float] = field(default_factory=lambda: {
        'excellent': 80.0,
        'good': 60.0,
        'passing': 40.0
    })
    
    # 评估周期配置（天）
    evaluation_periods: Dict[str, int] = field(default_factory=lambda: {
        'formative': 7,      # 形成性评价周期
        'summative': 30,     # 总结性评价周期
        'process': 7,        # 过程性评价周期
        'value_added': 30    # 增值评价周期
    })
    
    # 反馈配置
    feedback_config: Dict[str, Any] = field(default_factory=lambda: {
        'generate_real_time': True,
        'generate_summary': True,
        'suggestion_count': 5
    })


# =============================================================================
# 评估会话
# =============================================================================

@dataclass
class AssessmentSession:
    """评估会话"""
    session_id: str
    learner_id: str
    assessment_type: AssessmentType
    start_time: datetime
    end_time: Optional[datetime] = None
    data: Dict[str, Any] = field(default_factory=dict)
    results: Dict[str, Any] = field(default_factory=dict)
    status: str = "active"  # active, completed, cancelled
    
    def complete(self, results: Dict[str, Any]):
        """完成评估会话"""
        self.end_time = datetime.now()
        self.results = results
        self.status = "completed"
    
    def to_dict(self) -> Dict[str, Any]:
        """转换为字典"""
        return {
            'session_id': self.session_id,
            'learner_id': self.learner_id,
            'assessment_type': self.assessment_type.name,
            'start_time': self.start_time.isoformat(),
            'end_time': self.end_time.isoformat() if self.end_time else None,
            'data': self.data,
            'results': self.results,
            'status': self.status
        }


# =============================================================================
# 评估结果
# =============================================================================

@dataclass
class AssessmentResult:
    """评估结果"""
    result_id: str
    learner_id: str
    assessment_type: AssessmentType
    scores: Dict[str, float] = field(default_factory=dict)
    overall_score: float = 0.0
    level: EvaluationLevel = EvaluationLevel.BEGINNER
    feedback: Optional[FeedbackReport] = None
    report: Optional[AssessmentReport] = None
    timestamp: datetime = field(default_factory=datetime.now)
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def to_dict(self) -> Dict[str, Any]:
        """转换为字典"""
        return {
            'result_id': self.result_id,
            'learner_id': self.learner_id,
            'assessment_type': self.assessment_type.name,
            'scores': self.scores,
            'overall_score': self.overall_score,
            'level': self.level.name,
            'timestamp': self.timestamp.isoformat(),
            'metadata': self.metadata
        }


# =============================================================================
# 核心评估系统
# =============================================================================

class FormalMathAssessmentSystem:
    """
    FormalMath 评估系统核心类
    
    整合所有评估功能，提供统一的评估接口
    
    Attributes:
        config: 评估配置
        scoring_engine: 评分引擎
        feedback_generator: 反馈生成器
        report_generator: 报告生成器
        sessions: 活跃评估会话
    """
    
    def __init__(self, config: Optional[AssessmentConfig] = None):
        """
        初始化评估系统
        
        Args:
            config: 评估配置，如果为None则使用默认配置
        """
        self.config = config or AssessmentConfig()
        self.scoring_engine = ScoringEngine()
        self.feedback_generator = FeedbackGenerator()
        self.realtime_feedback_generator = RealTimeFeedbackGenerator()
        self.report_generator = ReportGenerator()
        
        # 存储学习者档案和评估会话
        self._learner_profiles: Dict[str, LearnerProfile] = {}
        self._sessions: Dict[str, AssessmentSession] = {}
        self._results: Dict[str, AssessmentResult] = {}
        
        # 认知诊断系统对接回调
        self._diagnosis_callbacks: List[Callable] = []
    
    # =========================================================================
    # 学习者管理
    # =========================================================================
    
    def register_learner(self, learner_id: str, name: str = "") -> LearnerProfile:
        """
        注册学习者
        
        Args:
            learner_id: 学习者ID
            name: 学习者姓名
        
        Returns:
            学习者档案
        """
        profile = LearnerProfile(
            learner_id=learner_id,
            name=name or learner_id
        )
        self._learner_profiles[learner_id] = profile
        return profile
    
    def get_learner_profile(self, learner_id: str) -> Optional[LearnerProfile]:
        """
        获取学习者档案
        
        Args:
            learner_id: 学习者ID
        
        Returns:
            学习者档案，如果不存在则返回None
        """
        return self._learner_profiles.get(learner_id)
    
    def update_learner_ability(
        self, 
        learner_id: str, 
        ability_profile: MathematicalAbilityProfile
    ) -> bool:
        """
        更新学习者能力档案
        
        Args:
            learner_id: 学习者ID
            ability_profile: 能力档案
        
        Returns:
            是否更新成功
        """
        profile = self._learner_profiles.get(learner_id)
        if profile:
            profile.current_ability = ability_profile
            return True
        return False
    
    def update_learner_knowledge(
        self, 
        learner_id: str, 
        concept: str, 
        mastery: float
    ) -> bool:
        """
        更新学习者知识状态
        
        Args:
            learner_id: 学习者ID
            concept: 概念名称
            mastery: 掌握度 (0-100)
        
        Returns:
            是否更新成功
        """
        profile = self._learner_profiles.get(learner_id)
        if profile:
            profile.knowledge_state[concept] = max(0, min(100, mastery))
            return True
        return False
    
    def record_learning_activity(
        self, 
        learner_id: str, 
        activity_data: Dict[str, Any]
    ) -> bool:
        """
        记录学习活动
        
        Args:
            learner_id: 学习者ID
            activity_data: 活动数据
        
        Returns:
            是否记录成功
        """
        profile = self._learner_profiles.get(learner_id)
        if profile:
            activity_data['timestamp'] = datetime.now().isoformat()
            profile.learning_history.append(activity_data)
            return True
        return False
    
    # =========================================================================
    # 评估会话管理
    # =========================================================================
    
    def start_assessment(
        self, 
        learner_id: str, 
        assessment_type: AssessmentType,
        data: Optional[Dict[str, Any]] = None
    ) -> AssessmentSession:
        """
        开始评估会话
        
        Args:
            learner_id: 学习者ID
            assessment_type: 评估类型
            data: 附加数据
        
        Returns:
            评估会话
        """
        session = AssessmentSession(
            session_id=str(uuid.uuid4()),
            learner_id=learner_id,
            assessment_type=assessment_type,
            start_time=datetime.now(),
            data=data or {}
        )
        self._sessions[session.session_id] = session
        return session
    
    def end_assessment(
        self, 
        session_id: str, 
        results: Dict[str, Any]
    ) -> Optional[AssessmentSession]:
        """
        结束评估会话
        
        Args:
            session_id: 会话ID
            results: 评估结果
        
        Returns:
            评估会话，如果不存在则返回None
        """
        session = self._sessions.get(session_id)
        if session:
            session.complete(results)
        return session
    
    def get_session(self, session_id: str) -> Optional[AssessmentSession]:
        """获取评估会话"""
        return self._sessions.get(session_id)
    
    # =========================================================================
    # 核心评估方法
    # =========================================================================
    
    def conduct_formative_assessment(
        self, 
        learner_id: str,
        assessment_data: Optional[Dict[str, Any]] = None
    ) -> AssessmentResult:
        """
        进行形成性评价
        
        形成性评价关注学习过程，提供及时反馈以促进学习改进。
        
        Args:
            learner_id: 学习者ID
            assessment_data: 评估数据
        
        Returns:
            评估结果
        """
        profile = self._learner_profiles.get(learner_id)
        if not profile:
            raise ValueError(f"学习者 {learner_id} 未注册")
        
        # 开始评估会话
        session = self.start_assessment(learner_id, AssessmentType.FORMATIVE, assessment_data)
        
        # 进行能力评估
        ability_result = self.scoring_engine.evaluate_mathematical_ability(
            profile.current_ability
        )
        
        # 生成反馈
        feedback = self.feedback_generator.generate_feedback(
            profile, ability_result, FeedbackType.SUMMARY
        )
        
        # 创建评估结果
        result = AssessmentResult(
            result_id=str(uuid.uuid4()),
            learner_id=learner_id,
            assessment_type=AssessmentType.FORMATIVE,
            scores=ability_result['dimension_scores'],
            overall_score=ability_result['overall_score'],
            level=ability_result['level'],
            feedback=feedback
        )
        
        # 结束评估会话
        session.complete(result.to_dict())
        self._results[result.result_id] = result
        
        return result
    
    def conduct_summative_assessment(
        self, 
        learner_id: str,
        assessment_data: Optional[Dict[str, Any]] = None
    ) -> AssessmentResult:
        """
        进行总结性评价
        
        总结性评价评估学习者在某一阶段的学习成果。
        
        Args:
            learner_id: 学习者ID
            assessment_data: 评估数据
        
        Returns:
            评估结果
        """
        profile = self._learner_profiles.get(learner_id)
        if not profile:
            raise ValueError(f"学习者 {learner_id} 未注册")
        
        # 开始评估会话
        session = self.start_assessment(learner_id, AssessmentType.SUMMATIVE, assessment_data)
        
        # 进行综合评估
        ability_result = self.scoring_engine.evaluate_mathematical_ability(
            profile.current_ability
        )
        
        # 生成详细报告
        report = self.report_generator.generate_report(
            ReportType.ABILITY,
            profile,
            detailed=True
        )
        
        # 生成反馈
        feedback = self.feedback_generator.generate_feedback(
            profile, ability_result, FeedbackType.SUMMARY
        )
        
        # 创建评估结果
        result = AssessmentResult(
            result_id=str(uuid.uuid4()),
            learner_id=learner_id,
            assessment_type=AssessmentType.SUMMATIVE,
            scores=ability_result['dimension_scores'],
            overall_score=ability_result['overall_score'],
            level=ability_result['level'],
            feedback=feedback,
            report=report
        )
        
        # 结束评估会话
        session.complete(result.to_dict())
        self._results[result.result_id] = result
        
        return result
    
    def conduct_process_assessment(
        self, 
        learner_id: str,
        learning_history: Optional[List[Dict[str, Any]]] = None,
        learning_path: Optional[Dict[str, Any]] = None,
        period_days: int = 7
    ) -> AssessmentResult:
        """
        进行过程性评价
        
        过程性评价关注学习过程，评估学习参与度和进展。
        
        Args:
            learner_id: 学习者ID
            learning_history: 学习历史，如果为None则使用档案中的历史
            learning_path: 学习路径
            period_days: 评估周期（天）
        
        Returns:
            评估结果
        """
        profile = self._learner_profiles.get(learner_id)
        if not profile:
            raise ValueError(f"学习者 {learner_id} 未注册")
        
        # 使用档案中的学习历史
        history = learning_history or profile.learning_history
        path = learning_path or {}
        
        # 开始评估会话
        session = self.start_assessment(
            learner_id, 
            AssessmentType.PROCESS,
            {'period_days': period_days}
        )
        
        # 进行过程性评估
        process_scores = self.scoring_engine.evaluate_process(
            profile, history, path, period_days
        )
        
        # 计算综合过程得分
        overall_process_score = (
            process_scores['participation']['score'] * 0.4 +
            process_scores['initiative']['score'] * 0.3 +
            process_scores['progress']['score'] * 0.3
        )
        
        # 生成反馈
        feedback = self.feedback_generator.generate_process_feedback(
            learner_id, process_scores
        )
        
        # 生成报告
        report = self.report_generator.generate_report(
            ReportType.PROGRESS,
            profile,
            learning_path=path,
            period_days=period_days
        )
        
        # 创建评估结果
        result = AssessmentResult(
            result_id=str(uuid.uuid4()),
            learner_id=learner_id,
            assessment_type=AssessmentType.PROCESS,
            scores={
                'participation': process_scores['participation']['score'],
                'initiative': process_scores['initiative']['score'],
                'progress': process_scores['progress']['score']
            },
            overall_score=overall_process_score,
            level=EvaluationCriteria.get_level(overall_process_score),
            feedback=feedback,
            report=report
        )
        
        # 结束评估会话
        session.complete(result.to_dict())
        self._results[result.result_id] = result
        
        return result
    
    def conduct_value_added_assessment(
        self, 
        learner_id: str,
        period_days: int = 30
    ) -> AssessmentResult:
        """
        进行增值评价
        
        增值评价评估学习者在一定时期内的能力提升。
        
        Args:
            learner_id: 学习者ID
            period_days: 评估周期（天）
        
        Returns:
            评估结果
        """
        profile = self._learner_profiles.get(learner_id)
        if not profile:
            raise ValueError(f"学习者 {learner_id} 未注册")
        
        # 开始评估会话
        session = self.start_assessment(
            learner_id,
            AssessmentType.VALUE_ADDED,
            {'period_days': period_days}
        )
        
        # 进行增值评估
        value_added = self.scoring_engine.evaluate_value_added(profile, period_days)
        
        # 生成反馈
        feedback = self.feedback_generator.generate_value_added_feedback(
            learner_id, value_added
        )
        
        # 生成报告
        report = self.report_generator.generate_report(
            ReportType.VALUE_ADDED,
            profile,
            period_days=period_days
        )
        
        # 创建评估结果
        overall_value_added = value_added.get('overall_value_added', 0)
        result = AssessmentResult(
            result_id=str(uuid.uuid4()),
            learner_id=learner_id,
            assessment_type=AssessmentType.VALUE_ADDED,
            scores=value_added.get('ability_value_added', {}),
            overall_score=overall_value_added,
            level=EvaluationCriteria.get_level(max(0, overall_value_added + 50)),
            feedback=feedback,
            report=report,
            metadata={
                'new_concepts': value_added.get('new_concepts_count', 0),
                'mastery_improvement': value_added.get('mastery_improvement', 0)
            }
        )
        
        # 结束评估会话
        session.complete(result.to_dict())
        self._results[result.result_id] = result
        
        return result
    
    def conduct_performance_assessment(
        self, 
        learner_id: str,
        performance_data: Dict[str, Any]
    ) -> AssessmentResult:
        """
        进行表现性评价
        
        表现性评价评估学习者在真实任务情境中的表现。
        
        Args:
            learner_id: 学习者ID
            performance_data: 表现数据
        
        Returns:
            评估结果
        """
        profile = self._learner_profiles.get(learner_id)
        if not profile:
            raise ValueError(f"学习者 {learner_id} 未注册")
        
        # 开始评估会话
        session = self.start_assessment(
            learner_id,
            AssessmentType.PERFORMANCE,
            performance_data
        )
        
        # 使用表现性评分模型进行评估
        performance_model = PerformanceScoringModel()
        
        # 评估操作能力
        operational = performance_model.assess_operational_ability(
            performance_data.get('problem_analysis', {}),
            performance_data.get('method_selection', {}),
            performance_data.get('execution', {}),
            performance_data.get('verification', {})
        )
        
        # 评估创造产品（如果有）
        product_score = 0
        if 'creative_product' in performance_data:
            product = performance_model.assess_creative_product(
                performance_data['creative_product'],
                performance_data.get('requirements', {})
            )
            product_score = product.calculate_score()
        
        # 计算综合表现得分
        overall_score = operational.calculate_score() * 0.7 + product_score * 0.3
        
        # 创建评估结果
        result = AssessmentResult(
            result_id=str(uuid.uuid4()),
            learner_id=learner_id,
            assessment_type=AssessmentType.PERFORMANCE,
            scores={
                'problem_analysis': operational.problem_analysis,
                'method_selection': operational.method_selection,
                'execution': operational.execution,
                'verification': operational.verification,
                'product': product_score
            },
            overall_score=overall_score,
            level=EvaluationCriteria.get_level(overall_score)
        )
        
        # 结束评估会话
        session.complete(result.to_dict())
        self._results[result.result_id] = result
        
        return result
    
    def conduct_divergent_assessment(
        self, 
        learner_id: str,
        creative_output: Dict[str, Any]
    ) -> AssessmentResult:
        """
        进行发散思维评价
        
        发散思维评价评估学习者的创造性思维能力。
        
        Args:
            learner_id: 学习者ID
            creative_output: 创造性产出数据
        
        Returns:
            评估结果
        """
        profile = self._learner_profiles.get(learner_id)
        if not profile:
            raise ValueError(f"学习者 {learner_id} 未注册")
        
        # 开始评估会话
        session = self.start_assessment(
            learner_id,
            AssessmentType.DIVERGENT,
            creative_output
        )
        
        # 使用发散思维评分模型
        divergent_model = DivergentThinkingScoringModel()
        creativity = divergent_model.assess_creativity(creative_output)
        
        # 计算创造性得分
        creativity_score = creativity.calculate_creativity_score()
        
        # 创建评估结果
        result = AssessmentResult(
            result_id=str(uuid.uuid4()),
            learner_id=learner_id,
            assessment_type=AssessmentType.DIVERGENT,
            scores={
                'fluency': creativity.fluency,
                'flexibility': creativity.flexibility,
                'originality': creativity.originality,
                'elaboration': creativity.elaboration
            },
            overall_score=creativity_score,
            level=EvaluationCriteria.get_level(creativity_score)
        )
        
        # 结束评估会话
        session.complete(result.to_dict())
        self._results[result.result_id] = result
        
        return result
    
    # =========================================================================
    # 实时反馈
    # =========================================================================
    
    def generate_real_time_feedback(
        self, 
        learner_id: str,
        interaction_data: Dict[str, Any]
    ) -> Optional[FeedbackItem]:
        """
        生成实时反馈
        
        Args:
            learner_id: 学习者ID
            interaction_data: 交互数据
        
        Returns:
            反馈项，如果不满足反馈条件则返回None
        """
        return self.realtime_feedback_generator.generate_real_time_feedback(
            interaction_data
        )
    
    def generate_answer_feedback(
        self,
        learner_id: str,
        is_correct: bool,
        attempt_count: int,
        time_spent: float
    ) -> FeedbackItem:
        """
        生成答题反馈
        
        Args:
            learner_id: 学习者ID
            is_correct: 是否正确
            attempt_count: 尝试次数
            time_spent: 花费时间（秒）
        
        Returns:
            反馈项
        """
        return self.realtime_feedback_generator.generate_answer_feedback(
            is_correct, attempt_count, time_spent
        )
    
    # =========================================================================
    # 报告生成与导出
    # =========================================================================
    
    def generate_report(
        self,
        report_type: ReportType,
        learner_id: str,
        **kwargs
    ) -> AssessmentReport:
        """
        生成评估报告
        
        Args:
            report_type: 报告类型
            learner_id: 学习者ID
            **kwargs: 额外参数
        
        Returns:
            评估报告
        """
        profile = self._learner_profiles.get(learner_id)
        if not profile:
            raise ValueError(f"学习者 {learner_id} 未注册")
        
        return self.report_generator.generate_report(
            report_type, profile, **kwargs
        )
    
    def export_report(
        self,
        report: AssessmentReport,
        format: ReportFormat,
        filepath: str
    ) -> str:
        """
        导出报告
        
        Args:
            report: 评估报告
            format: 导出格式
            filepath: 文件路径
        
        Returns:
            导出的文件路径
        """
        return self.report_generator.export_report(report, format, filepath)
    
    # =========================================================================
    # 认知诊断系统对接接口
    # =========================================================================
    
    def register_diagnosis_callback(self, callback: Callable):
        """
        注册认知诊断回调函数
        
        Args:
            callback: 回调函数，接收诊断数据作为参数
        """
        self._diagnosis_callbacks.append(callback)
    
    def notify_diagnosis_system(self, diagnosis_data: Dict[str, Any]):
        """
        通知认知诊断系统
        
        Args:
            diagnosis_data: 诊断数据
        """
        for callback in self._diagnosis_callbacks:
            try:
                callback(diagnosis_data)
            except Exception as e:
                print(f"诊断回调执行失败: {e}")
    
    def get_learner_diagnosis_profile(self, learner_id: str) -> Dict[str, Any]:
        """
        获取学习者诊断档案
        
        为认知诊断系统提供学习者的评估数据
        
        Args:
            learner_id: 学习者ID
        
        Returns:
            诊断档案数据
        """
        profile = self._learner_profiles.get(learner_id)
        if not profile:
            return {}
        
        return {
            'learner_id': learner_id,
            'ability_profile': profile.current_ability.get_dimension_scores(),
            'knowledge_state': profile.knowledge_state,
            'learning_history_summary': {
                'total_sessions': len(profile.learning_history),
                'recent_activities': profile.learning_history[-10:] if profile.learning_history else []
            }
        }
    
    # =========================================================================
    # 系统信息
    # =========================================================================
    
    def get_system_info(self) -> Dict[str, Any]:
        """获取系统信息"""
        return {
            'name': 'FormalMath Assessment System',
            'version': '1.0.0',
            'supported_assessment_types': [t.name for t in AssessmentType],
            'registered_learners': len(self._learner_profiles),
            'active_sessions': len([s for s in self._sessions.values() if s.status == 'active']),
            'total_assessments': len(self._results)
        }
    
    def get_learner_results(
        self, 
        learner_id: str,
        assessment_type: Optional[AssessmentType] = None
    ) -> List[AssessmentResult]:
        """
        获取学习者的评估结果
        
        Args:
            learner_id: 学习者ID
            assessment_type: 评估类型过滤
        
        Returns:
            评估结果列表
        """
        results = [
            r for r in self._results.values() 
            if r.learner_id == learner_id
        ]
        
        if assessment_type:
            results = [r for r in results if r.assessment_type == assessment_type]
        
        return sorted(results, key=lambda r: r.timestamp, reverse=True)


# 导出所有类和函数
__all__ = [
    'AssessmentConfig',
    'AssessmentSession',
    'AssessmentResult',
    'FormalMathAssessmentSystem'
]
