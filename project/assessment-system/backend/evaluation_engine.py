# -*- coding: utf-8 -*-
"""
evaluation_engine.py - FormalMath 评估系统核心引擎

实现评估系统的核心功能：
- 多维度评价计算
- 增值评价计算
- 学习轨迹追踪
- 错误模式识别
"""

import uuid
import math
from typing import Dict, List, Optional, Any, Tuple
from datetime import datetime, timedelta
from dataclasses import dataclass, field
from collections import defaultdict
import numpy as np
from scipy import stats


# =============================================================================
# 数据类定义
# =============================================================================

@dataclass
class DimensionScore:
    """维度得分"""
    dimension: str
    score: float
    weight: float = 1.0
    sub_scores: Dict[str, float] = field(default_factory=dict)
    
    def calculate_weighted(self) -> float:
        """计算加权得分"""
        return self.score * self.weight


@dataclass
class EvaluationResult:
    """评价结果"""
    result_id: str
    learner_id: str
    assessment_type: str
    overall_score: float
    level: str
    dimension_scores: Dict[str, DimensionScore]
    timestamp: datetime = field(default_factory=datetime.now)
    details: Dict[str, Any] = field(default_factory=dict)
    
    def to_dict(self) -> dict:
        return {
            "result_id": self.result_id,
            "learner_id": self.learner_id,
            "assessment_type": self.assessment_type,
            "overall_score": round(self.overall_score, 2),
            "level": self.level,
            "dimension_scores": {
                k: {
                    "score": round(v.score, 2),
                    "weight": v.weight,
                    "sub_scores": v.sub_scores
                }
                for k, v in self.dimension_scores.items()
            },
            "timestamp": self.timestamp.isoformat(),
            "details": self.details
        }


@dataclass
class ValueAddedResult:
    """增值评价结果"""
    learner_id: str
    period_start: datetime
    period_end: datetime
    absolute_gains: Dict[str, float]
    relative_gains: Dict[str, float]
    growth_percentile: float  # SGP
    overall_growth: str  # 增长等级
    
    def to_dict(self) -> dict:
        return {
            "learner_id": self.learner_id,
            "period": {
                "start": self.period_start.isoformat(),
                "end": self.period_end.isoformat()
            },
            "absolute_gains": {k: round(v, 2) for k, v in self.absolute_gains.items()},
            "relative_gains": {k: round(v, 2) for k, v in self.relative_gains.items()},
            "growth_percentile": round(self.growth_percentile, 1),
            "overall_growth": self.overall_growth
        }


@dataclass
class LearningTrajectoryPoint:
    """学习轨迹点"""
    date: datetime
    score: float
    context: str = ""


# =============================================================================
# 评价等级判定
# =============================================================================

class EvaluationLevelUtil:
    """评价等级工具类"""
    
    LEVEL_THRESHOLDS = {
        "expert": (90, 100),
        "advanced": (80, 90),
        "proficient": (60, 80),
        "developing": (40, 60),
        "beginner": (0, 40)
    }
    
    LEVEL_DESCRIPTIONS = {
        "expert": "专家水平 - 能够创造新知和指导他人",
        "advanced": "高级水平 - 能够灵活应用和迁移知识",
        "proficient": "熟练水平 - 能够独立应用知识和技能",
        "developing": "发展中 - 正在发展理解和应用能力",
        "beginner": "初级水平 - 正在建立基础概念和技能"
    }
    
    @classmethod
    def get_level(cls, score: float) -> str:
        """根据分数获取等级"""
        for level, (low, high) in cls.LEVEL_THRESHOLDS.items():
            if low <= score <= high:
                return level
        return "beginner"
    
    @classmethod
    def get_description(cls, level: str) -> str:
        """获取等级描述"""
        return cls.LEVEL_DESCRIPTIONS.get(level, "未知等级")


# =============================================================================
# 核心评估引擎
# =============================================================================

class AssessmentEngine:
    """评估引擎"""
    
    # 四维评价权重配置
    DIMENSION_WEIGHTS = {
        "knowledge_mastery": 0.30,
        "skill_proficiency": 0.25,
        "problem_solving": 0.25,
        "creative_thinking": 0.20
    }
    
    # 五维数学能力权重（MAA标准）
    MAA_DIMENSION_WEIGHTS = {
        "conceptual_understanding": 0.20,
        "procedural_fluency": 0.20,
        "strategic_competence": 0.25,
        "adaptive_reasoning": 0.25,
        "productive_disposition": 0.10
    }
    
    def __init__(self):
        self.scoring_algorithms = ScoringAlgorithms()
    
    def evaluate_comprehensive(
        self,
        learner_id: str,
        knowledge_scores: Dict[str, float],
        skill_scores: Dict[str, float],
        problem_solving_scores: Dict[str, float],
        creative_scores: Dict[str, float]
    ) -> EvaluationResult:
        """
        综合评价 - 四维评价模型
        
        Args:
            learner_id: 学习者ID
            knowledge_scores: 知识掌握度得分详情
            skill_scores: 技能熟练度得分详情
            problem_solving_scores: 问题解决能力得分详情
            creative_scores: 创新思维能力得分详情
        
        Returns:
            评价结果
        """
        # 计算各维度得分
        knowledge = self._calculate_knowledge_score(knowledge_scores)
        skill = self._calculate_skill_score(skill_scores)
        problem = self._calculate_problem_solving_score(problem_solving_scores)
        creative = self._calculate_creative_score(creative_scores)
        
        dimension_scores = {
            "knowledge_mastery": DimensionScore(
                dimension="知识掌握度",
                score=knowledge,
                weight=self.DIMENSION_WEIGHTS["knowledge_mastery"],
                sub_scores=knowledge_scores
            ),
            "skill_proficiency": DimensionScore(
                dimension="技能熟练度",
                score=skill,
                weight=self.DIMENSION_WEIGHTS["skill_proficiency"],
                sub_scores=skill_scores
            ),
            "problem_solving": DimensionScore(
                dimension="问题解决能力",
                score=problem,
                weight=self.DIMENSION_WEIGHTS["problem_solving"],
                sub_scores=problem_solving_scores
            ),
            "creative_thinking": DimensionScore(
                dimension="创新思维能力",
                score=creative,
                weight=self.DIMENSION_WEIGHTS["creative_thinking"],
                sub_scores=creative_scores
            )
        }
        
        # 计算总分
        overall = sum(ds.calculate_weighted() for ds in dimension_scores.values())
        level = EvaluationLevelUtil.get_level(overall)
        
        return EvaluationResult(
            result_id=str(uuid.uuid4()),
            learner_id=learner_id,
            assessment_type="comprehensive",
            overall_score=overall,
            level=level,
            dimension_scores=dimension_scores,
            details={
                "evaluation_model": "four_dimension",
                "strengths": self._identify_strengths(dimension_scores),
                "weaknesses": self._identify_weaknesses(dimension_scores)
            }
        )
    
    def evaluate_mathematical_ability(
        self,
        learner_id: str,
        ability_data: Dict[str, Dict[str, float]]
    ) -> EvaluationResult:
        """
        五维数学能力评价（MAA标准）
        
        Args:
            learner_id: 学习者ID
            ability_data: 五维能力数据
                {
                    "conceptual_understanding": {...},
                    "procedural_fluency": {...},
                    ...
                }
        
        Returns:
            评价结果
        """
        dimension_scores = {}
        
        for dim_key, weight in self.MAA_DIMENSION_WEIGHTS.items():
            dim_data = ability_data.get(dim_key, {})
            score = self._calculate_dimension_average(dim_data)
            
            dimension_scores[dim_key] = DimensionScore(
                dimension=self._translate_dimension_name(dim_key),
                score=score,
                weight=weight,
                sub_scores=dim_data
            )
        
        overall = sum(ds.calculate_weighted() for ds in dimension_scores.values())
        level = EvaluationLevelUtil.get_level(overall)
        
        return EvaluationResult(
            result_id=str(uuid.uuid4()),
            learner_id=learner_id,
            assessment_type="mathematical_ability",
            overall_score=overall,
            level=level,
            dimension_scores=dimension_scores
        )
    
    def _calculate_knowledge_score(self, scores: Dict[str, float]) -> float:
        """计算知识掌握度得分"""
        if not scores:
            return 0.0
        weights = {
            "concept_understanding": 0.35,
            "theorem_mastery": 0.35,
            "method_proficiency": 0.30
        }
        return sum(scores.get(k, 0) * w for k, w in weights.items())
    
    def _calculate_skill_score(self, scores: Dict[str, float]) -> float:
        """计算技能熟练度得分"""
        if not scores:
            return 0.0
        weights = {
            "calculation": 0.40,
            "proof": 0.35,
            "modeling": 0.25
        }
        return sum(scores.get(k, 0) * w for k, w in weights.items())
    
    def _calculate_problem_solving_score(self, scores: Dict[str, float]) -> float:
        """计算问题解决能力得分"""
        if not scores:
            return 0.0
        weights = {
            "problem_analysis": 0.30,
            "strategy_selection": 0.35,
            "execution_verification": 0.35
        }
        return sum(scores.get(k, 0) * w for k, w in weights.items())
    
    def _calculate_creative_score(self, scores: Dict[str, float]) -> float:
        """计算创新思维能力得分"""
        if not scores:
            return 0.0
        weights = {
            "divergent_thinking": 0.35,
            "creativity": 0.35,
            "critical_thinking": 0.30
        }
        return sum(scores.get(k, 0) * w for k, w in weights.items())
    
    def _calculate_dimension_average(self, scores: Dict[str, float]) -> float:
        """计算维度平均分"""
        if not scores:
            return 0.0
        return sum(scores.values()) / len(scores)
    
    def _identify_strengths(
        self, 
        dimension_scores: Dict[str, DimensionScore],
        threshold: float = 70.0
    ) -> List[str]:
        """识别强项"""
        return [ds.dimension for ds in dimension_scores.values() if ds.score >= threshold]
    
    def _identify_weaknesses(
        self, 
        dimension_scores: Dict[str, DimensionScore],
        threshold: float = 60.0
    ) -> List[str]:
        """识别弱项"""
        return [ds.dimension for ds in dimension_scores.values() if ds.score < threshold]
    
    def _translate_dimension_name(self, key: str) -> str:
        """翻译维度名称"""
        translations = {
            "conceptual_understanding": "概念理解",
            "procedural_fluency": "程序流畅性",
            "strategic_competence": "策略能力",
            "adaptive_reasoning": "适应性推理",
            "productive_disposition": "数学产出"
        }
        return translations.get(key, key)


# =============================================================================
# 增值评价引擎
# =============================================================================

class ValueAddedEngine:
    """增值评价引擎"""
    
    def calculate_value_added(
        self,
        learner_id: str,
        baseline_scores: Dict[str, float],
        current_scores: Dict[str, float],
        peer_gains: Optional[List[Dict[str, float]]] = None
    ) -> ValueAddedResult:
        """
        计算增值
        
        Args:
            learner_id: 学习者ID
            baseline_scores: 期初得分
            current_scores: 期末得分
            peer_gains: 同侪增值数据（用于计算SGP）
        
        Returns:
            增值评价结果
        """
        # 计算绝对增值
        absolute_gains = {}
        for dim in set(baseline_scores.keys()) | set(current_scores.keys()):
            baseline = baseline_scores.get(dim, 0)
            current = current_scores.get(dim, 0)
            absolute_gains[dim] = current - baseline
        
        # 计算相对增值（百分比）
        relative_gains = {}
        for dim, gain in absolute_gains.items():
            baseline = baseline_scores.get(dim, 0)
            if baseline > 0:
                relative_gains[dim] = (gain / baseline) * 100
            else:
                relative_gains[dim] = gain
        
        # 计算SGP（Student Growth Percentile）
        sgp = self._calculate_sgp(absolute_gains, peer_gains)
        
        # 判定增长等级
        overall_growth = self._classify_growth(
            sum(absolute_gains.values()) / len(absolute_gains) if absolute_gains else 0
        )
        
        return ValueAddedResult(
            learner_id=learner_id,
            period_start=datetime.now() - timedelta(days=30),
            period_end=datetime.now(),
            absolute_gains=absolute_gains,
            relative_gains=relative_gains,
            growth_percentile=sgp,
            overall_growth=overall_growth
        )
    
    def _calculate_sgp(
        self, 
        gains: Dict[str, float], 
        peer_gains: Optional[List[Dict[str, float]]]
    ) -> float:
        """计算学生增长百分位（SGP）"""
        if not peer_gains:
            return 50.0  # 无同侪数据时返回中位数
        
        # 计算当前学生的平均增值
        avg_gain = sum(gains.values()) / len(gains) if gains else 0
        
        # 计算同侪的平均增值
        peer_avg_gains = []
        for peer in peer_gains:
            avg = sum(peer.values()) / len(peer) if peer else 0
            peer_avg_gains.append(avg)
        
        # 计算百分位
        if not peer_avg_gains:
            return 50.0
        
        percentile = stats.percentileofscore(peer_avg_gains, avg_gain, kind='rank')
        return float(percentile)
    
    def _classify_growth(self, gain: float) -> str:
        """对增长进行分类"""
        if gain < -5:
            return "退步"
        elif gain < 5:
            return "停滞"
        elif gain < 15:
            return "缓慢增长"
        elif gain < 30:
            return "稳健增长"
        else:
            return "快速增长"


# =============================================================================
# 过程性评价引擎
# =============================================================================

class ProcessEvaluationEngine:
    """过程性评价引擎"""
    
    def evaluate_process(
        self,
        learner_id: str,
        behavior_records: List[Dict[str, Any]],
        period_days: int = 7
    ) -> Dict[str, Any]:
        """
        过程性评价
        
        Args:
            learner_id: 学习者ID
            behavior_records: 学习行为记录
            period_days: 评价周期（天）
        
        Returns:
            过程性评价结果
        """
        # 计算参与度
        participation = self._calculate_participation(behavior_records, period_days)
        
        # 计算主动性
        initiative = self._calculate_initiative(behavior_records)
        
        # 计算持续性
        consistency = self._calculate_consistency(behavior_records, period_days)
        
        # 计算投入度
        engagement = self._calculate_engagement(behavior_records)
        
        # 综合过程得分
        overall = (
            participation * 0.35 +
            initiative * 0.25 +
            consistency * 0.20 +
            engagement * 0.20
        )
        
        return {
            "participation": round(participation, 2),
            "initiative": round(initiative, 2),
            "consistency": round(consistency, 2),
            "engagement": round(engagement, 2),
            "overall_score": round(overall, 2),
            "level": EvaluationLevelUtil.get_level(overall),
            "details": {
                "record_count": len(behavior_records),
                "period_days": period_days
            }
        }
    
    def _calculate_participation(
        self, 
        records: List[Dict], 
        period_days: int
    ) -> float:
        """计算参与度"""
        if not records:
            return 0.0
        
        # 学习时长得分（假设每天1小时为满分）
        total_duration = sum(r.get("duration", 0) for r in records)
        hours_per_day = (total_duration / 3600) / period_days
        duration_score = min(100, hours_per_day * 100)
        
        # 频率得分（假设每周5次为满分）
        unique_days = len(set(
            r.get("timestamp", datetime.now()).strftime("%Y-%m-%d") 
            if isinstance(r.get("timestamp"), datetime) 
            else str(r.get("timestamp", ""))[:10]
            for r in records
        ))
        frequency_per_week = (unique_days / period_days) * 7
        frequency_score = min(100, frequency_per_week * 20)
        
        return (duration_score + frequency_score) / 2
    
    def _calculate_initiative(self, records: List[Dict]) -> float:
        """计算主动性"""
        if not records:
            return 0.0
        
        # 主动行为：搜索、提问、笔记、讨论
        active_types = {"search", "question", "note", "discussion", "reflection"}
        active_count = sum(
            1 for r in records 
            if r.get("behavior_type", "").lower() in active_types
        )
        
        total = len(records)
        ratio = active_count / total if total > 0 else 0
        
        return min(100, ratio * 200)  # 50%主动行为为满分
    
    def _calculate_consistency(
        self, 
        records: List[Dict], 
        period_days: int
    ) -> float:
        """计算持续性"""
        if not records or period_days <= 0:
            return 0.0
        
        # 按天统计学习行为
        daily_counts = defaultdict(int)
        for r in records:
            ts = r.get("timestamp")
            if isinstance(ts, datetime):
                day = ts.strftime("%Y-%m-%d")
            else:
                day = str(ts)[:10] if ts else ""
            if day:
                daily_counts[day] += 1
        
        # 计算变异系数（越小越稳定）
        if len(daily_counts) < 2:
            return 50.0
        
        counts = list(daily_counts.values())
        mean = np.mean(counts)
        std = np.std(counts)
        
        if mean == 0:
            return 0.0
        
        cv = std / mean  # 变异系数
        consistency = max(0, 100 - cv * 50)  # 转换为得分
        
        return consistency
    
    def _calculate_engagement(self, records: List[Dict]) -> float:
        """计算投入度"""
        if not records:
            return 0.0
        
        # 基于平均学习时长和互动深度
        durations = [r.get("duration", 0) for r in records]
        avg_duration = np.mean(durations) if durations else 0
        
        # 基于有metadata深度的记录比例
        deep_records = sum(
            1 for r in records 
            if r.get("metadata") and len(r.get("metadata", {})) > 2
        )
        depth_ratio = deep_records / len(records) if records else 0
        
        # 综合得分
        duration_score = min(100, avg_duration / 60 * 20)  # 5分钟平均为满分
        depth_score = depth_ratio * 100
        
        return (duration_score + depth_score) / 2


# =============================================================================
# 学习轨迹分析引擎
# =============================================================================

class TrajectoryAnalyzer:
    """学习轨迹分析器"""
    
    def analyze_trajectory(
        self,
        data_points: List[LearningTrajectoryPoint]
    ) -> Dict[str, Any]:
        """
        分析学习轨迹
        
        Args:
            data_points: 轨迹数据点
        
        Returns:
            分析结果
        """
        if len(data_points) < 2:
            return {
                "trend": "insufficient_data",
                "slope": 0.0,
                "direction": "stable",
                "projection": []
            }
        
        # 按时间排序
        sorted_points = sorted(data_points, key=lambda p: p.date)
        
        # 提取得分序列
        scores = [p.score for p in sorted_points]
        times = list(range(len(scores)))
        
        # 线性回归计算趋势
        slope, intercept, r_value, p_value, std_err = stats.linregress(times, scores)
        
        # 判定趋势方向
        if slope > 2:
            direction = "up"
        elif slope < -2:
            direction = "down"
        else:
            direction = "stable"
        
        # 预测未来3个点
        projection = []
        for i in range(1, 4):
            pred_score = slope * (len(scores) + i) + intercept
            projection.append(round(max(0, min(100, pred_score)), 2))
        
        return {
            "trend": {
                "slope": round(slope, 4),
                "r_squared": round(r_value ** 2, 4),
                "p_value": round(p_value, 4)
            },
            "direction": direction,
            "current_level": EvaluationLevelUtil.get_level(scores[-1]),
            "projection": projection
        }
    
    def calculate_growth_rate(
        self, 
        data_points: List[LearningTrajectoryPoint]
    ) -> float:
        """计算增长率"""
        if len(data_points) < 2:
            return 0.0
        
        sorted_points = sorted(data_points, key=lambda p: p.date)
        first_score = sorted_points[0].score
        last_score = sorted_points[-1].score
        
        if first_score == 0:
            return last_score
        
        return ((last_score - first_score) / first_score) * 100


# =============================================================================
# 评分算法工具
# =============================================================================

class ScoringAlgorithms:
    """评分算法工具类"""
    
    @staticmethod
    def normalize_score(score: float, min_val: float = 0, max_val: float = 100) -> float:
        """归一化分数到[0, 100]"""
        if max_val == min_val:
            return 50.0
        normalized = (score - min_val) / (max_val - min_val) * 100
        return max(0, min(100, normalized))
    
    @staticmethod
    def weighted_average(scores: List[float], weights: List[float]) -> float:
        """加权平均"""
        if not scores or not weights or len(scores) != len(weights):
            return 0.0
        total_weight = sum(weights)
        if total_weight == 0:
            return 0.0
        return sum(s * w for s, w in zip(scores, weights)) / total_weight
    
    @staticmethod
    def calculate_percentile(value: float, distribution: List[float]) -> float:
        """计算百分位"""
        if not distribution:
            return 50.0
        return float(stats.percentileofscore(distribution, value, kind='rank'))


# =============================================================================
# 主评估系统类
# =============================================================================

class EvaluationSystem:
    """评估系统主类"""
    
    def __init__(self):
        self.assessment_engine = AssessmentEngine()
        self.value_added_engine = ValueAddedEngine()
        self.process_engine = ProcessEvaluationEngine()
        self.trajectory_analyzer = TrajectoryAnalyzer()
    
    def conduct_comprehensive_assessment(
        self,
        learner_id: str,
        data: Dict[str, Dict[str, float]]
    ) -> EvaluationResult:
        """进行综合评价"""
        return self.assessment_engine.evaluate_comprehensive(
            learner_id=learner_id,
            knowledge_scores=data.get("knowledge", {}),
            skill_scores=data.get("skill", {}),
            problem_solving_scores=data.get("problem_solving", {}),
            creative_scores=data.get("creative", {})
        )
    
    def conduct_process_assessment(
        self,
        learner_id: str,
        behavior_records: List[Dict],
        period_days: int = 7
    ) -> Dict[str, Any]:
        """进行过程性评价"""
        return self.process_engine.evaluate_process(
            learner_id=learner_id,
            behavior_records=behavior_records,
            period_days=period_days
        )
    
    def conduct_value_added_assessment(
        self,
        learner_id: str,
        baseline: Dict[str, float],
        current: Dict[str, float],
        peer_data: Optional[List[Dict]] = None
    ) -> ValueAddedResult:
        """进行增值评价"""
        return self.value_added_engine.calculate_value_added(
            learner_id=learner_id,
            baseline_scores=baseline,
            current_scores=current,
            peer_gains=peer_data
        )
    
    def analyze_learning_trajectory(
        self,
        data_points: List[LearningTrajectoryPoint]
    ) -> Dict[str, Any]:
        """分析学习轨迹"""
        return self.trajectory_analyzer.analyze_trajectory(data_points)
