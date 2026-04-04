"""
遗忘曲线建模与间隔重复调度
基于艾宾浩斯遗忘曲线和优化算法实现智能复习调度
"""
import math
import numpy as np
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from scipy.optimize import minimize_scalar
import json


@dataclass
class MemoryTrace:
    """记忆痕迹"""
    concept_id: str
    initial_strength: float  # 初始记忆强度
    current_strength: float  # 当前记忆强度
    created_at: datetime
    last_reviewed: datetime
    review_count: int = 0
    review_history: List[Dict] = field(default_factory=list)
    forgetting_rate: float = 0.1  # 遗忘率
    
    def to_dict(self) -> Dict:
        return {
            'concept_id': self.concept_id,
            'initial_strength': self.initial_strength,
            'current_strength': self.current_strength,
            'created_at': self.created_at.isoformat(),
            'last_reviewed': self.last_reviewed.isoformat(),
            'review_count': self.review_count,
            'review_history': self.review_history,
            'forgetting_rate': self.forgetting_rate
        }


@dataclass
class ReviewSchedule:
    """复习计划"""
    concept_id: str
    scheduled_time: datetime
    priority: float
    estimated_retention: float
    optimal_interval: timedelta
    review_type: str  # 'scheduled', 'urgent', 'maintenance'
    
    def to_dict(self) -> Dict:
        return {
            'concept_id': self.concept_id,
            'scheduled_time': self.scheduled_time.isoformat(),
            'priority': self.priority,
            'estimated_retention': self.estimated_retention,
            'optimal_interval_hours': self.optimal_interval.total_seconds() / 3600,
            'review_type': self.review_type
        }


class ForgettingCurveModel:
    """
    遗忘曲线模型
    
    基于改进的艾宾浩斯遗忘曲线：
    R(t) = e^(-λ * t / S)
    
    其中：
    - R(t): 时间t后的记忆保持率
    - λ: 基础遗忘率
    - t: 经过的时间
    - S: 记忆强度（随复习增加）
    """
    
    def __init__(
        self,
        base_forgetting_rate: float = 0.3,
        memory_strength_factor: float = 1.2,
        min_interval_hours: float = 0.5,
        max_interval_days: float = 365
    ):
        self.base_forgetting_rate = base_forgetting_rate
        self.memory_strength_factor = memory_strength_factor
        self.min_interval_hours = min_interval_hours
        self.max_interval_days = max_interval_days
        
        # 存储记忆痕迹
        self.memory_traces: Dict[str, MemoryTrace] = {}
        
        # 个性化遗忘率调整
        self.user_adjustment_factor = 1.0
    
    def set_user_adjustment(self, factor: float):
        """设置用户特定的遗忘率调整因子"""
        self.user_adjustment_factor = max(0.5, min(2.0, factor))
    
    def calculate_retention(
        self,
        concept_id: str,
        at_time: Optional[datetime] = None
    ) -> float:
        """
        计算特定时间的记忆保持率
        
        Args:
            concept_id: 概念ID
            at_time: 指定时间，默认为当前时间
        
        Returns:
            记忆保持率 0-1
        """
        if concept_id not in self.memory_traces:
            return 0.0
        
        trace = self.memory_traces[concept_id]
        
        if at_time is None:
            at_time = datetime.utcnow()
        
        # 计算经过的时间（小时）
        elapsed = (at_time - trace.last_reviewed).total_seconds() / 3600
        
        # 应用遗忘曲线公式
        # R = e^(-λ * t / S)
        adjusted_rate = trace.forgetting_rate * self.user_adjustment_factor
        retention = math.exp(-adjusted_rate * elapsed / max(trace.current_strength, 0.1))
        
        return max(0.0, min(1.0, retention))
    
    def create_memory_trace(
        self,
        concept_id: str,
        initial_strength: float = 1.0,
        timestamp: Optional[datetime] = None
    ) -> MemoryTrace:
        """
        创建新的记忆痕迹
        
        Args:
            concept_id: 概念ID
            initial_strength: 初始记忆强度
            timestamp: 时间戳
        
        Returns:
            记忆痕迹对象
        """
        if timestamp is None:
            timestamp = datetime.utcnow()
        
        trace = MemoryTrace(
            concept_id=concept_id,
            initial_strength=initial_strength,
            current_strength=initial_strength,
            created_at=timestamp,
            last_reviewed=timestamp,
            review_count=0,
            forgetting_rate=self._estimate_forgetting_rate(concept_id)
        )
        
        self.memory_traces[concept_id] = trace
        return trace
    
    def _estimate_forgetting_rate(self, concept_id: str) -> float:
        """估计特定概念的遗忘率（可根据概念复杂度调整）"""
        # 基础遗忘率，可以根据概念特征调整
        # 例如抽象概念可能有更高的遗忘率
        return self.base_forgetting_rate
    
    def review_concept(
        self,
        concept_id: str,
        performance: float,  # 0-1, 复习表现
        review_duration: int = 0,  # 复习持续时间（秒）
        timestamp: Optional[datetime] = None
    ) -> MemoryTrace:
        """
        处理概念复习
        
        Args:
            concept_id: 概念ID
            performance: 复习表现 0-1
            review_duration: 复习持续时间
            timestamp: 时间戳
        
        Returns:
            更新后的记忆痕迹
        """
        if timestamp is None:
            timestamp = datetime.utcnow()
        
        if concept_id not in self.memory_traces:
            self.create_memory_trace(concept_id, timestamp=timestamp)
        
        trace = self.memory_traces[concept_id]
        
        # 更新记忆强度
        # 基于表现和复习间隔计算新的强度
        time_since_last = (timestamp - trace.last_reviewed).total_seconds() / 3600
        
        # 间隔重复强度增长模型
        # 表现越好，强度增长越多
        # 间隔越长（但不超过最佳间隔），强度增长越多
        base_increase = performance * self.memory_strength_factor
        
        # 间隔因子：适当长的间隔有助于长期记忆
        optimal_interval = self._calculate_optimal_interval(trace)
        interval_factor = 1.0 + 0.5 * min(time_since_last / optimal_interval, 2.0)
        
        # 更新记忆强度
        strength_increase = base_increase * interval_factor
        trace.current_strength += strength_increase
        trace.current_strength = min(trace.current_strength, 10.0)  # 上限
        
        # 根据表现调整遗忘率
        # 表现好 -> 遗忘率降低（记忆更牢固）
        if performance >= 0.9:
            trace.forgetting_rate *= 0.9
        elif performance >= 0.7:
            trace.forgetting_rate *= 0.95
        elif performance < 0.5:
            trace.forgetting_rate *= 1.1
        
        trace.forgetting_rate = max(0.05, min(0.5, trace.forgetting_rate))
        
        # 更新历史
        trace.review_count += 1
        trace.review_history.append({
            'timestamp': timestamp.isoformat(),
            'performance': performance,
            'duration': review_duration,
            'retention_before': self.calculate_retention(concept_id, timestamp),
            'strength_after': trace.current_strength
        })
        
        trace.last_reviewed = timestamp
        
        return trace
    
    def _calculate_optimal_interval(self, trace: MemoryTrace) -> float:
        """计算最佳复习间隔（小时）"""
        # 基于记忆强度和遗忘率计算
        # 目标是保持记忆保持率在80%左右
        target_retention = 0.8
        adjusted_rate = trace.forgetting_rate * self.user_adjustment_factor
        
        if adjusted_rate <= 0:
            return self.max_interval_days * 24
        
        # 解方程: target = exp(-λ * t / S)
        # t = -S * ln(target) / λ
        optimal_hours = -trace.current_strength * math.log(target_retention) / adjusted_rate
        
        # 限制在合理范围内
        optimal_hours = max(
            self.min_interval_hours,
            min(optimal_hours, self.max_interval_days * 24)
        )
        
        return optimal_hours
    
    def predict_forgetting_curve(
        self,
        concept_id: str,
        hours_ahead: int = 168  # 默认7天
    ) -> List[Tuple[float, float]]:
        """
        预测未来遗忘曲线
        
        Args:
            concept_id: 概念ID
            hours_ahead: 预测时间（小时）
        
        Returns:
            [(小时, 记忆保持率), ...]
        """
        if concept_id not in self.memory_traces:
            return [(h, 0.0) for h in range(0, hours_ahead + 1, 24)]
        
        now = datetime.utcnow()
        curve = []
        
        for h in range(0, hours_ahead + 1, max(1, hours_ahead // 20)):
            future_time = now + timedelta(hours=h)
            retention = self.calculate_retention(concept_id, future_time)
            curve.append((float(h), float(retention)))
        
        return curve
    
    def get_critical_concepts(
        self,
        threshold: float = 0.3,
        max_results: int = 10
    ) -> List[Tuple[str, float]]:
        """
        获取即将遗忘的概念
        
        Args:
            threshold: 临界保持率
            max_results: 最大返回数量
        
        Returns:
            [(概念ID, 当前保持率), ...]
        """
        critical = []
        
        for concept_id, trace in self.memory_traces.items():
            retention = self.calculate_retention(concept_id)
            if retention <= threshold:
                # 计算紧急程度（越快遗忘越紧急）
                urgency = (threshold - retention) / threshold
                critical.append((concept_id, retention, urgency))
        
        # 按紧急程度排序
        critical.sort(key=lambda x: x[2], reverse=True)
        
        return [(c[0], c[1]) for c in critical[:max_results]]
    
    def get_learning_statistics(self) -> Dict:
        """获取学习统计"""
        if not self.memory_traces:
            return {
                'total_concepts': 0,
                'average_retention': 0,
                'total_reviews': 0,
                'concepts_needing_review': 0
            }
        
        retentions = [self.calculate_retention(cid) for cid in self.memory_traces.keys()]
        total_reviews = sum(t.review_count for t in self.memory_traces.values())
        
        return {
            'total_concepts': len(self.memory_traces),
            'average_retention': float(np.mean(retentions)),
            'retention_std': float(np.std(retentions)),
            'total_reviews': total_reviews,
            'average_reviews_per_concept': total_reviews / len(self.memory_traces),
            'concepts_needing_review': sum(1 for r in retentions if r < 0.5),
            'high_retention_concepts': sum(1 for r in retentions if r >= 0.8)
        }


class SpacedRepetitionScheduler:
    """
    间隔重复调度器
    
    使用优化算法为学习者生成最优复习计划
    """
    
    def __init__(
        self,
        forgetting_model: Optional[ForgettingCurveModel] = None,
        max_daily_reviews: int = 20,
        target_retention: float = 0.8
    ):
        self.model = forgetting_model or ForgettingCurveModel()
        self.max_daily_reviews = max_daily_reviews
        self.target_retention = target_retention
        
        # 用户偏好
        self.user_preferences = {
            'preferred_study_times': [9, 14, 20],  # 偏好学习时间（小时）
            'session_duration': 30,  # 每次学习时长（分钟）
            'max_new_concepts_per_session': 5
        }
    
    def set_user_preferences(self, preferences: Dict):
        """设置用户偏好"""
        self.user_preferences.update(preferences)
    
    def generate_schedule(
        self,
        concept_ids: Optional[List[str]] = None,
        days_ahead: int = 7,
        start_time: Optional[datetime] = None
    ) -> List[ReviewSchedule]:
        """
        生成复习计划
        
        Args:
            concept_ids: 指定概念列表，None表示所有概念
            days_ahead: 计划天数
            start_time: 开始时间
        
        Returns:
            复习计划列表
        """
        if start_time is None:
            start_time = datetime.utcnow()
        
        if concept_ids is None:
            concept_ids = list(self.model.memory_traces.keys())
        
        schedules = []
        end_time = start_time + timedelta(days=days_ahead)
        
        for concept_id in concept_ids:
            if concept_id not in self.model.memory_traces:
                continue
            
            trace = self.model.memory_traces[concept_id]
            
            # 计算当前保持率
            current_retention = self.model.calculate_retention(concept_id)
            
            # 如果保持率低于目标，需要复习
            if current_retention < self.target_retention:
                # 紧急复习
                schedule = self._create_urgent_schedule(
                    concept_id, start_time, current_retention
                )
                schedules.append(schedule)
            else:
                # 计算最佳复习时间
                optimal_interval = self.model._calculate_optimal_interval(trace)
                scheduled_time = trace.last_reviewed + timedelta(hours=optimal_interval)
                
                # 只安排在计划期内
                if scheduled_time <= end_time:
                    estimated_retention = self.model.calculate_retention(concept_id, scheduled_time)
                    
                    schedule = ReviewSchedule(
                        concept_id=concept_id,
                        scheduled_time=scheduled_time,
                        priority=self._calculate_priority(concept_id, estimated_retention),
                        estimated_retention=estimated_retention,
                        optimal_interval=timedelta(hours=optimal_interval),
                        review_type='scheduled'
                    )
                    schedules.append(schedule)
        
        # 按优先级和时间排序
        schedules.sort(key=lambda s: (s.scheduled_time, -s.priority))
        
        # 应用日常限制
        schedules = self._apply_daily_limits(schedules)
        
        return schedules
    
    def _create_urgent_schedule(
        self,
        concept_id: str,
        start_time: datetime,
        current_retention: float
    ) -> ReviewSchedule:
        """创建紧急复习计划"""
        # 尽快安排
        urgency = (self.target_retention - current_retention) / self.target_retention
        
        # 选择最近的偏好学习时间
        current_hour = start_time.hour
        preferred_times = self.user_preferences['preferred_study_times']
        
        next_preferred = None
        for pt in preferred_times:
            if pt > current_hour:
                next_preferred = pt
                break
        
        if next_preferred is None:
            # 明天的第一个偏好时间
            scheduled_time = start_time + timedelta(days=1)
            scheduled_time = scheduled_time.replace(hour=preferred_times[0], minute=0)
        else:
            scheduled_time = start_time.replace(hour=next_preferred, minute=0)
        
        return ReviewSchedule(
            concept_id=concept_id,
            scheduled_time=scheduled_time,
            priority=urgency * 2,  # 紧急任务优先级加倍
            estimated_retention=current_retention,
            optimal_interval=timedelta(hours=1),
            review_type='urgent'
        )
    
    def _calculate_priority(self, concept_id: str, estimated_retention: float) -> float:
        """计算复习优先级"""
        trace = self.model.memory_traces.get(concept_id)
        if not trace:
            return 0.5
        
        # 基于多个因素
        factors = {
            'retention_decay': 1 - estimated_retention,
            'importance': min(trace.review_count / 10, 1.0),  # 复习次数越多越重要
            'difficulty': trace.forgetting_rate / 0.5  # 遗忘率越高越难
        }
        
        # 加权综合
        priority = (
            0.5 * factors['retention_decay'] +
            0.3 * factors['importance'] +
            0.2 * factors['difficulty']
        )
        
        return min(1.0, priority)
    
    def _apply_daily_limits(self, schedules: List[ReviewSchedule]) -> List[ReviewSchedule]:
        """应用每日复习数量限制"""
        # 按日期分组
        daily_schedules: Dict[str, List[ReviewSchedule]] = {}
        
        for s in schedules:
            date_key = s.scheduled_time.strftime('%Y-%m-%d')
            if date_key not in daily_schedules:
                daily_schedules[date_key] = []
            daily_schedules[date_key].append(s)
        
        # 限制每天数量
        limited_schedules = []
        for date_key, day_schedules in sorted(daily_schedules.items()):
            # 按优先级排序并限制
            day_schedules.sort(key=lambda s: -s.priority)
            limited_schedules.extend(day_schedules[:self.max_daily_reviews])
        
        return sorted(limited_schedules, key=lambda s: s.scheduled_time)
    
    def optimize_schedule(
        self,
        schedules: List[ReviewSchedule],
        optimization_target: str = 'retention'
    ) -> List[ReviewSchedule]:
        """
        优化复习计划
        
        Args:
            schedules: 初始计划
            optimization_target: 优化目标 (retention, efficiency, workload)
        
        Returns:
            优化后的计划
        """
        if optimization_target == 'retention':
            # 优先保证记忆保持率
            return sorted(schedules, key=lambda s: (-s.priority, s.scheduled_time))
        
        elif optimization_target == 'efficiency':
            # 优先效率（单位时间收益）
            for s in schedules:
                # 计算效率分数
                time_cost = 1.0  # 假设每个复习成本相同
                benefit = (self.target_retention - s.estimated_retention) * s.priority
                s.efficiency_score = benefit / time_cost if time_cost > 0 else 0
            
            return sorted(schedules, key=lambda s: (-s.efficiency_score, s.scheduled_time))
        
        elif optimization_target == 'workload':
            # 平衡工作量
            return self._balance_workload(schedules)
        
        return schedules
    
    def _balance_workload(self, schedules: List[ReviewSchedule]) -> List[ReviewSchedule]:
        """平衡每日工作量"""
        # 计算每日工作量
        daily_counts: Dict[str, int] = {}
        for s in schedules:
            date_key = s.scheduled_time.strftime('%Y-%m-%d')
            daily_counts[date_key] = daily_counts.get(date_key, 0) + 1
        
        # 如果某天工作量过大，将低优先级任务推迟
        balanced = []
        for s in schedules:
            date_key = s.scheduled_time.strftime('%Y-%m-%d')
            
            if daily_counts[date_key] > self.max_daily_reviews and s.priority < 0.5:
                # 推迟到第二天
                s.scheduled_time += timedelta(days=1)
                new_date = s.scheduled_time.strftime('%Y-%m-%d')
                daily_counts[date_key] -= 1
                daily_counts[new_date] = daily_counts.get(new_date, 0) + 1
            
            balanced.append(s)
        
        return sorted(balanced, key=lambda s: s.scheduled_time)
    
    def get_daily_review_summary(self, date: Optional[datetime] = None) -> Dict:
        """获取每日复习摘要"""
        if date is None:
            date = datetime.utcnow()
        
        date_str = date.strftime('%Y-%m-%d')
        
        schedules = self.generate_schedule(days_ahead=1)
        daily_schedules = [
            s for s in schedules
            if s.scheduled_time.strftime('%Y-%m-%d') == date_str
        ]
        
        return {
            'date': date_str,
            'total_reviews': len(daily_schedules),
            'urgent_reviews': sum(1 for s in daily_schedules if s.review_type == 'urgent'),
            'scheduled_reviews': sum(1 for s in daily_schedules if s.review_type == 'scheduled'),
            'average_retention': np.mean([s.estimated_retention for s in daily_schedules]) if daily_schedules else 0,
            'estimated_duration': len(daily_schedules) * self.user_preferences['session_duration'],
            'concepts': [s.to_dict() for s in daily_schedules]
        }
    
    def adapt_to_performance(
        self,
        review_results: List[Dict[str, Any]]
    ) -> Dict:
        """
        根据复习表现自适应调整
        
        Args:
            review_results: 复习结果列表
                [{concept_id, scheduled_time, actual_performance, time_spent}, ...]
        
        Returns:
            调整结果
        """
        adjustments = {
            'forgetting_rate_adjusted': False,
            'new_factor': self.model.user_adjustment_factor,
            'recommendations': []
        }
        
        performance_sum = 0
        count = 0
        
        for result in review_results:
            concept_id = result.get('concept_id')
            performance = result.get('actual_performance', 0)
            performance_sum += performance
            count += 1
            
            # 更新模型
            if concept_id in self.model.memory_traces:
                self.model.review_concept(
                    concept_id=concept_id,
                    performance=performance,
                    review_duration=result.get('time_spent', 0)
                )
        
        # 基于整体表现调整遗忘率因子
        if count > 0:
            avg_performance = performance_sum / count
            
            if avg_performance < 0.6:
                # 表现差，可能需要更频繁的复习（增加因子）
                self.model.user_adjustment_factor = min(
                    2.0,
                    self.model.user_adjustment_factor * 1.1
                )
                adjustments['forgetting_rate_adjusted'] = True
                adjustments['new_factor'] = self.model.user_adjustment_factor
                adjustments['recommendations'].append(
                    '检测到记忆保持困难，建议增加复习频率'
                )
            elif avg_performance > 0.9:
                # 表现很好，可以适当减少复习（降低因子）
                self.model.user_adjustment_factor = max(
                    0.5,
                    self.model.user_adjustment_factor * 0.95
                )
                adjustments['forgetting_rate_adjusted'] = True
                adjustments['new_factor'] = self.model.user_adjustment_factor
                adjustments['recommendations'].append(
                    '记忆表现良好，可以适当延长复习间隔'
                )
        
        return adjustments
