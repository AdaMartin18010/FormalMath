"""
实时调整引擎
实现学习进度监控、困难检测与干预、路径动态调整
"""

from datetime import datetime, timedelta
from typing import Dict, List, Optional, Any, Tuple
from dataclasses import dataclass, field
from enum import Enum
import uuid

from models.learner import LearnerProfile, LearningRecord
from models.learning_path import LearningPath, PathNode, NodeStatus, PathStatus, PathAdjustment, LearningSchedule


class InterventionType(Enum):
    """干预类型"""
    DIFFICULTY_ADJUST = "difficulty_adjust"  # 难度调整
    RESOURCE_CHANGE = "resource_change"        # 资源更换
    REVIEW_SUGGEST = "review_suggest"          # 复习建议
    BREAK_SUGGEST = "break_suggest"            # 休息建议
    PEER_HELP = "peer_help"                    # 同伴求助
    SKIP_SUGGEST = "skip_suggest"              # 跳过建议


class DifficultySignal(Enum):
    """困难信号"""
    TOO_EASY = "too_easy"      # 太简单
    APPROPRIATE = "appropriate"  # 适中
    TOO_HARD = "too_hard"      # 太难


@dataclass
class LearningProgress:
    """学习进度状态"""
    learner_id: str = ""
    path_id: str = ""

    # 当前状态
    current_node_id: Optional[str] = None
    current_session_start: Optional[datetime] = None

    # 进度统计
    completed_nodes: List[str] = field(default_factory=list)
    in_progress_nodes: List[str] = field(default_factory=list)

    # 时间统计
    total_study_time_minutes: int = 0
    session_count: int = 0
    average_session_duration: float = 0.0

    # 表现统计
    average_mastery_rate: float = 0.0
    success_rate: float = 0.0

    # 困难检测
    difficulty_signals: List[Dict[str, Any]] = field(default_factory=list)
    struggle_concepts: List[str] = field(default_factory=list)

    def update_with_record(self, record: LearningRecord):
        """根据学习记录更新进度"""
        self.total_study_time_minutes += record.duration_minutes
        self.session_count += 1
        self.average_session_duration = self.total_study_time_minutes / self.session_count

        if record.performance_score >= 0.7:
            if record.concept_id not in self.completed_nodes:
                self.completed_nodes.append(record.concept_id)
            if record.concept_id in self.in_progress_nodes:
                self.in_progress_nodes.remove(record.concept_id)
        else:
            if record.concept_id not in self.in_progress_nodes:
                self.in_progress_nodes.append(record.concept_id)

        # 更新成功率
        total_attempts = len(self.completed_nodes) + len(self.in_progress_nodes)
        if total_attempts > 0:
            self.success_rate = len(self.completed_nodes) / total_attempts


@dataclass
class DifficultyDetection:
    """困难检测结果"""
    concept_id: str = ""
    signal: DifficultySignal = DifficultySignal.APPROPRIATE
    confidence: float = 0.0

    # 检测指标
    time_ratio: float = 1.0  # 实际时间/预计时间
    attempt_count: int = 0
    error_rate: float = 0.0
    help_requests: int = 0

    # 建议
    suggested_action: str = ""
    alternative_resources: List[str] = field(default_factory=list)


class RealTimeMonitor:
    """实时监控器"""

    def __init__(self, learner: LearnerProfile, path: LearningPath):
        self.learner = learner
        self.path = path
        self.progress = LearningProgress(
            learner_id=learner.learner_id,
            path_id=path.path_id
        )
        self.records: List[LearningRecord] = []

    def start_session(self, node_id: str):
        """开始学习会话"""
        self.progress.current_node_id = node_id
        self.progress.current_session_start = datetime.now()

    def end_session(self, performance_score: float, notes: str = ""):
        """结束学习会话"""
        if not self.progress.current_node_id:
            return

        session_end = datetime.now()
        duration = int((session_end - self.progress.current_session_start).total_seconds() / 60)

        record = LearningRecord(
            learner_id=self.learner.learner_id,
            concept_id=self.progress.current_node_id,
            start_time=self.progress.current_session_start,
            end_time=session_end,
            duration_minutes=duration,
            performance_score=performance_score,
            feedback=notes
        )

        self.records.append(record)
        self.progress.update_with_record(record)

        # 更新路径节点
        if self.progress.current_node_id in self.path.nodes:
            node = self.path.nodes[self.progress.current_node_id]
            node.completion_percentage = min(1.0, node.completion_percentage + 0.2)
            node.mastery_level = performance_score

            if performance_score >= node.mastery_threshold:
                node.status = NodeStatus.COMPLETED
                node.actual_end = session_end
            else:
                node.status = NodeStatus.IN_PROGRESS

        self.progress.current_node_id = None
        self.progress.current_session_start = None

        return record

    def detect_difficulty(self, node_id: str, current_metrics: Dict[str, Any]) -> DifficultyDetection:
        """检测学习难度是否合适"""
        node = self.path.nodes.get(node_id)
        if not node:
            return DifficultyDetection(concept_id=node_id)

        detection = DifficultyDetection(concept_id=node_id)

        # 计算时间比例
        estimated_time = node.estimated_duration
        actual_time = current_metrics.get("time_spent", estimated_time)
        detection.time_ratio = actual_time / max(estimated_time, 1)

        # 获取尝试次数
        detection.attempt_count = current_metrics.get("attempt_count", 1)

        # 计算错误率
        errors = current_metrics.get("error_count", 0)
        detection.error_rate = errors / max(detection.attempt_count, 1)

        # 帮助请求次数
        detection.help_requests = current_metrics.get("help_requests", 0)

        # 综合判断
        signals = []

        # 时间信号
        if detection.time_ratio < 0.5:
            signals.append((DifficultySignal.TOO_EASY, 0.6))
        elif detection.time_ratio > 2.0:
            signals.append((DifficultySignal.TOO_HARD, 0.7))

        # 错误率信号
        if detection.error_rate < 0.1:
            signals.append((DifficultySignal.TOO_EASY, 0.4))
        elif detection.error_rate > 0.5:
            signals.append((DifficultySignal.TOO_HARD, 0.8))

        # 帮助请求信号
        if detection.help_requests >= 3:
            signals.append((DifficultySignal.TOO_HARD, 0.6))

        # 综合判断
        if signals:
            # 取加权平均
            hard_score = sum(conf for sig, conf in signals if sig == DifficultySignal.TOO_HARD)
            easy_score = sum(conf for sig, conf in signals if sig == DifficultySignal.TOO_EASY)

            if hard_score > easy_score and hard_score > 0.5:
                detection.signal = DifficultySignal.TOO_HARD
                detection.confidence = min(hard_score, 1.0)
                detection.suggested_action = "降低难度或提供额外支持"
            elif easy_score > hard_score and easy_score > 0.5:
                detection.signal = DifficultySignal.TOO_EASY
                detection.confidence = min(easy_score, 1.0)
                detection.suggested_action = "提高难度或加速进度"

        self.progress.difficulty_signals.append({
            "node_id": node_id,
            "signal": detection.signal.value,
            "confidence": detection.confidence,
            "timestamp": datetime.now().isoformat()
        })

        if detection.signal == DifficultySignal.TOO_HARD:
            self.progress.struggle_concepts.append(node_id)

        return detection

    def check_progress_anomaly(self) -> List[Dict[str, Any]]:
        """检查进度异常"""
        anomalies = []

        # 检查长时间停滞
        if self.progress.current_node_id:
            node = self.path.nodes.get(self.progress.current_node_id)
            if node and self.progress.current_session_start:
                elapsed = (datetime.now() - self.progress.current_session_start).total_seconds() / 60
                if elapsed > node.estimated_duration * 2:
                    anomalies.append({
                        "type": "time_exceeded",
                        "node_id": self.progress.current_node_id,
                        "message": f"学习时间过长，建议休息或寻求帮助",
                        "severity": "warning"
                    })

        # 检查连续失败
        recent_records = self.records[-3:]
        if len(recent_records) >= 3:
            avg_score = sum(r.performance_score for r in recent_records) / 3
            if avg_score < 0.5:
                anomalies.append({
                    "type": "consecutive_low_scores",
                    "message": "最近几次学习表现不佳，建议调整学习策略",
                    "severity": "critical"
                })

        # 检查学习停滞
        if len(self.records) > 5:
            last_progress = self.path.calculate_overall_progress()
            if last_progress < 0.1:
                anomalies.append({
                    "type": "no_progress",
                    "message": "学习进度缓慢，建议重新评估学习路径",
                    "severity": "warning"
                })

        return anomalies


class PathAdjustmentEngine:
    """路径调整引擎"""

    def __init__(self, path: LearningPath, learner: LearnerProfile):
        self.path = path
        self.learner = learner
        self.adjustments: List[PathAdjustment] = []

    def adjust_based_on_feedback(
        self,
        progress: LearningProgress,
        detection: Optional[DifficultyDetection] = None
    ) -> Optional[PathAdjustment]:
        """基于反馈调整路径"""

        adjustment = PathAdjustment(
            path_id=self.path.path_id,
            trigger_type="feedback"
        )

        # 根据困难检测结果调整
        if detection:
            if detection.signal == DifficultySignal.TOO_HARD:
                adjustment.reason = "检测到学习困难，需要降低难度"
                self._add_supportive_content(adjustment, detection.concept_id)
                self._extend_time_allocation(adjustment, detection.concept_id)

            elif detection.signal == DifficultySignal.TOO_EASY:
                adjustment.reason = "内容过于简单，需要提高挑战"
                self._increase_difficulty(adjustment, detection.concept_id)

        # 检查是否需要复习
        review_nodes = self._identify_review_needed(progress)
        if review_nodes:
            self._insert_review_nodes(adjustment, review_nodes)

        # 检查时间进度
        time_adjustment = self._check_time_progress(progress)
        if time_adjustment:
            adjustment.adjustments_made["time_adjustment"] = time_adjustment

        if adjustment.adjustments_made or adjustment.nodes_added:
            self.adjustments.append(adjustment)
            return adjustment

        return None

    def _add_supportive_content(self, adjustment: PathAdjustment, node_id: str):
        """添加支持性内容"""
        if node_id not in self.path.nodes:
            return

        node = self.path.nodes[node_id]

        # 添加预备知识节点
        # 简化处理：添加一个辅助节点
        support_node = PathNode(
            concept_id=f"support_{node_id}",
            sequence_number=node.sequence_number,
            status=NodeStatus.AVAILABLE,
            estimated_duration=30,
            prerequisites=[],
            difficulty=max(1, node.difficulty - 1),
            importance=0.5
        )

        adjustment.nodes_added.append(support_node.node_id)
        adjustment.adjustments_made["added_support_content"] = True

    def _extend_time_allocation(self, adjustment: PathAdjustment, node_id: str):
        """延长学习时间分配"""
        if node_id in self.path.nodes:
            node = self.path.nodes[node_id]
            original_time = node.estimated_duration
            new_time = int(original_time * 1.5)
            node.estimated_duration = new_time

            adjustment.adjustments_made["extended_time"] = {
                "node_id": node_id,
                "original": original_time,
                "new": new_time
            }

    def _increase_difficulty(self, adjustment: PathAdjustment, node_id: str):
        """增加难度"""
        if node_id in self.path.nodes:
            node = self.path.nodes[node_id]

            # 增加挑战性任务
            adjustment.adjustments_made["increased_challenge"] = True
            adjustment.adjustments_made["bonus_tasks"] = [
                "尝试更复杂的例子",
                "探索相关的高级概念"
            ]

    def _identify_review_needed(self, progress: LearningProgress) -> List[str]:
        """识别需要复习的节点"""
        review_needed = []

        # 检查已完成的节点中哪些需要复习
        for node_id in progress.completed_nodes:
            if node_id in self.path.nodes:
                node = self.path.nodes[node_id]
                # 简单规则：如果掌握度低于0.8，建议复习
                if node.mastery_level < 0.8:
                    review_needed.append(node_id)

        return review_needed

    def _insert_review_nodes(self, adjustment: PathAdjustment, review_nodes: List[str]):
        """插入复习节点"""
        for node_id in review_nodes[:3]:  # 限制复习节点数量
            review_node = PathNode(
                concept_id=f"review_{node_id}",
                sequence_number=-1,  # 稍后确定
                status=NodeStatus.AVAILABLE,
                estimated_duration=20,
                prerequisites=[],
                difficulty=1,
                importance=0.6
            )
            adjustment.nodes_added.append(review_node.node_id)

        adjustment.adjustments_made["added_review_nodes"] = len(review_nodes[:3])

    def _check_time_progress(self, progress: LearningProgress) -> Optional[Dict[str, Any]]:
        """检查时间进度"""
        if not self.path.target_completion:
            return None

        remaining_time = self.path.target_completion - datetime.now()
        remaining_hours = remaining_time.total_seconds() / 3600

        path_remaining = self.path.get_remaining_time()

        if path_remaining > remaining_hours:
            # 需要加快进度
            return {
                "type": "accelerate",
                "message": f"进度落后，建议每日学习时长增加到 {path_remaining / max(remaining_hours / 24, 1):.1f} 小时"
            }

        return None

    def optimize_path_for_remaining(self) -> PathAdjustment:
        """为剩余内容优化路径"""
        adjustment = PathAdjustment(
            path_id=self.path.path_id,
            reason="优化剩余学习路径",
            trigger_type="optimization"
        )

        # 获取剩余节点
        remaining = [
            node_id for node_id in self.path.node_order
            if self.path.nodes[node_id].status != NodeStatus.COMPLETED
        ]

        # 简化路径：移除重要性较低的节点
        to_remove = []
        for node_id in remaining:
            node = self.path.nodes[node_id]
            if node.importance < 0.4 and len(to_remove) < len(remaining) * 0.2:
                to_remove.append(node_id)

        adjustment.nodes_removed = to_remove
        adjustment.adjustments_made["removed_low_priority"] = len(to_remove)

        self.adjustments.append(adjustment)
        return adjustment


class SpacedRepetitionScheduler:
    """间隔重复调度器（基于遗忘曲线）"""

    def __init__(self, path: LearningPath, learner: LearnerProfile):
        self.path = path
        self.learner = learner
        self.schedule: Dict[str, List[datetime]] = {}  # 复习计划

    def calculate_review_intervals(
        self,
        concept_id: str,
        mastery_level: float,
        review_count: int = 0
    ) -> List[int]:
        """
        计算复习间隔（天数）
        基于艾宾浩斯遗忘曲线和掌握度调整
        """
        # 基础间隔（艾宾浩斯遗忘曲线简化版）
        base_intervals = [1, 2, 4, 7, 15, 30, 60, 120]

        # 根据掌握度调整
        if mastery_level >= 0.9:
            multiplier = 2.0
        elif mastery_level >= 0.8:
            multiplier = 1.5
        elif mastery_level >= 0.7:
            multiplier = 1.0
        else:
            multiplier = 0.7

        # 根据已复习次数选择间隔
        intervals = base_intervals[review_count:review_count + 4]
        adjusted_intervals = [int(i * multiplier) for i in intervals]

        return adjusted_intervals

    def schedule_reviews(self, completed_nodes: List[str]) -> Dict[str, List[datetime]]:
        """为已完成的节点安排复习"""
        review_schedule = {}

        for node_id in completed_nodes:
            if node_id not in self.path.nodes:
                continue

            node = self.path.nodes[node_id]

            # 计算复习间隔
            intervals = self.calculate_review_intervals(
                node_id,
                node.mastery_level,
                review_count=0
            )

            # 计算复习日期
            base_date = node.actual_end or datetime.now()
            review_dates = [
                base_date + timedelta(days=interval)
                for interval in intervals
            ]

            review_schedule[node_id] = review_dates
            self.schedule[node_id] = review_dates

        return review_schedule

    def get_due_reviews(self, date: Optional[datetime] = None) -> List[Dict[str, Any]]:
        """获取指定日期需要复习的内容"""
        if date is None:
            date = datetime.now()

        due_reviews = []

        for concept_id, review_dates in self.schedule.items():
            for i, review_date in enumerate(review_dates):
                # 检查日期是否匹配（允许±1天的误差）
                if abs((review_date - date).days) <= 1:
                    node = self.path.nodes.get(concept_id)
                    if node:
                        due_reviews.append({
                            "concept_id": concept_id,
                            "concept_name": node.concept_id,
                            "review_date": review_date.isoformat(),
                            "review_number": i + 1,
                            "mastery_level": node.mastery_level,
                            "estimated_time": 20  # 复习时间较短
                        })

        # 按复习次数排序（优先复习次数少的）
        due_reviews.sort(key=lambda x: x["review_number"])

        return due_reviews

    def update_after_review(
        self,
        concept_id: str,
        performance: float,
        review_number: int
    ):
        """复习后更新计划"""
        if concept_id not in self.path.nodes:
            return

        node = self.path.nodes[concept_id]

        # 更新掌握度
        node.mastery_level = node.mastery_level * 0.7 + performance * 0.3

        # 如果表现不佳，增加额外复习
        if performance < 0.6:
            # 在2天后增加一次复习
            extra_review = datetime.now() + timedelta(days=2)
            if concept_id in self.schedule:
                self.schedule[concept_id].insert(review_number + 1, extra_review)


class FeedbackLoop:
    """学习效果反馈循环"""

    def __init__(self, learner: LearnerProfile, path: LearningPath):
        self.learner = learner
        self.path = path
        self.feedback_history: List[Dict[str, Any]] = []

    def generate_feedback(self, recent_records: List[LearningRecord]) -> Dict[str, Any]:
        """生成学习反馈"""
        if not recent_records:
            return {"message": "暂无学习记录"}

        feedback = {
            "period": {
                "start": recent_records[0].start_time.isoformat(),
                "end": recent_records[-1].end_time.isoformat() if recent_records[-1].end_time else None
            },
            "summary": {},
            "achievements": [],
            "suggestions": [],
            "next_steps": []
        }

        # 计算统计信息
        total_time = sum(r.duration_minutes for r in recent_records)
        avg_score = sum(r.performance_score for r in recent_records) / len(recent_records)
        concepts_covered = len(set(r.concept_id for r in recent_records))

        feedback["summary"] = {
            "total_study_time_minutes": total_time,
            "average_score": round(avg_score, 2),
            "concepts_covered": concepts_covered,
            "session_count": len(recent_records)
        }

        # 成就
        if avg_score >= 0.9:
            feedback["achievements"].append("🌟 优秀表现：平均成绩超过90%")
        if total_time >= 120:
            feedback["achievements"].append("📚 勤奋学习：累计学习超过2小时")
        if concepts_covered >= 3:
            feedback["achievements"].append("🎯 多元学习：学习了3个或以上概念")

        # 建议
        if avg_score < 0.6:
            feedback["suggestions"].append("💡 建议：当前难度可能过高，考虑调整学习策略")
        if total_time < 30:
            feedback["suggestions"].append("⏰ 建议：增加学习时间可以提高效果")

        # 下一步
        current = self.path.get_current_node()
        if current:
            feedback["next_steps"].append({
                "type": "continue",
                "concept": current.concept_id,
                "message": f"继续学习：{current.concept_id}"
            })

        available = self.path.get_available_nodes()
        if available:
            feedback["next_steps"].append({
                "type": "available",
                "count": len(available),
                "message": f"有 {len(available)} 个新概念可以学习"
            })

        self.feedback_history.append(feedback)
        return feedback

    def generate_weekly_report(self) -> Dict[str, Any]:
        """生成周报"""
        # 获取本周记录
        week_ago = datetime.now() - timedelta(days=7)
        recent_records = [r for r in self.feedback_history if
                        isinstance(r.get("period"), dict) and
                        datetime.fromisoformat(r["period"]["start"]) >= week_ago]

        if not recent_records:
            return {"message": "本周暂无学习记录"}

        return {
            "period": "本周",
            "total_sessions": len(recent_records),
            "summary": "学习周报生成完成",
            "recommendations": [
                "保持当前的学习节奏",
                "定期复习已学内容",
                "尝试更多实践练习"
            ]
        }
