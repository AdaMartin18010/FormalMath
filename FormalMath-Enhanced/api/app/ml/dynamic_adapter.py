"""
动态调整模块
根据实时学习反馈动态调整推荐策略
"""
import numpy as np
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from collections import deque
from enum import Enum


class AdaptationTrigger(Enum):
    """调整触发条件"""
    PERFORMANCE_DROP = "performance_drop"       # 表现下降
    ENGAGEMENT_DROP = "engagement_drop"         # 参与度下降
    TIME_EXCEED = "time_exceed"                 # 超时
    RAPID_PROGRESS = "rapid_progress"           # 快速进步
    MASTERY_STAGNATION = "mastery_stagnation"   # 掌握停滞


@dataclass
class LearningSignal:
    """学习信号"""
    timestamp: datetime
    concept_id: str
    signal_type: str
    value: float
    context: Dict[str, Any] = field(default_factory=dict)


@dataclass
class AdaptationAction:
    """调整动作"""
    action_type: str
    target: str
    parameters: Dict[str, Any] = field(default_factory=dict)
    reason: str = ""
    expected_outcome: str = ""
    
    def to_dict(self) -> Dict:
        return {
            'action_type': self.action_type,
            'target': self.target,
            'parameters': self.parameters,
            'reason': self.reason,
            'expected_outcome': self.expected_outcome
        }


class SignalDetector:
    """学习信号检测器"""
    
    def __init__(self, window_size: int = 10):
        self.window_size = window_size
        self.signal_history: Dict[str, deque] = {}
        
        # 阈值配置
        self.thresholds = {
            'performance_drop': 0.2,      # 表现下降20%
            'engagement_drop': 0.3,       # 参与度下降30%
            'time_exceed_ratio': 1.5,     # 超时50%
            'rapid_progress_threshold': 0.8,  # 快速进步阈值
            'stagnation_rounds': 3        # 停滞轮数
        }
    
    def detect_signals(
        self,
        user_id: str,
        interaction_data: Dict[str, Any]
    ) -> List[LearningSignal]:
        """
        检测学习信号
        
        Args:
            user_id: 用户ID
            interaction_data: 交互数据
                {
                    'concept_id': str,
                    'performance': float,  # 0-1
                    'time_spent': int,     # 秒
                    'expected_time': int,  # 秒
                    'engagement_score': float,  # 0-1
                    'mastery_level': float,     # 0-1
                    'attempt_count': int
                }
        
        Returns:
            检测到的信号列表
        """
        signals = []
        
        # 初始化历史
        if user_id not in self.signal_history:
            self.signal_history[user_id] = deque(maxlen=self.window_size)
        
        history = self.signal_history[user_id]
        
        # 检测表现下降
        if len(history) >= 3:
            recent_performance = [h['performance'] for h in list(history)[-3:]]
            current_performance = interaction_data.get('performance', 0)
            
            avg_recent = np.mean(recent_performance)
            if avg_recent - current_performance > self.thresholds['performance_drop']:
                signals.append(LearningSignal(
                    timestamp=datetime.utcnow(),
                    concept_id=interaction_data.get('concept_id', ''),
                    signal_type=AdaptationTrigger.PERFORMANCE_DROP.value,
                    value=current_performance - avg_recent,
                    context={'recent_avg': avg_recent, 'current': current_performance}
                ))
        
        # 检测参与度下降
        engagement = interaction_data.get('engagement_score', 1.0)
        if len(history) >= 2:
            prev_engagement = list(history)[-1].get('engagement_score', 1.0)
            if prev_engagement - engagement > self.thresholds['engagement_drop']:
                signals.append(LearningSignal(
                    timestamp=datetime.utcnow(),
                    concept_id=interaction_data.get('concept_id', ''),
                    signal_type=AdaptationTrigger.ENGAGEMENT_DROP.value,
                    value=engagement - prev_engagement
                ))
        
        # 检测超时
        time_spent = interaction_data.get('time_spent', 0)
        expected_time = interaction_data.get('expected_time', time_spent)
        if expected_time > 0 and time_spent > expected_time * self.thresholds['time_exceed_ratio']:
            signals.append(LearningSignal(
                timestamp=datetime.utcnow(),
                concept_id=interaction_data.get('concept_id', ''),
                signal_type=AdaptationTrigger.TIME_EXCEED.value,
                value=time_spent / expected_time
            ))
        
        # 检测快速进步
        mastery = interaction_data.get('mastery_level', 0)
        if mastery > self.thresholds['rapid_progress_threshold']:
            attempts = interaction_data.get('attempt_count', 1)
            if attempts <= 2:  # 很少尝试就掌握
                signals.append(LearningSignal(
                    timestamp=datetime.utcnow(),
                    concept_id=interaction_data.get('concept_id', ''),
                    signal_type=AdaptationTrigger.RAPID_PROGRESS.value,
                    value=mastery
                ))
        
        # 检测停滞
        if len(history) >= self.thresholds['stagnation_rounds']:
            recent_mastery = [h.get('mastery_level', 0) for h in list(history)[-self.thresholds['stagnation_rounds']:]]
            if max(recent_mastery) - min(recent_mastery) < 0.05:
                signals.append(LearningSignal(
                    timestamp=datetime.utcnow(),
                    concept_id=interaction_data.get('concept_id', ''),
                    signal_type=AdaptationTrigger.MASTERY_STAGNATION.value,
                    value=np.mean(recent_mastery)
                ))
        
        # 更新历史
        history.append(interaction_data)
        
        return signals


class StrategyAdapter:
    """策略调整器"""
    
    def __init__(self):
        self.adaptation_rules = self._initialize_rules()
        self.adaptation_history: Dict[str, List[Dict]] = {}
    
    def _initialize_rules(self) -> Dict[str, Any]:
        """初始化调整规则"""
        return {
            AdaptationTrigger.PERFORMANCE_DROP.value: {
                'actions': [
                    {'type': 'difficulty_decrease', 'amount': 0.2},
                    {'type': 'add_prerequisite_review', 'count': 1},
                    {'type': 'hint_increase', 'level': 'detailed'}
                ],
                'priority': 1
            },
            AdaptationTrigger.ENGAGEMENT_DROP.value: {
                'actions': [
                    {'type': 'content_type_change', 'preference': 'interactive'},
                    {'type': 'break_suggestion', 'duration': 10},
                    {'type': 'gamification_boost', 'enabled': True}
                ],
                'priority': 2
            },
            AdaptationTrigger.TIME_EXCEED.value: {
                'actions': [
                    {'type': 'content_chunking', 'size': 'small'},
                    {'type': 'time_estimate_adjust', 'factor': 1.3},
                    {'type': 'difficulty_decrease', 'amount': 0.1}
                ],
                'priority': 1
            },
            AdaptationTrigger.RAPID_PROGRESS.value: {
                'actions': [
                    {'type': 'difficulty_increase', 'amount': 0.15},
                    {'type': 'skip_prerequisite', 'condition': 'optional'},
                    {'type': 'bonus_content', 'enabled': True}
                ],
                'priority': 3
            },
            AdaptationTrigger.MASTERY_STAGNATION.value: {
                'actions': [
                    {'type': 'approach_change', 'method': 'alternative'},
                    {'type': 'peer_learning', 'enabled': True},
                    {'type': 'tutor_suggestion', 'level': 'light'}
                ],
                'priority': 1
            }
        }
    
    def generate_adaptations(
        self,
        user_id: str,
        signals: List[LearningSignal]
    ) -> List[AdaptationAction]:
        """生成调整动作"""
        actions = []
        
        # 按优先级排序信号
        sorted_signals = sorted(
            signals,
            key=lambda s: self.adaptation_rules.get(s.signal_type, {}).get('priority', 5)
        )
        
        for signal in sorted_signals:
            rule = self.adaptation_rules.get(signal.signal_type)
            if not rule:
                continue
            
            for action_spec in rule['actions']:
                action = self._create_action(signal, action_spec)
                if action:
                    actions.append(action)
        
        # 记录历史
        if user_id not in self.adaptation_history:
            self.adaptation_history[user_id] = []
        
        self.adaptation_history[user_id].append({
            'timestamp': datetime.utcnow().isoformat(),
            'signals': [{'type': s.signal_type, 'value': s.value} for s in signals],
            'actions': [a.to_dict() for a in actions]
        })
        
        return actions
    
    def _create_action(
        self,
        signal: LearningSignal,
        action_spec: Dict
    ) -> Optional[AdaptationAction]:
        """创建调整动作"""
        action_type = action_spec['type']
        
        action_map = {
            'difficulty_decrease': lambda: AdaptationAction(
                action_type='adjust_difficulty',
                target=signal.concept_id,
                parameters={'adjustment': -action_spec['amount']},
                reason=f"检测到{signal.signal_type}",
                expected_outcome="降低难度，提高成功率"
            ),
            'difficulty_increase': lambda: AdaptationAction(
                action_type='adjust_difficulty',
                target=signal.concept_id,
                parameters={'adjustment': action_spec['amount']},
                reason=f"检测到{signal.signal_type}",
                expected_outcome="增加挑战，保持学习动力"
            ),
            'add_prerequisite_review': lambda: AdaptationAction(
                action_type='insert_review',
                target='path',
                parameters={'concept_count': action_spec['count']},
                reason="表现下降，需要巩固基础",
                expected_outcome="强化前置知识"
            ),
            'content_type_change': lambda: AdaptationAction(
                action_type='change_content_type',
                target=signal.concept_id,
                parameters={'preference': action_spec['preference']},
                reason="参与度下降",
                expected_outcome="提高学习兴趣"
            ),
            'break_suggestion': lambda: AdaptationAction(
                action_type='suggest_break',
                target='session',
                parameters={'duration': action_spec['duration']},
                reason="学习疲劳",
                expected_outcome="恢复注意力"
            ),
            'content_chunking': lambda: AdaptationAction(
                action_type='adjust_chunk_size',
                target='content',
                parameters={'size': action_spec['size']},
                reason="学习时间过长",
                expected_outcome="降低认知负荷"
            ),
            'approach_change': lambda: AdaptationAction(
                action_type='change_learning_approach',
                target=signal.concept_id,
                parameters={'method': action_spec['method']},
                reason="学习停滞",
                expected_outcome="打破思维定势"
            )
        }
        
        creator = action_map.get(action_type)
        return creator() if creator else None


class DynamicRecommender:
    """
    动态推荐器
    整合信号检测和策略调整
    """
    
    def __init__(
        self,
        knowledge_graph: Any,
        path_planner: Any,
        base_recommender: Any
    ):
        self.knowledge_graph = knowledge_graph
        self.path_planner = path_planner
        self.base_recommender = base_recommender
        
        self.signal_detector = SignalDetector()
        self.strategy_adapter = StrategyAdapter()
        
        # 当前会话状态
        self.session_states: Dict[str, Dict] = {}
    
    def process_interaction(
        self,
        user_id: str,
        interaction: Dict[str, Any]
    ) -> Dict[str, Any]:
        """
        处理学习交互并返回调整建议
        
        Returns:
            {
                'recommendations': List[Dict],
                'adaptations': List[AdaptationAction],
                'signals': List[LearningSignal],
                'next_action': str
            }
        """
        # 检测信号
        signals = self.signal_detector.detect_signals(user_id, interaction)
        
        # 生成调整
        adaptations = []
        if signals:
            adaptations = self.strategy_adapter.generate_adaptations(user_id, signals)
        
        # 应用调整并生成新推荐
        recommendations = self._generate_adapted_recommendations(
            user_id, interaction, adaptations
        )
        
        # 决定下一步行动
        next_action = self._determine_next_action(signals, adaptations)
        
        # 更新会话状态
        self._update_session_state(user_id, interaction, signals, adaptations)
        
        return {
            'recommendations': recommendations,
            'adaptations': [a.to_dict() for a in adaptations],
            'signals': [
                {
                    'type': s.signal_type,
                    'concept_id': s.concept_id,
                    'value': s.value
                } for s in signals
            ],
            'next_action': next_action
        }
    
    def _generate_adapted_recommendations(
        self,
        user_id: str,
        interaction: Dict,
        adaptations: List[AdaptationAction]
    ) -> List[Dict]:
        """生成调整后的推荐"""
        # 获取基础推荐
        base_recs = self.base_recommender.get_recommendations(user_id)
        
        # 应用调整
        adapted_recs = base_recs.get('next_steps', []).copy()
        
        for adaptation in adaptations:
            if adaptation.action_type == 'adjust_difficulty':
                # 调整难度
                adjustment = adaptation.parameters.get('adjustment', 0)
                for rec in adapted_recs:
                    if 'difficulty' in rec:
                        rec['difficulty'] = max(0.1, min(1.0, rec['difficulty'] + adjustment))
            
            elif adaptation.action_type == 'insert_review':
                # 插入复习
                concept_id = interaction.get('concept_id')
                prereqs = self.knowledge_graph.graph.get_prerequisites(concept_id)
                if prereqs:
                    adapted_recs.insert(0, {
                        'type': 'review',
                        'concept_id': prereqs[0],
                        'reason': '巩固前置知识',
                        'priority': 1.0
                    })
            
            elif adaptation.action_type == 'change_content_type':
                # 改变内容类型
                preference = adaptation.parameters.get('preference', 'interactive')
                for rec in adapted_recs:
                    if 'content_types' in rec:
                        # 将偏好类型移到前面
                        rec['content_types'].insert(0, preference)
            
            elif adaptation.action_type == 'suggest_break':
                # 建议休息
                adapted_recs = [{
                    'type': 'break',
                    'duration': adaptation.parameters.get('duration', 10),
                    'reason': '建议休息以保持学习效率',
                    'priority': 1.0
                }]
        
        return adapted_recs
    
    def _determine_next_action(
        self,
        signals: List[LearningSignal],
        adaptations: List[AdaptationAction]
    ) -> str:
        """决定下一步行动"""
        if not signals:
            return "continue"
        
        # 检查是否有休息建议
        for adaptation in adaptations:
            if adaptation.action_type == 'suggest_break':
                return "take_break"
        
        # 检查是否需要调整
        for signal in signals:
            if signal.signal_type == AdaptationTrigger.PERFORMANCE_DROP.value:
                return "review_prerequisites"
            elif signal.signal_type == AdaptationTrigger.RAPID_PROGRESS.value:
                return "advance_faster"
        
        return "adjust_difficulty"
    
    def _update_session_state(
        self,
        user_id: str,
        interaction: Dict,
        signals: List[LearningSignal],
        adaptations: List[AdaptationAction]
    ):
        """更新会话状态"""
        if user_id not in self.session_states:
            self.session_states[user_id] = {
                'start_time': datetime.utcnow(),
                'interactions': [],
                'adaptations_applied': [],
                'signals_detected': []
            }
        
        state = self.session_states[user_id]
        state['interactions'].append({
            'timestamp': datetime.utcnow().isoformat(),
            'concept_id': interaction.get('concept_id'),
            'performance': interaction.get('performance')
        })
        state['signals_detected'].extend([s.signal_type for s in signals])
        state['adaptations_applied'].extend([a.action_type for a in adaptations])
    
    def get_session_summary(self, user_id: str) -> Dict:
        """获取会话摘要"""
        state = self.session_states.get(user_id, {})
        
        if not state:
            return {'message': '没有活跃会话'}
        
        interactions = state.get('interactions', [])
        
        return {
            'session_duration': (
                datetime.utcnow() - state.get('start_time', datetime.utcnow())
            ).total_seconds() / 60,  # 分钟
            'total_interactions': len(interactions),
            'adaptations_applied': len(state.get('adaptations_applied', [])),
            'signals_detected': len(state.get('signals_detected', [])),
            'average_performance': np.mean([
                i.get('performance', 0) for i in interactions if 'performance' in i
            ]) if interactions else 0
        }
    
    def reset_session(self, user_id: str):
        """重置会话"""
        if user_id in self.session_states:
            del self.session_states[user_id]
        self.signal_detector.signal_history.pop(user_id, None)


class DifficultyAdjuster:
    """难度调整器"""
    
    def __init__(self):
        self.difficulty_history: Dict[str, List[float]] = {}
        self.adjustment_factors: Dict[str, float] = {}
    
    def adjust_difficulty(
        self,
        user_id: str,
        concept_id: str,
        base_difficulty: float,
        performance_history: List[float]
    ) -> float:
        """
        动态调整难度
        
        Args:
            user_id: 用户ID
            concept_id: 概念ID
            base_difficulty: 基础难度
            performance_history: 历史表现
        
        Returns:
            调整后的难度
        """
        if len(performance_history) < 3:
            return base_difficulty
        
        # 计算趋势
        recent = np.mean(performance_history[-3:])
        older = np.mean(performance_history[:-3]) if len(performance_history) > 3 else recent
        
        trend = recent - older
        
        # 调整因子
        key = f"{user_id}_{concept_id}"
        current_factor = self.adjustment_factors.get(key, 1.0)
        
        if trend > 0.2:  # 进步明显
            new_factor = min(1.3, current_factor * 1.05)
        elif trend < -0.2:  # 退步明显
            new_factor = max(0.7, current_factor * 0.95)
        else:
            new_factor = current_factor
        
        self.adjustment_factors[key] = new_factor
        
        # 应用调整
        adjusted = base_difficulty * new_factor
        return max(0.1, min(1.0, adjusted))
    
    def get_adjustment_factor(self, user_id: str, concept_id: str) -> float:
        """获取调整因子"""
        key = f"{user_id}_{concept_id}"
        return self.adjustment_factors.get(key, 1.0)
