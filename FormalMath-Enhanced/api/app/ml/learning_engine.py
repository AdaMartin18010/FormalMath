"""
个性化学习引擎2.0
整合所有组件的统一接口
"""
import numpy as np
from typing import Dict, List, Optional, Tuple, Any, Set
from dataclasses import dataclass, field
from datetime import datetime, timedelta

# 导入各模块
from .dnc_knowledge_tracing import DNCKnowledgeTracer, MultiHeadKnowledgeTracer
from .forgetting_curve import ForgettingCurveModel, SpacedRepetitionScheduler
from .individual_differences import IndividualDifferenceModel, LearningStyleProfile

# 导入优化模块
from .knowledge_graph_embedding import KnowledgeGraphEmbedder
from .path_planner import AStarPathPlanner, AdaptivePathPlanner, PathOptimizationGoal
from .goal_based_recommender import GoalBasedRecommender, GoalType
from .dynamic_adapter import DynamicRecommender, DifficultyAdjuster
from .path_evaluator import PathEvaluator, PathMetrics


@dataclass
class LearningSession:
    """学习会话"""
    user_id: str
    session_id: str
    concept_id: Optional[str] = None
    content_items: List[Dict] = field(default_factory=list)
    start_time: datetime = field(default_factory=datetime.utcnow)
    end_time: Optional[datetime] = None
    performance_summary: Dict = field(default_factory=dict)


@dataclass
class LearningRecommendation:
    """学习推荐"""
    user_id: str
    recommendations: List[Dict]
    rationale: str
    confidence: float
    generated_at: datetime = field(default_factory=datetime.utcnow)


class PersonalizedLearningEngine:
    """
    个性化学习引擎2.0
    
    整合认知模型、推荐系统和游戏化功能
    """
    
    def __init__(self):
        # 认知模型
        self.knowledge_tracer = MultiHeadKnowledgeTracer(num_heads=3)
        self.forgetting_model = ForgettingCurveModel()
        self.spaced_repetition = SpacedRepetitionScheduler(self.forgetting_model)
        self.individual_model = IndividualDifferenceModel()
        
        # 知识图谱与路径规划
        self.knowledge_graph = KnowledgeGraphEmbedder(embedding_dim=64)
        self.path_planner = AStarPathPlanner(self.knowledge_graph)
        self.adaptive_planner = AdaptivePathPlanner(self.path_planner)
        
        # 目标导向推荐
        self.goal_recommender = GoalBasedRecommender(
            self.knowledge_graph, 
            self.path_planner
        )
        
        # 动态调整
        self.dynamic_recommender: Optional[DynamicRecommender] = None
        self.difficulty_adjuster = DifficultyAdjuster()
        
        # 路径评估
        self.path_evaluator = PathEvaluator(self.knowledge_graph)
        
        # 学习历史
        self.session_history: Dict[str, List[LearningSession]] = {}
        self.user_states: Dict[str, Dict] = {}
        self.active_paths: Dict[str, Any] = {}
    
    def initialize_user(
        self,
        user_id: str,
        initial_assessment: Optional[Dict] = None
    ) -> Dict[str, Any]:
        """
        初始化用户
        
        Args:
            user_id: 用户ID
            initial_assessment: 初始评估数据
        
        Returns:
            初始化结果
        """
        # 初始化个体差异模型
        self.individual_model.initialize_user(user_id, initial_assessment)
        
        # 创建用户状态
        self.user_states[user_id] = {
            'initialized_at': datetime.utcnow().isoformat(),
            'learning_style': None,
            'current_level': 0.5,
            'total_study_time': 0,
            'sessions_completed': 0
        }
        
        # 如果有初始评估，应用到各模型
        if initial_assessment:
            if 'knowledge_levels' in initial_assessment:
                for concept_id, level in initial_assessment['knowledge_levels'].items():
                    self.knowledge_tracer.tracers[0].knowledge_states[concept_id] = (
                        self._create_knowledge_state(concept_id, level)
                    )
        
        return {
            'user_id': user_id,
            'status': 'initialized',
            'next_steps': [
                '完成初始学习风格评估',
                '开始第一个学习会话',
                '设定学习目标'
            ]
        }
    
    def _create_knowledge_state(self, concept_id: str, level: float):
        """创建知识状态对象"""
        from .dnc_knowledge_tracing import KnowledgeState
        return KnowledgeState(
            concept_id=concept_id,
            mastery_level=level,
            confidence=0.5,
            last_updated=datetime.utcnow()
        )
    
    def process_learning_interaction(
        self,
        user_id: str,
        concept_id: str,
        interaction_type: str,
        result: Dict[str, Any],
        context: Optional[Dict] = None
    ) -> Dict[str, Any]:
        """
        处理学习交互
        
        Args:
            user_id: 用户ID
            concept_id: 概念ID
            interaction_type: 交互类型
            result: 结果数据
            context: 上下文
        
        Returns:
            处理结果
        """
        # 更新知识追踪
        interaction_data = {
            'type': interaction_type,
            'result': result.get('correctness', 'incorrect'),
            'duration': result.get('time_spent', 0),
            'difficulty': result.get('difficulty', 0.5),
            'timestamp': datetime.utcnow()
        }
        
        knowledge_states = self.knowledge_tracer.update(
            concept_id=concept_id,
            interaction_data=interaction_data
        )
        
        # 更新遗忘模型
        performance = 1.0 if result.get('correctness') == 'correct' else 0.5 if result.get('correctness') == 'partial' else 0.0
        self.forgetting_model.review_concept(
            concept_id=concept_id,
            performance=performance,
            review_duration=result.get('time_spent', 0)
        )
        
        # 更新个体差异模型
        self.individual_model.record_interaction(
            user_id=user_id,
            interaction_type=interaction_type,
            concept_id=concept_id,
            result=result,
            context=context
        )
        
        # 更新用户状态
        if user_id in self.user_states:
            self.user_states[user_id]['total_study_time'] += result.get('time_spent', 0)
        
        # 生成反馈
        feedback = self._generate_feedback(
            user_id, concept_id, result, knowledge_states
        )
        
        return {
            'user_id': user_id,
            'concept_id': concept_id,
            'knowledge_updated': True,
            'current_mastery': knowledge_states[0].mastery_level if knowledge_states else 0,
            'feedback': feedback,
            'next_recommendations': self.get_next_steps(user_id, concept_id)
        }
    
    def _generate_feedback(
        self,
        user_id: str,
        concept_id: str,
        result: Dict,
        knowledge_states: List
    ) -> Dict[str, Any]:
        """生成学习反馈"""
        feedback = {
            'performance': result.get('correctness'),
            'messages': []
        }
        
        correctness = result.get('correctness')
        
        if correctness == 'correct':
            feedback['messages'].append('回答正确！继续保持。')
            
            # 检查掌握程度
            if knowledge_states and knowledge_states[0].mastery_level >= 0.8:
                feedback['messages'].append('您已熟练掌握这个概念！')
        
        elif correctness == 'partial':
            feedback['messages'].append('部分正确，还有提升空间。')
            feedback['suggestion'] = '建议回顾相关基础概念'
        
        else:
            feedback['messages'].append('需要更多练习，不要气馁。')
            feedback['suggestion'] = '建议查看讲解视频或示例'
        
        return feedback
    
    def get_next_steps(
        self,
        user_id: str,
        current_concept: Optional[str] = None
    ) -> List[Dict]:
        """获取下一步建议"""
        suggestions = []
        
        # 基于知识追踪的建议
        if current_concept:
            # 获取相关概念
            related = self.knowledge_tracer.tracers[0].temporal_linkage.get_related_concepts(
                current_concept, threshold=0.3
            )
            
            for rel_id, strength in related[:3]:
                if rel_id in self.knowledge_tracer.tracers[0].knowledge_states:
                    state = self.knowledge_tracer.tracers[0].knowledge_states[rel_id]
                    if state.mastery_level < 0.7:
                        suggestions.append({
                            'type': 'concept',
                            'id': rel_id,
                            'reason': f'与当前概念相关（关联度: {strength:.2f}）',
                            'priority': 1 - state.mastery_level
                        })
        
        # 基于遗忘曲线的复习建议
        critical = self.forgetting_model.get_critical_concepts(threshold=0.4)
        for concept_id, retention in critical[:3]:
            suggestions.append({
                'type': 'review',
                'id': concept_id,
                'reason': f'记忆保持率较低（{retention:.0%}），建议复习',
                'priority': 1 - retention
            })
        
        # 排序
        suggestions.sort(key=lambda x: x['priority'], reverse=True)
        
        return suggestions[:5]
    
    def generate_learning_path(
        self,
        user_id: str,
        target_concepts: List[str],
        constraints: Optional[Dict] = None
    ) -> Dict[str, Any]:
        """
        生成个性化学习路径
        
        Args:
            user_id: 用户ID
            target_concepts: 目标概念
            constraints: 约束条件
        
        Returns:
            学习路径
        """
        # 获取学习风格适配
        if user_id in self.individual_model.learning_styles:
            style = self.individual_model.learning_styles[user_id]
            style_adaptation = style.get_dominant_style()
        else:
            style_adaptation = {}
        
        # 获取路径建议
        suggestions = self.knowledge_tracer.get_learning_path_suggestions(
            target_concepts=target_concepts
        )
        
        # 应用个体差异调整
        adapted_path = []
        for suggestion in suggestions:
            adapted = self._adapt_node_to_user(
                suggestion, user_id, style_adaptation
            )
            adapted_path.append(adapted)
        
        return {
            'user_id': user_id,
            'target_concepts': target_concepts,
            'path_nodes': adapted_path,
            'estimated_duration': sum(n.get('estimated_time', 30) for n in adapted_path),
            'style_adaptation': style_adaptation
        }
    
    def _adapt_node_to_user(
        self,
        node: Dict,
        user_id: str,
        style_adaptation: Dict
    ) -> Dict:
        """根据用户特点调整节点"""
        adapted = node.copy()
        
        # 根据学习风格调整
        if style_adaptation.get('visual_verbal') == 'visual':
            adapted['recommended_content_types'] = ['video', 'diagram', 'animation']
        elif style_adaptation.get('visual_verbal') == 'verbal':
            adapted['recommended_content_types'] = ['text', 'reading']
        
        if style_adaptation.get('active_reflective') == 'active':
            adapted['include_exercises'] = True
            adapted['exercise_ratio'] = 0.6
        
        # 根据知识水平调整难度
        concept_id = node.get('concept_id')
        if concept_id in self.knowledge_tracer.tracers[0].knowledge_states:
            mastery = self.knowledge_tracer.tracers[0].knowledge_states[concept_id].mastery_level
            if mastery > 0.6:
                adapted['skip_prerequisites'] = True
                adapted['include_advanced'] = True
        
        return adapted
    
    def get_spaced_repetition_schedule(
        self,
        user_id: str,
        days_ahead: int = 7
    ) -> List[Dict]:
        """
        获取间隔重复复习计划
        
        Args:
            user_id: 用户ID
            days_ahead: 计划天数
        
        Returns:
            复习计划
        """
        schedule = self.spaced_repetition.generate_schedule(
            days_ahead=days_ahead
        )
        
        return [s.to_dict() for s in schedule]
    
    def get_user_analytics(self, user_id: str) -> Dict[str, Any]:
        """
        获取用户学习分析
        
        Returns:
            学习分析报告
        """
        # 知识状态摘要
        knowledge_summary = self.knowledge_tracer.tracers[0].get_knowledge_state_summary()
        
        # 遗忘曲线统计
        forgetting_stats = self.forgetting_model.get_learning_statistics()
        
        # 个体差异档案
        individual_profile = self.individual_model.get_user_profile_summary(user_id)
        
        # 学习状态
        user_state = self.user_states.get(user_id, {})
        
        return {
            'user_id': user_id,
            'knowledge_summary': knowledge_summary,
            'retention_stats': forgetting_stats,
            'individual_profile': individual_profile,
            'learning_stats': {
                'total_study_time': user_state.get('total_study_time', 0),
                'sessions_completed': user_state.get('sessions_completed', 0),
                'initialization_date': user_state.get('initialized_at')
            },
            'generated_at': datetime.utcnow().isoformat()
        }
    
    def predict_performance(
        self,
        user_id: str,
        concept_id: str,
        difficulty: float = 0.5
    ) -> Dict[str, Any]:
        """
        预测学习表现
        
        Args:
            user_id: 用户ID
            concept_id: 概念ID
            difficulty: 难度
        
        Returns:
            预测结果
        """
        # 获取集成预测
        ensemble = self.knowledge_tracer.get_ensemble_prediction(concept_id)
        
        # 考虑个体差异
        if user_id in self.individual_model.cognitive_profiles:
            cog_profile = self.individual_model.cognitive_profiles[user_id]
            ability_factor = np.mean(list(cog_profile.abilities.values()))
            
            # 调整预测
            adjusted_pred = ensemble['ensemble_prediction'] * 0.8 + ability_factor * 0.2
        else:
            adjusted_pred = ensemble['ensemble_prediction']
        
        return {
            'concept_id': concept_id,
            'predicted_performance': adjusted_pred,
            'confidence': 1 - ensemble['uncertainty'],
            'difficulty': difficulty,
            'estimated_time_to_master': self._estimate_time_to_master(
                concept_id, adjusted_pred
            )
        }
    
    def _estimate_time_to_master(
        self,
        concept_id: str,
        current_performance: float
    ) -> int:
        """估计掌握所需时间（分钟）"""
        # 基于当前表现和概念复杂度
        if current_performance >= 0.8:
            return 15  # 巩固
        elif current_performance >= 0.5:
            return 45  # 提升
        else:
            return 90  # 从头学习
    
    def export_user_model(self, user_id: str) -> Dict[str, Any]:
        """
        导出用户模型（用于持久化）
        
        Returns:
            用户模型数据
        """
        return {
            'user_id': user_id,
            'knowledge_tracer_state': self.knowledge_tracer.tracers[0].export_state(),
            'forgetting_model_state': {
                'memory_traces': {
                    cid: trace.to_dict()
                    for cid, trace in self.forgetting_model.memory_traces.items()
                },
                'user_adjustment_factor': self.forgetting_model.user_adjustment_factor
            },
            'individual_model_state': self.individual_model.export_user_model(user_id),
            'user_state': self.user_states.get(user_id, {}),
            'exported_at': datetime.utcnow().isoformat()
        }
    
    def import_user_model(self, user_id: str, data: Dict[str, Any]):
        """
        导入用户模型
        
        Args:
            user_id: 用户ID
            data: 模型数据
        """
        # 恢复知识追踪器
        if 'knowledge_tracer_state' in data:
            self.knowledge_tracer.tracers[0].import_state(data['knowledge_tracer_state'])
        
        # 恢复遗忘模型
        if 'forgetting_model_state' in data:
            fm_state = data['forgetting_model_state']
            self.forgetting_model.user_adjustment_factor = fm_state.get(
                'user_adjustment_factor', 1.0
            )
            # 恢复记忆痕迹
            for cid, trace_data in fm_state.get('memory_traces', {}).items():
                from .forgetting_curve import MemoryTrace
                self.forgetting_model.memory_traces[cid] = MemoryTrace(
                    concept_id=cid,
                    initial_strength=trace_data['initial_strength'],
                    current_strength=trace_data['current_strength'],
                    created_at=datetime.fromisoformat(trace_data['created_at']),
                    last_reviewed=datetime.fromisoformat(trace_data['last_reviewed']),
                    review_count=trace_data['review_count'],
                    forgetting_rate=trace_data['forgetting_rate']
                )
        
        # 恢复个体差异模型
        if 'individual_model_state' in data:
            self.individual_model.import_user_model(user_id, data['individual_model_state'])
        
        # 恢复用户状态
        if 'user_state' in data:
            self.user_states[user_id] = data['user_state']
    
    # ========== 新增优化方法 ==========
    
    def add_concept_to_graph(self, concept_data: Dict[str, Any]):
        """添加概念到知识图谱"""
        self.knowledge_graph.add_concept(concept_data)
    
    def add_relation_to_graph(self, relation_data: Dict[str, Any]):
        """添加关系到知识图谱"""
        self.knowledge_graph.add_relation(relation_data)
    
    def build_knowledge_embeddings(self, epochs: int = 100):
        """构建知识嵌入"""
        self.knowledge_graph.fit_embeddings(epochs=epochs)
    
    def create_learning_goal(
        self,
        user_id: str,
        goal_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """
        创建学习目标
        
        Args:
            user_id: 用户ID
            goal_data: 目标数据
                {
                    'title': str,
                    'description': str,
                    'goal_type': str,
                    'target_concepts': List[str],
                    'target_mastery': float,
                    'deadline': str (ISO format),
                    'priority': int,
                    'max_daily_time': int
                }
        
        Returns:
            创建的目标信息
        """
        goal = self.goal_recommender.create_goal(user_id, goal_data)
        
        # 分析目标可行性
        user_profile = self._build_user_profile(user_id)
        analysis = self.goal_recommender.goal_analyzer.analyze_goal(goal, user_profile)
        
        return {
            'goal': goal.to_dict(),
            'analysis': analysis
        }
    
    def _build_user_profile(self, user_id: str) -> Dict[str, Any]:
        """构建用户画像"""
        # 获取已知概念
        known_concepts = set()
        if user_id in self.user_states:
            known_concepts = set(self.user_states[user_id].get('known_concepts', []))
        
        # 从知识追踪器获取
        for tracer in self.knowledge_tracer.tracers:
            for cid, state in tracer.knowledge_states.items():
                if state.mastery_level >= 0.6:
                    known_concepts.add(cid)
        
        # 获取能力水平
        current_level = 0.5
        if user_id in self.user_states:
            current_level = self.user_states[user_id].get('current_level', 0.5)
        
        return {
            'user_id': user_id,
            'known_concepts': list(known_concepts),
            'current_level': current_level,
            'daily_available_time': 60
        }
    
    def get_goal_based_recommendations(
        self,
        user_id: str,
        goal_id: Optional[str] = None,
        context: Optional[Dict] = None
    ) -> Dict[str, Any]:
        """
        获取基于目标的推荐
        
        Args:
            user_id: 用户ID
            goal_id: 目标ID（可选）
            context: 当前上下文
        
        Returns:
            推荐结果
        """
        # 构建上下文
        if context is None:
            context = self._build_learning_context(user_id)
        
        return self.goal_recommender.get_recommendations(
            user_id=user_id,
            goal_id=goal_id,
            current_context=context
        )
    
    def _build_learning_context(self, user_id: str) -> Dict[str, Any]:
        """构建学习上下文"""
        # 获取最近完成的
        completed = []
        mastery = {}
        
        for tracer in self.knowledge_tracer.tracers:
            for cid, state in tracer.knowledge_states.items():
                if state.mastery_level >= 0.8:
                    completed.append(cid)
                mastery[cid] = state.mastery_level
        
        # 获取总学习时间
        total_time = 0
        if user_id in self.user_states:
            total_time = self.user_states[user_id].get('total_study_time', 0)
        
        return {
            'completed_concepts': completed,
            'concept_mastery': mastery,
            'session_time': total_time
        }
    
    def generate_optimized_learning_path(
        self,
        user_id: str,
        target_concepts: List[str],
        goal: PathOptimizationGoal = PathOptimizationGoal.BALANCED,
        constraints: Optional[Dict] = None
    ) -> Dict[str, Any]:
        """
        生成优化的学习路径
        
        Args:
            user_id: 用户ID
            target_concepts: 目标概念
            goal: 优化目标
            constraints: 约束条件
        
        Returns:
            学习路径
        """
        # 获取已知概念
        user_profile = self._build_user_profile(user_id)
        known_concepts = set(user_profile.get('known_concepts', []))
        
        # 生成路径
        path = self.path_planner.plan_path(
            user_id=user_id,
            start_concepts=known_concepts,
            target_concepts=set(target_concepts),
            goal=goal,
            constraints=constraints
        )
        
        if path is None:
            return {'error': '无法生成路径'}
        
        # 应用个体差异调整
        if user_id in self.individual_model.learning_styles:
            style = self.individual_model.learning_styles[user_id]
            adapted_nodes = self.individual_model.get_learning_path_adaptation(
                user_id, [n.to_dict() for n in path.nodes]
            )
            path.nodes = adapted_nodes
        
        # 保存活跃路径
        self.active_paths[user_id] = path
        
        return path.to_dict()
    
    def adapt_learning_path(
        self,
        user_id: str,
        progress_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """
        根据进度调整学习路径
        
        Args:
            user_id: 用户ID
            progress_data: 进度数据
        
        Returns:
            调整后的路径
        """
        if user_id not in self.active_paths:
            return {'error': '没有活跃的学习路径'}
        
        current_path = self.active_paths[user_id]
        
        # 调整路径
        adapted_path = self.adaptive_planner.adapt_path(current_path, progress_data)
        
        # 更新活跃路径
        self.active_paths[user_id] = adapted_path
        
        return adapted_path.to_dict()
    
    def process_learning_interaction_with_adaptation(
        self,
        user_id: str,
        interaction: Dict[str, Any]
    ) -> Dict[str, Any]:
        """
        处理学习交互并进行动态调整
        
        Args:
            user_id: 用户ID
            interaction: 交互数据
        
        Returns:
            处理结果和调整建议
        """
        # 初始化动态推荐器
        if self.dynamic_recommender is None:
            self.dynamic_recommender = DynamicRecommender(
                self.knowledge_graph,
                self.path_planner,
                self.goal_recommender
            )
        
        # 处理交互
        result = self.dynamic_recommender.process_interaction(user_id, interaction)
        
        # 动态调整难度
        concept_id = interaction.get('concept_id')
        if concept_id:
            performance_history = self._get_performance_history(user_id, concept_id)
            adjusted_difficulty = self.difficulty_adjuster.adjust_difficulty(
                user_id, concept_id,
                base_difficulty=interaction.get('difficulty', 0.5),
                performance_history=performance_history
            )
            result['adjusted_difficulty'] = adjusted_difficulty
        
        return result
    
    def _get_performance_history(self, user_id: str, concept_id: str) -> List[float]:
        """获取历史表现"""
        history = []
        
        # 从知识追踪器获取
        for tracer in self.knowledge_tracer.tracers:
            if concept_id in tracer.knowledge_states:
                state = tracer.knowledge_states[concept_id]
                for interaction in state.interaction_history:
                    result = interaction.get('result', 'incorrect')
                    if result == 'correct':
                        history.append(1.0)
                    elif result == 'partial':
                        history.append(0.5)
                    else:
                        history.append(0.0)
        
        return history
    
    def evaluate_learning_path(
        self,
        user_id: str,
        execution_data: Dict[str, Any]
    ) -> Dict[str, Any]:
        """
        评估学习路径效果
        
        Args:
            user_id: 用户ID
            execution_data: 执行数据
        
        Returns:
            评估指标
        """
        if user_id not in self.active_paths:
            return {'error': '没有活跃的学习路径'}
        
        path = self.active_paths[user_id]
        
        # 评估
        metrics = self.path_evaluator.evaluate_path(path, execution_data)
        
        return metrics.to_dict()
    
    def get_path_analytics(self, user_id: str) -> Dict[str, Any]:
        """
        获取路径分析
        
        Args:
            user_id: 用户ID
        
        Returns:
            路径分析数据
        """
        if user_id not in self.active_paths:
            return {'error': '没有活跃的学习路径'}
        
        path = self.active_paths[user_id]
        
        return {
            'path_id': path.path_id,
            'target_concepts': path.target_concepts,
            'total_nodes': len(path.nodes),
            'total_time': path.total_time,
            'total_difficulty': path.total_difficulty,
            'expected_mastery': path.expected_mastery,
            'optimization_goal': path.optimization_goal.value,
            'remaining_nodes': [
                n.concept_id for n in path.nodes
                if n.concept_id not in self._get_completed_concepts(user_id)
            ]
        }
    
    def _get_completed_concepts(self, user_id: str) -> Set[str]:
        """获取已完成的概念"""
        completed = set()
        
        for tracer in self.knowledge_tracer.tracers:
            for cid, state in tracer.knowledge_states.items():
                if state.mastery_level >= 0.8:
                    completed.add(cid)
        
        return completed


# 全局引擎实例
_learning_engine: Optional[PersonalizedLearningEngine] = None


def get_learning_engine() -> PersonalizedLearningEngine:
    """获取学习引擎实例（单例模式）"""
    global _learning_engine
    if _learning_engine is None:
        _learning_engine = PersonalizedLearningEngine()
    return _learning_engine
