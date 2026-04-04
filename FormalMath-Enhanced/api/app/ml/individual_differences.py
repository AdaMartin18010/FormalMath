"""
个体差异建模
学习风格、认知能力、个性特征建模
"""
import numpy as np
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, field
from datetime import datetime
from enum import Enum
import json


class LearningStyleDimension(str, Enum):
    """学习风格维度"""
    VISUAL_VERBAL = "visual_verbal"      # 视觉-言语
    SEQUENTIAL_GLOBAL = "sequential_global"  # 序列-整体
    ACTIVE_REFLECTIVE = "active_reflective"  # 主动-反思
    SENSING_INTUITIVE = "sensing_intuitive"  # 感知-直觉


class CognitiveAbility(str, Enum):
    """认知能力类型"""
    WORKING_MEMORY = "working_memory"
    PROCESSING_SPEED = "processing_speed"
    LOGICAL_REASONING = "logical_reasoning"
    SPATIAL_REASONING = "spatial_reasoning"
    VERBAL_COMPREHENSION = "verbal_comprehension"


@dataclass
class LearningStyleProfile:
    """学习风格档案"""
    user_id: str
    
    # 各维度得分 -1到1，0为平衡
    visual_verbal: float = 0.0
    sequential_global: float = 0.0
    active_reflective: float = 0.0
    sensing_intuitive: float = 0.0
    
    # 置信度
    confidence: Dict[str, float] = field(default_factory=dict)
    
    # 历史更新记录
    update_history: List[Dict] = field(default_factory=list)
    
    def get_dominant_style(self) -> Dict[str, str]:
        """获取主导学习风格"""
        styles = {}
        
        dimensions = {
            'visual_verbal': ('visual', 'verbal'),
            'sequential_global': ('sequential', 'global'),
            'active_reflective': ('active', 'reflective'),
            'sensing_intuitive': ('sensing', 'intuitive')
        }
        
        for dim, (pos, neg) in dimensions.items():
            value = getattr(self, dim)
            if value > 0.3:
                styles[dim] = pos
            elif value < -0.3:
                styles[dim] = neg
            else:
                styles[dim] = 'balanced'
        
        return styles
    
    def to_vector(self) -> np.ndarray:
        """转换为向量表示"""
        return np.array([
            self.visual_verbal,
            self.sequential_global,
            self.active_reflective,
            self.sensing_intuitive
        ])
    
    def to_dict(self) -> Dict:
        return {
            'user_id': self.user_id,
            'visual_verbal': self.visual_verbal,
            'sequential_global': self.sequential_global,
            'active_reflective': self.active_reflective,
            'sensing_intuitive': self.sensing_intuitive,
            'dominant_style': self.get_dominant_style(),
            'confidence': self.confidence
        }


@dataclass
class CognitiveProfile:
    """认知能力档案"""
    user_id: str
    
    # 各认知能力得分 0-1
    abilities: Dict[str, float] = field(default_factory=dict)
    
    # 评估历史
    assessment_history: List[Dict] = field(default_factory=list)
    
    def get_strengths(self, top_n: int = 3) -> List[Tuple[str, float]]:
        """获取认知优势"""
        sorted_abilities = sorted(
            self.abilities.items(),
            key=lambda x: x[1],
            reverse=True
        )
        return sorted_abilities[:top_n]
    
    def get_weaknesses(self, top_n: int = 3) -> List[Tuple[str, float]]:
        """获取认知劣势"""
        sorted_abilities = sorted(
            self.abilities.items(),
            key=lambda x: x[1]
        )
        return sorted_abilities[:top_n]
    
    def to_dict(self) -> Dict:
        return {
            'user_id': self.user_id,
            'abilities': self.abilities,
            'strengths': self.get_strengths(),
            'weaknesses': self.get_weaknesses()
        }


@dataclass
class PersonalityTraits:
    """个性特征（基于大五人格模型）"""
    user_id: str
    
    # 开放性
    openness: float = 0.5
    # 尽责性
    conscientiousness: float = 0.5
    # 外向性
    extraversion: float = 0.5
    # 宜人性
    agreeableness: float = 0.5
    # 神经质
    neuroticism: float = 0.5
    
    def to_dict(self) -> Dict:
        return {
            'user_id': self.user_id,
            'openness': self.openness,
            'conscientiousness': self.conscientiousness,
            'extraversion': self.extraversion,
            'agreeableness': self.agreeableness,
            'neuroticism': self.neuroticism
        }


class IndividualDifferenceModel:
    """
    个体差异模型
    
    整合学习风格、认知能力和个性特征，
    为个性化学习提供基础
    """
    
    def __init__(self):
        # 用户档案存储
        self.learning_styles: Dict[str, LearningStyleProfile] = {}
        self.cognitive_profiles: Dict[str, CognitiveProfile] = {}
        self.personality_traits: Dict[str, PersonalityTraits] = {}
        
        # 交互历史
        self.interaction_history: Dict[str, List[Dict]] = {}
        
        # 学习行为模式
        self.behavior_patterns: Dict[str, Dict] = {}
    
    def initialize_user(self, user_id: str, initial_assessment: Optional[Dict] = None):
        """
        初始化用户档案
        
        Args:
            user_id: 用户ID
            initial_assessment: 初始评估数据
        """
        # 创建学习风格档案
        if user_id not in self.learning_styles:
            self.learning_styles[user_id] = LearningStyleProfile(
                user_id=user_id,
                confidence={dim.value: 0.0 for dim in LearningStyleDimension}
            )
        
        # 创建认知档案
        if user_id not in self.cognitive_profiles:
            self.cognitive_profiles[user_id] = CognitiveProfile(
                user_id=user_id,
                abilities={ability.value: 0.5 for ability in CognitiveAbility}
            )
        
        # 创建个性档案
        if user_id not in self.personality_traits:
            self.personality_traits[user_id] = PersonalityTraits(user_id=user_id)
        
        # 初始化历史
        if user_id not in self.interaction_history:
            self.interaction_history[user_id] = []
        
        # 应用初始评估
        if initial_assessment:
            self._apply_initial_assessment(user_id, initial_assessment)
    
    def _apply_initial_assessment(self, user_id: str, assessment: Dict):
        """应用初始评估数据"""
        # 学习风格评估
        if 'learning_style' in assessment:
            style_data = assessment['learning_style']
            profile = self.learning_styles[user_id]
            
            for dim in LearningStyleDimension:
                if dim.value in style_data:
                    setattr(profile, dim.value, style_data[dim.value])
                    profile.confidence[dim.value] = 0.6  # 初始置信度
        
        # 认知能力评估
        if 'cognitive_abilities' in assessment:
            cog_data = assessment['cognitive_abilities']
            profile = self.cognitive_profiles[user_id]
            
            for ability in CognitiveAbility:
                if ability.value in cog_data:
                    profile.abilities[ability.value] = cog_data[ability.value]
        
        # 个性特征
        if 'personality' in assessment:
            pers_data = assessment['personality']
            traits = self.personality_traits[user_id]
            
            for trait in ['openness', 'conscientiousness', 'extraversion', 
                         'agreeableness', 'neuroticism']:
                if trait in pers_data:
                    setattr(traits, trait, pers_data[trait])
    
    def record_interaction(
        self,
        user_id: str,
        interaction_type: str,
        concept_id: str,
        result: Dict[str, Any],
        context: Optional[Dict] = None
    ):
        """
        记录学习交互
        
        Args:
            user_id: 用户ID
            interaction_type: 交互类型
            concept_id: 概念ID
            result: 交互结果
            context: 上下文信息
        """
        if user_id not in self.interaction_history:
            self.initialize_user(user_id)
        
        interaction = {
            'timestamp': datetime.utcnow().isoformat(),
            'type': interaction_type,
            'concept_id': concept_id,
            'result': result,
            'context': context or {}
        }
        
        self.interaction_history[user_id].append(interaction)
        
        # 保持最近1000条记录
        if len(self.interaction_history[user_id]) > 1000:
            self.interaction_history[user_id] = self.interaction_history[user_id][-1000:]
        
        # 实时更新模型
        self._update_from_interaction(user_id, interaction)
    
    def _update_from_interaction(self, user_id: str, interaction: Dict):
        """从交互中更新模型"""
        interaction_type = interaction['type']
        result = interaction['result']
        context = interaction.get('context', {})
        
        # 根据交互类型更新不同模型
        if interaction_type == 'content_consumption':
            self._update_from_content_consumption(user_id, result, context)
        elif interaction_type == 'exercise_attempt':
            self._update_from_exercise(user_id, result, context)
        elif interaction_type == 'navigation_pattern':
            self._update_from_navigation(user_id, result, context)
    
    def _update_from_content_consumption(
        self,
        user_id: str,
        result: Dict,
        context: Dict
    ):
        """从内容消费更新学习风格"""
        profile = self.learning_styles[user_id]
        
        content_type = context.get('content_type', 'text')
        time_spent = result.get('time_spent', 0)
        completion_rate = result.get('completion_rate', 0)
        
        # 视觉-言语维度
        if content_type in ['video', 'diagram', 'animation']:
            # 对视觉内容表现好
            if completion_rate > 0.8 and time_spent < context.get('expected_time', time_spent * 2):
                # 增量更新（指数移动平均）
                alpha = 0.1
                profile.visual_verbal = alpha * 1.0 + (1 - alpha) * profile.visual_verbal
                profile.confidence['visual_verbal'] = min(
                    1.0, profile.confidence['visual_verbal'] + 0.05
                )
        elif content_type in ['text', 'audio']:
            if completion_rate > 0.8:
                alpha = 0.1
                profile.visual_verbal = alpha * (-1.0) + (1 - alpha) * profile.visual_verbal
                profile.confidence['visual_verbal'] = min(
                    1.0, profile.confidence['visual_verbal'] + 0.05
                )
        
        # 主动-反思维度
        interaction_level = context.get('interaction_level', 0)
        if interaction_level > 0.7:  # 高交互
            alpha = 0.05
            profile.active_reflective = alpha * 1.0 + (1 - alpha) * profile.active_reflective
        elif interaction_level < 0.3:  # 低交互，线性消费
            alpha = 0.05
            profile.active_reflective = alpha * (-1.0) + (1 - alpha) * profile.active_reflective
    
    def _update_from_exercise(
        self,
        user_id: str,
        result: Dict,
        context: Dict
    ):
        """从练习结果更新认知能力估计"""
        profile = self.cognitive_profiles[user_id]
        
        exercise_type = context.get('exercise_type', 'general')
        difficulty = context.get('difficulty', 0.5)
        performance = result.get('score', 0) / result.get('max_score', 1)
        time_spent = result.get('time_spent', 0)
        expected_time = context.get('expected_time', time_spent)
        
        # 根据练习类型更新不同认知能力
        ability_mapping = {
            'logical_puzzle': 'logical_reasoning',
            'calculation': 'processing_speed',
            'proof': 'logical_reasoning',
            'visualization': 'spatial_reasoning',
            'reading_comprehension': 'verbal_comprehension',
            'memory_task': 'working_memory'
        }
        
        ability = ability_mapping.get(exercise_type)
        if ability and ability in profile.abilities:
            # 基于表现和时间更新能力估计
            time_efficiency = min(1.0, expected_time / max(time_spent, 1))
            
            # 贝叶斯更新简化版
            current_estimate = profile.abilities[ability]
            observation = performance * 0.7 + time_efficiency * 0.3
            
            # 加权更新
            alpha = 0.15 * difficulty  # 难度越高，权重越大
            profile.abilities[ability] = alpha * observation + (1 - alpha) * current_estimate
    
    def _update_from_navigation(
        self,
        user_id: str,
        result: Dict,
        context: Dict
    ):
        """从导航模式更新学习风格"""
        profile = self.learning_styles[user_id]
        
        navigation_pattern = result.get('pattern', 'sequential')
        
        if navigation_pattern == 'jumping':
            # 跳跃式导航表明整体型学习风格
            alpha = 0.1
            profile.sequential_global = alpha * 1.0 + (1 - alpha) * profile.sequential_global
        elif navigation_pattern == 'sequential':
            alpha = 0.1
            profile.sequential_global = alpha * (-1.0) + (1 - alpha) * profile.sequential_global
    
    def get_content_recommendations(
        self,
        user_id: str,
        available_content: List[Dict],
        concept_id: Optional[str] = None
    ) -> List[Dict]:
        """
        基于学习风格推荐内容
        
        Args:
            user_id: 用户ID
            available_content: 可用内容列表
            concept_id: 可选概念过滤
        
        Returns:
            排序后的推荐列表
        """
        if user_id not in self.learning_styles:
            # 无个性化数据，返回默认排序
            return [{**c, 'personalization_score': 0.5} for c in available_content]
        
        profile = self.learning_styles[user_id]
        style = profile.get_dominant_style()
        
        scored_content = []
        for content in available_content:
            if concept_id and content.get('concept_id') != concept_id:
                continue
            
            score = self._calculate_content_match(content, style, profile)
            scored_content.append({
                **content,
                'personalization_score': score,
                'match_reason': self._get_match_reason(content, style)
            })
        
        # 按个性化分数排序
        scored_content.sort(key=lambda x: x['personalization_score'], reverse=True)
        
        return scored_content
    
    def _calculate_content_match(
        self,
        content: Dict,
        style: Dict[str, str],
        profile: LearningStyleProfile
    ) -> float:
        """计算内容与学习风格的匹配度"""
        scores = []
        
        content_type = content.get('type', 'text')
        presentation = content.get('presentation', 'linear')
        interactivity = content.get('interactivity', 0.5)
        
        # 视觉-言语匹配
        if style['visual_verbal'] == 'visual' and content_type in ['video', 'diagram', 'animation']:
            scores.append(1.0)
        elif style['visual_verbal'] == 'verbal' and content_type in ['text', 'audio']:
            scores.append(1.0)
        elif style['visual_verbal'] == 'balanced':
            scores.append(0.8)
        else:
            scores.append(0.5)
        
        # 序列-整体匹配
        if style['sequential_global'] == 'global' and presentation == 'overview':
            scores.append(1.0)
        elif style['sequential_global'] == 'sequential' and presentation == 'linear':
            scores.append(1.0)
        else:
            scores.append(0.6)
        
        # 主动-反思匹配
        if style['active_reflective'] == 'active' and interactivity > 0.6:
            scores.append(1.0)
        elif style['active_reflective'] == 'reflective' and interactivity < 0.4:
            scores.append(1.0)
        else:
            scores.append(0.7)
        
        return np.mean(scores) if scores else 0.5
    
    def _get_match_reason(self, content: Dict, style: Dict[str, str]) -> str:
        """获取匹配原因说明"""
        reasons = []
        
        content_type = content.get('type', 'text')
        
        if style['visual_verbal'] == 'visual' and content_type in ['video', 'diagram']:
            reasons.append('符合您的视觉学习偏好')
        elif style['visual_verbal'] == 'verbal' and content_type == 'text':
            reasons.append('符合您的阅读学习偏好')
        
        if style['active_reflective'] == 'active':
            reasons.append('包含互动练习')
        elif style['active_reflective'] == 'reflective':
            reasons.append('适合深度学习思考')
        
        return '；'.join(reasons) if reasons else '标准推荐'
    
    def get_learning_path_adaptation(
        self,
        user_id: str,
        base_path: List[Dict]
    ) -> List[Dict]:
        """
        根据个体差异调整学习路径
        
        Args:
            user_id: 用户ID
            base_path: 基础学习路径
        
        Returns:
            调整后的路径
        """
        if user_id not in self.learning_styles:
            return base_path
        
        profile = self.learning_styles[user_id]
        cog_profile = self.cognitive_profiles.get(user_id)
        
        adapted_path = []
        
        for node in base_path:
            adapted_node = node.copy()
            
            # 根据序列-整体维度调整内容组织
            if profile.sequential_global > 0.3:  # 整体型
                adapted_node['content_format'] = 'overview_first'
                adapted_node['include_summary'] = True
            else:  # 序列型
                adapted_node['content_format'] = 'step_by_step'
                adapted_node['include_prerequisites'] = True
            
            # 根据认知能力调整难度节奏
            if cog_profile:
                working_memory = cog_profile.abilities.get('working_memory', 0.5)
                if working_memory < 0.4:
                    adapted_node['chunk_size'] = 'small'
                    adapted_node['include_scaffolding'] = True
                elif working_memory > 0.7:
                    adapted_node['chunk_size'] = 'large'
                    adapted_node['include_extensions'] = True
            
            # 根据主动-反思维度调整练习比例
            if profile.active_reflective > 0.3:  # 主动型
                adapted_node['practice_ratio'] = 0.6
                adapted_node['include_collaboration'] = True
            else:  # 反思型
                adapted_node['practice_ratio'] = 0.4
                adapted_node['include_reflection_prompts'] = True
            
            adapted_path.append(adapted_node)
        
        return adapted_path
    
    def get_difficulty_adjustment(self, user_id: str, base_difficulty: float) -> float:
        """
        根据用户能力调整难度
        
        Args:
            user_id: 用户ID
            base_difficulty: 基础难度 0-1
        
        Returns:
            调整后的难度
        """
        if user_id not in self.cognitive_profiles:
            return base_difficulty
        
        profile = self.cognitive_profiles[user_id]
        
        # 计算综合认知能力
        avg_ability = np.mean(list(profile.abilities.values())) if profile.abilities else 0.5
        
        # 能力越高，适当增加难度
        ability_factor = (avg_ability - 0.5) * 0.2
        
        adjusted = base_difficulty + ability_factor
        
        # 考虑尽责性（更尽责的用户可以处理略高的难度）
        if user_id in self.personality_traits:
            conscientiousness = self.personality_traits[user_id].conscientiousness
            adjusted += (conscientiousness - 0.5) * 0.1
        
        return max(0.1, min(1.0, adjusted))
    
    def estimate_optimal_session_duration(self, user_id: str) -> int:
        """
        估计最佳学习会话时长（分钟）
        
        Args:
            user_id: 用户ID
        
        Returns:
            建议时长
        """
        base_duration = 25  # 默认25分钟（番茄工作法）
        
        if user_id in self.cognitive_profiles:
            # 基于工作记忆和处理速度调整
            wm = self.cognitive_profiles[user_id].abilities.get('working_memory', 0.5)
            ps = self.cognitive_profiles[user_id].abilities.get('processing_speed', 0.5)
            
            # 能力越高，可以持续更长时间
            ability_factor = (wm + ps) / 2
            base_duration = int(20 + ability_factor * 30)  # 20-50分钟范围
        
        if user_id in self.personality_traits:
            # 尽责性影响持续注意力
            con = self.personality_traits[user_id].conscientiousness
            base_duration = int(base_duration * (0.8 + con * 0.4))
        
        return max(15, min(60, base_duration))
    
    def get_user_profile_summary(self, user_id: str) -> Dict:
        """获取用户档案摘要"""
        summary = {
            'user_id': user_id,
            'learning_style': None,
            'cognitive_profile': None,
            'personality': None,
            'recommendations': []
        }
        
        if user_id in self.learning_styles:
            summary['learning_style'] = self.learning_styles[user_id].to_dict()
        
        if user_id in self.cognitive_profiles:
            summary['cognitive_profile'] = self.cognitive_profiles[user_id].to_dict()
        
        if user_id in self.personality_traits:
            summary['personality'] = self.personality_traits[user_id].to_dict()
        
        # 生成个性化建议
        summary['recommendations'] = self._generate_recommendations(user_id)
        
        return summary
    
    def _generate_recommendations(self, user_id: str) -> List[str]:
        """生成个性化学习建议"""
        recommendations = []
        
        # 基于学习风格
        if user_id in self.learning_styles:
            style = self.learning_styles[user_id].get_dominant_style()
            
            if style.get('visual_verbal') == 'visual':
                recommendations.append('建议多使用图表、视频等视觉材料')
            elif style.get('visual_verbal') == 'verbal':
                recommendations.append('建议多阅读文字材料和书面笔记')
            
            if style.get('active_reflective') == 'active':
                recommendations.append('尝试通过实践练习和小组讨论来学习')
            else:
                recommendations.append('留出时间进行独立思考和总结')
        
        # 基于认知能力
        if user_id in self.cognitive_profiles:
            weaknesses = self.cognitive_profiles[user_id].get_weaknesses(2)
            for ability, score in weaknesses:
                if score < 0.4:
                    recommendations.append(
                        f'您的{CognitiveAbility(ability).value}能力有提升空间，建议针对性练习'
                    )
        
        # 基于个性特征
        if user_id in self.personality_traits:
            traits = self.personality_traits[user_id]
            
            if traits.conscientiousness < 0.4:
                recommendations.append('建议使用学习计划工具保持学习规律')
            
            if traits.openness > 0.7:
                recommendations.append('您可以尝试探索更多拓展性内容')
        
        return recommendations
    
    def export_user_model(self, user_id: str) -> Dict:
        """导出用户模型用于持久化"""
        return {
            'user_id': user_id,
            'learning_style': self.learning_styles.get(user_id, {}).to_dict() if user_id in self.learning_styles else None,
            'cognitive_profile': self.cognitive_profiles.get(user_id, {}).to_dict() if user_id in self.cognitive_profiles else None,
            'personality': self.personality_traits.get(user_id, {}).to_dict() if user_id in self.personality_traits else None,
            'interaction_count': len(self.interaction_history.get(user_id, [])),
            'last_updated': datetime.utcnow().isoformat()
        }
    
    def import_user_model(self, user_id: str, data: Dict):
        """从持久化数据恢复用户模型"""
        if 'learning_style' in data and data['learning_style']:
            ls_data = data['learning_style']
            self.learning_styles[user_id] = LearningStyleProfile(
                user_id=user_id,
                visual_verbal=ls_data.get('visual_verbal', 0),
                sequential_global=ls_data.get('sequential_global', 0),
                active_reflective=ls_data.get('active_reflective', 0),
                sensing_intuitive=ls_data.get('sensing_intuitive', 0),
                confidence=ls_data.get('confidence', {})
            )
        
        if 'cognitive_profile' in data and data['cognitive_profile']:
            cp_data = data['cognitive_profile']
            self.cognitive_profiles[user_id] = CognitiveProfile(
                user_id=user_id,
                abilities=cp_data.get('abilities', {})
            )
        
        if 'personality' in data and data['personality']:
            p_data = data['personality']
            self.personality_traits[user_id] = PersonalityTraits(
                user_id=user_id,
                openness=p_data.get('openness', 0.5),
                conscientiousness=p_data.get('conscientiousness', 0.5),
                extraversion=p_data.get('extraversion', 0.5),
                agreeableness=p_data.get('agreeableness', 0.5),
                neuroticism=p_data.get('neuroticism', 0.5)
            )
