"""
学习资源推荐模块
基于用户画像和认知风格推荐学习资源
"""
from typing import List, Dict, Optional, Tuple
import random

from ..schemas import (
    UserProfile, ConceptNode, ResourceRecommendation, 
    ResourceType, CognitiveStyle, LearningPreference, DifficultyLevel
)
from ..knowledge_graph import get_knowledge_graph


class ResourceRecommender:
    """资源推荐器"""
    
    def __init__(self):
        self.kg = get_knowledge_graph()
        
        # 资源模板库
        self.resource_templates = {
            ResourceType.TEXT: {
                'prefixes': ['教程', '指南', '详解', '讲义', '笔记'],
                'features': ['系统全面', '逻辑清晰', '适合深入学习']
            },
            ResourceType.VIDEO: {
                'prefixes': ['视频讲解', '公开课', '演示', '动画'],
                'features': ['生动形象', '适合视觉学习者', '可反复观看']
            },
            ResourceType.INTERACTIVE: {
                'prefixes': ['交互式演示', '模拟实验', '可视化工具', '探索工具'],
                'features': ['动手实践', '即时反馈', '深度理解']
            },
            ResourceType.EXERCISE: {
                'prefixes': ['练习题', '习题集', '测试', '挑战题'],
                'features': ['巩固知识', '检验掌握度', '提高熟练度']
            },
            ResourceType.PROOF: {
                'prefixes': ['证明详解', '定理证明', '推导过程'],
                'features': ['严谨逻辑', '培养证明能力', '深入理解']
            },
            ResourceType.EXAMPLE: {
                'prefixes': ['实例分析', '应用案例', '例题精讲', '典型问题'],
                'features': ['具体直观', '联系实际', '启发思路']
            }
        }
    
    def recommend_for_concept(self, user_profile: UserProfile,
                             concept_id: str,
                             num_recommendations: int = 5) -> List[ResourceRecommendation]:
        """
        为特定概念推荐学习资源
        
        Args:
            user_profile: 用户画像
            concept_id: 概念ID
            num_recommendations: 推荐数量
            
        Returns:
            推荐资源列表
        """
        concept = self.kg.get_concept(concept_id)
        if not concept:
            return []
        
        # 确定推荐的资源类型
        preferred_types = self._determine_resource_types(user_profile)
        
        # 确定推荐难度
        recommended_difficulty = self._determine_difficulty(user_profile, concept)
        
        recommendations = []
        
        # 为每种类型生成推荐
        for i, res_type in enumerate(preferred_types[:num_recommendations]):
            relevance = self._calculate_relevance(
                res_type, user_profile, concept
            )
            
            resource = self._create_resource(
                concept=concept,
                res_type=res_type,
                difficulty=recommended_difficulty,
                relevance=relevance,
                index=i
            )
            
            recommendations.append(resource)
        
        # 按相关度排序
        recommendations.sort(key=lambda r: r.relevance_score, reverse=True)
        
        return recommendations
    
    def recommend_for_path(self, user_profile: UserProfile,
                          concept_ids: List[str],
                          num_per_concept: int = 3) -> Dict[str, List[ResourceRecommendation]]:
        """
        为整个学习路径推荐资源
        
        Returns:
            {concept_id: [recommendations]}
        """
        result = {}
        
        for concept_id in concept_ids:
            result[concept_id] = self.recommend_for_concept(
                user_profile, concept_id, num_per_concept
            )
        
        return result
    
    def _determine_resource_types(self, user_profile: UserProfile) -> List[ResourceType]:
        """根据认知风格确定资源类型优先级"""
        style_mapping = {
            CognitiveStyle.VISUAL: [
                ResourceType.VIDEO, ResourceType.INTERACTIVE, 
                ResourceType.EXAMPLE, ResourceType.TEXT
            ],
            CognitiveStyle.READING: [
                ResourceType.TEXT, ResourceType.PROOF,
                ResourceType.EXAMPLE, ResourceType.EXERCISE
            ],
            CognitiveStyle.KINESTHETIC: [
                ResourceType.INTERACTIVE, ResourceType.EXERCISE,
                ResourceType.EXAMPLE, ResourceType.VIDEO
            ],
            CognitiveStyle.AUDITORY: [
                ResourceType.VIDEO, ResourceType.TEXT,
                ResourceType.EXAMPLE, ResourceType.EXERCISE
            ],
            CognitiveStyle.MIXED: [
                ResourceType.TEXT, ResourceType.VIDEO,
                ResourceType.EXERCISE, ResourceType.INTERACTIVE,
                ResourceType.EXAMPLE, ResourceType.PROOF
            ]
        }
        
        base_types = style_mapping.get(
            user_profile.cognitive_style,
            style_mapping[CognitiveStyle.MIXED]
        )
        
        # 根据学习偏好调整
        preference_adjustments = {
            LearningPreference.THEORY_FIRST: [ResourceType.TEXT, ResourceType.PROOF],
            LearningPreference.EXAMPLE_FIRST: [ResourceType.EXAMPLE, ResourceType.VIDEO],
            LearningPreference.PRACTICE_FIRST: [ResourceType.EXERCISE, ResourceType.INTERACTIVE],
            LearningPreference.BALANCED: []
        }
        
        priority_types = preference_adjustments.get(
            user_profile.learning_preference, []
        )
        
        # 重新排序
        result = priority_types.copy()
        for t in base_types:
            if t not in result:
                result.append(t)
        
        return result
    
    def _determine_difficulty(self, user_profile: UserProfile,
                             concept: ConceptNode) -> DifficultyLevel:
        """确定推荐资源的难度"""
        levels = [
            DifficultyLevel.BEGINNER,
            DifficultyLevel.INTERMEDIATE,
            DifficultyLevel.ADVANCED,
            DifficultyLevel.EXPERT
        ]
        
        user_idx = levels.index(user_profile.current_level)
        concept_idx = levels.index(concept.difficulty)
        
        # 平衡用户水平和概念难度
        if user_idx < concept_idx:
            # 用户水平低于概念难度，推荐入门资源
            return levels[user_idx]
        elif user_idx > concept_idx:
            # 用户水平高于概念难度，可以挑战
            return levels[min(concept_idx + 1, len(levels) - 1)]
        else:
            return concept.difficulty
    
    def _calculate_relevance(self, res_type: ResourceType,
                            user_profile: UserProfile,
                            concept: ConceptNode) -> float:
        """计算资源与用户的匹配度"""
        relevance = 0.5  # 基础分
        
        # 认知风格匹配
        style_scores = {
            CognitiveStyle.VISUAL: {
                ResourceType.VIDEO: 0.3, ResourceType.INTERACTIVE: 0.2
            },
            CognitiveStyle.READING: {
                ResourceType.TEXT: 0.3, ResourceType.PROOF: 0.2
            },
            CognitiveStyle.KINESTHETIC: {
                ResourceType.INTERACTIVE: 0.3, ResourceType.EXERCISE: 0.2
            }
        }
        
        style_score = style_scores.get(user_profile.cognitive_style, {})
        relevance += style_score.get(res_type, 0)
        
        # 学习偏好匹配
        preference_scores = {
            LearningPreference.THEORY_FIRST: {
                ResourceType.TEXT: 0.2, ResourceType.PROOF: 0.15
            },
            LearningPreference.EXAMPLE_FIRST: {
                ResourceType.EXAMPLE: 0.25, ResourceType.VIDEO: 0.1
            },
            LearningPreference.PRACTICE_FIRST: {
                ResourceType.EXERCISE: 0.25, ResourceType.INTERACTIVE: 0.1
            }
        }
        
        pref_score = preference_scores.get(user_profile.learning_preference, {})
        relevance += pref_score.get(res_type, 0)
        
        # 概念类型匹配
        branch_preferences = {
            '代数': [ResourceType.TEXT, ResourceType.PROOF, ResourceType.EXERCISE],
            '几何': [ResourceType.VIDEO, ResourceType.INTERACTIVE, ResourceType.EXAMPLE],
            '分析': [ResourceType.TEXT, ResourceType.PROOF, ResourceType.EXAMPLE],
            '拓扑': [ResourceType.VIDEO, ResourceType.INTERACTIVE, ResourceType.TEXT],
        }
        
        preferred_for_branch = branch_preferences.get(concept.branch, [])
        if res_type in preferred_for_branch:
            relevance += 0.1
        
        return round(min(relevance, 1.0), 3)
    
    def _create_resource(self, concept: ConceptNode,
                        res_type: ResourceType,
                        difficulty: DifficultyLevel,
                        relevance: float,
                        index: int) -> ResourceRecommendation:
        """创建资源推荐对象"""
        templates = self.resource_templates.get(res_type, {})
        prefixes = templates.get('prefixes', ['资源'])
        
        # 生成标题
        prefix = prefixes[index % len(prefixes)]
        title = f"{prefix}：{concept.name}"
        
        # 生成描述
        features = templates.get('features', [])
        description = f"针对{concept.name}的{res_type.value}资源"
        if features:
            description += f"。特点：{', '.join(features[:2])}"
        
        # 生成URL（示例）
        url = f"/resources/{concept.id}/{res_type.value}/{index}"
        
        # 估计时间
        time_estimates = {
            ResourceType.TEXT: 20,
            ResourceType.VIDEO: 15,
            ResourceType.INTERACTIVE: 25,
            ResourceType.EXERCISE: 30,
            ResourceType.PROOF: 25,
            ResourceType.EXAMPLE: 15
        }
        estimated_time = time_estimates.get(res_type, 20)
        
        # 难度调整
        if difficulty == DifficultyLevel.BEGINNER:
            estimated_time = int(estimated_time * 0.8)
        elif difficulty == DifficultyLevel.ADVANCED:
            estimated_time = int(estimated_time * 1.3)
        elif difficulty == DifficultyLevel.EXPERT:
            estimated_time = int(estimated_time * 1.5)
        
        # 匹配原因
        match_reasons = [
            f"符合您的{self._get_cognitive_style_desc()}认知风格",
            f"适合{difficulty.value}水平学习",
            f"有助于掌握{concept.branch}分支知识"
        ]
        match_reason = match_reasons[index % len(match_reasons)]
        
        return ResourceRecommendation(
            resource_id=f"res_{concept.id}_{res_type.value}_{index}",
            title=title,
            type=res_type,
            url=url,
            description=description,
            difficulty=difficulty,
            estimated_time=estimated_time,
            relevance_score=relevance,
            match_reason=match_reason,
            suitable_for=[CognitiveStyle.MIXED]
        )
    
    def _get_cognitive_style_desc(self) -> str:
        """获取认知风格描述"""
        return "多样化"
    
    def recommend_next_resource(self, user_profile: UserProfile,
                               current_concept_id: str,
                               last_resource_type: Optional[ResourceType] = None,
                               performance: Optional[float] = None) -> Optional[ResourceRecommendation]:
        """
        推荐下一个学习资源（即时推荐）
        
        Args:
            performance: 上一个资源的学习表现 (0-100)
        """
        concept = self.kg.get_concept(current_concept_id)
        if not concept:
            return None
        
        # 根据表现决定推荐类型
        if performance is not None:
            if performance < 50:
                # 表现不佳，推荐更简单或辅助资源
                if last_resource_type == ResourceType.EXERCISE:
                    # 练习做得不好，推荐示例
                    next_type = ResourceType.EXAMPLE
                else:
                    next_type = ResourceType.TEXT
            elif performance > 85:
                # 表现优秀，推荐进阶内容
                next_type = ResourceType.EXERCISE
            else:
                # 正常，继续同类型或练习
                next_type = ResourceType.EXERCISE if last_resource_type != ResourceType.EXERCISE else ResourceType.TEXT
        else:
            # 没有表现数据，使用默认推荐
            next_type = ResourceType.EXERCISE
        
        relevance = self._calculate_relevance(next_type, user_profile, concept)
        
        return self._create_resource(
            concept=concept,
            res_type=next_type,
            difficulty=concept.difficulty,
            relevance=relevance,
            index=0
        )
    
    def get_resource_by_difficulty(self, resources: List[ResourceRecommendation],
                                   target_difficulty: DifficultyLevel) -> List[ResourceRecommendation]:
        """按难度筛选资源"""
        return [r for r in resources if r.difficulty == target_difficulty]
    
    def diversify_recommendations(self, resources: List[ResourceRecommendation],
                                  diversity_factor: float = 0.3) -> List[ResourceRecommendation]:
        """
        增加推荐多样性
        
        在保持相关度的同时增加资源类型的多样性
        """
        if not resources:
            return []
        
        # 按类型分组
        by_type = {}
        for r in resources:
            if r.type not in by_type:
                by_type[r.type] = []
            by_type[r.type].append(r)
        
        # 多样化选择
        diversified = []
        types = list(by_type.keys())
        
        # 轮询选择不同类型
        while len(diversified) < len(resources):
            added = False
            for t in types:
                if by_type[t]:
                    # 选择该类型中相关度最高的
                    best = max(by_type[t], key=lambda r: r.relevance_score)
                    diversified.append(best)
                    by_type[t].remove(best)
                    added = True
                    
                    if len(diversified) >= len(resources):
                        break
            
            if not added:
                break
        
        return diversified


def recommend_resources(user_profile: UserProfile,
                       concept_id: str,
                       num_recommendations: int = 5) -> List[ResourceRecommendation]:
    """
    资源推荐主函数
    
    Args:
        user_profile: 用户画像
        concept_id: 概念ID
        num_recommendations: 推荐数量
        
    Returns:
        推荐资源列表
    """
    recommender = ResourceRecommender()
    return recommender.recommend_for_concept(
        user_profile, concept_id, num_recommendations
    )
