"""
学习路径实时调整模块
根据学习表现动态调整路径
"""
from typing import List, Dict, Optional, Tuple
from datetime import datetime, timedelta
import numpy as np

from ..schemas import (
    UserProfile, LearningPath, PathNode, PathStatus, 
    PathAdjustment, LearningActivity, DifficultyLevel
)
from ..knowledge_graph import get_knowledge_graph
from ..core.config import settings


class PathAdjuster:
    """学习路径调整器"""
    
    def __init__(self, user_profile: UserProfile):
        self.user_profile = user_profile
        self.kg = get_knowledge_graph()
    
    def evaluate_performance(self, activities: List[LearningActivity],
                            path: LearningPath) -> Dict[str, any]:
        """
        评估学习表现
        
        分析学习者在当前路径上的表现
        """
        evaluation = {
            'overall_score': 0.0,
            'struggle_concepts': [],
            'mastery_concepts': [],
            'pace_assessment': 'normal',
            'difficulty_assessment': 'appropriate',
            'recommendations': []
        }
        
        # 按概念聚合活动
        concept_performance = {}
        for activity in activities:
            cid = activity.concept_id
            if cid not in concept_performance:
                concept_performance[cid] = {
                    'scores': [],
                    'total_time': 0,
                    'attempts': 0
                }
            
            if activity.score is not None:
                concept_performance[cid]['scores'].append(activity.score)
            concept_performance[cid]['total_time'] += activity.duration
            concept_performance[cid]['attempts'] += 1
        
        # 分析每个概念
        struggle_concepts = []
        mastery_concepts = []
        
        for concept_id, perf in concept_performance.items():
            avg_score = np.mean(perf['scores']) if perf['scores'] else 0
            concept = self.kg.get_concept(concept_id)
            expected_time = concept.estimated_time if concept else 30
            
            # 判断掌握情况
            if avg_score >= settings.MASTERY_THRESHOLD * 100:
                mastery_concepts.append({
                    'concept_id': concept_id,
                    'score': avg_score,
                    'time_ratio': perf['total_time'] / expected_time
                })
            elif avg_score < settings.STRUGGLE_THRESHOLD * 100:
                struggle_concepts.append({
                    'concept_id': concept_id,
                    'score': avg_score,
                    'time_ratio': perf['total_time'] / expected_time,
                    'attempts': perf['attempts']
                })
        
        evaluation['struggle_concepts'] = struggle_concepts
        evaluation['mastery_concepts'] = mastery_concepts
        
        # 整体评分
        if concept_performance:
            all_scores = []
            for perf in concept_performance.values():
                all_scores.extend(perf['scores'])
            if all_scores:
                evaluation['overall_score'] = np.mean(all_scores)
        
        # 学习节奏评估
        total_time = sum(p['total_time'] for p in concept_performance.values())
        expected_total = sum(
            self.kg.get_concept(cid).estimated_time if self.kg.get_concept(cid) else 30
            for cid in concept_performance.keys()
        )
        
        if expected_total > 0:
            pace_ratio = total_time / expected_total
            if pace_ratio < 0.7:
                evaluation['pace_assessment'] = 'fast'
            elif pace_ratio > 1.5:
                evaluation['pace_assessment'] = 'slow'
        
        # 难度评估
        if len(struggle_concepts) >= 2:
            evaluation['difficulty_assessment'] = 'too_hard'
        elif len(mastery_concepts) >= len(concept_performance) * 0.8:
            evaluation['difficulty_assessment'] = 'too_easy'
        
        return evaluation
    
    def should_adjust(self, evaluation: Dict) -> Tuple[bool, str]:
        """
        判断是否需要调整路径
        
        Returns:
            (是否需要调整, 调整原因)
        """
        # 检查困难概念数量
        if len(evaluation['struggle_concepts']) >= 2:
            return True, "检测到多个困难概念，需要调整路径"
        
        # 检查难度不匹配
        if evaluation['difficulty_assessment'] == 'too_hard':
            return True, "当前路径难度过高"
        
        if evaluation['difficulty_assessment'] == 'too_easy':
            return True, "当前路径难度过低，建议增加挑战"
        
        # 检查学习节奏
        if evaluation['pace_assessment'] == 'slow':
            return True, "学习进度较慢，建议优化路径"
        
        # 检查整体表现
        if evaluation['overall_score'] < 50:
            return True, "整体表现不佳，需要路径调整"
        
        return False, ""
    
    def adjust_path(self, path: LearningPath,
                   evaluation: Dict,
                   reason: str = "") -> PathAdjustment:
        """
        调整学习路径
        
        根据评估结果生成路径调整方案
        """
        adjustment = PathAdjustment(
            adjustment_id=f"adj_{datetime.now().timestamp()}",
            path_id=path.path_id,
            user_id=self.user_profile.user_id,
            trigger_reason=reason or evaluation.get('adjustment_reason', ''),
            performance_data=evaluation,
            old_nodes=path.nodes.copy(),
            adjustment_type='modify'
        )
        
        new_nodes = path.nodes.copy()
        
        # 1. 处理困难概念
        for struggle in evaluation.get('struggle_concepts', []):
            concept_id = struggle['concept_id']
            self._handle_struggle_concept(new_nodes, concept_id, struggle)
        
        # 2. 处理掌握良好的概念 - 可能跳过或加速
        for mastery in evaluation.get('mastery_concepts', []):
            concept_id = mastery['concept_id']
            self._handle_mastery_concept(new_nodes, concept_id, mastery)
        
        # 3. 难度不匹配调整
        if evaluation['difficulty_assessment'] == 'too_hard':
            new_nodes = self._reduce_difficulty(new_nodes)
        elif evaluation['difficulty_assessment'] == 'too_easy':
            new_nodes = self._increase_difficulty(new_nodes)
        
        # 4. 节奏调整
        if evaluation['pace_assessment'] == 'slow':
            new_nodes = self._optimize_pace(new_nodes)
        
        # 重新排序
        new_nodes = self._reorder_nodes(new_nodes)
        
        adjustment.new_nodes = new_nodes
        
        # 更新路径
        path.nodes = new_nodes
        path.status = PathStatus.ADJUSTED
        path.updated_at = datetime.now()
        
        return adjustment
    
    def _handle_struggle_concept(self, nodes: List[PathNode],
                                 concept_id: str,
                                 struggle_data: Dict):
        """处理困难概念 - 添加辅助资源或先修概念"""
        # 查找对应节点
        for i, node in enumerate(nodes):
            if node.concept.id == concept_id:
                # 增加学习时间估计
                node.estimated_time = int(node.estimated_time * 1.5)
                
                # 添加额外资源
                extra_resources = [
                    {
                        'id': f"extra_{concept_id}_basic",
                        'title': f"基础回顾 - {node.concept.name}",
                        'type': 'text',
                        'difficulty': 'beginner'
                    },
                    {
                        'id': f"extra_{concept_id}_example",
                        'title': f"详细示例 - {node.concept.name}",
                        'type': 'example',
                        'difficulty': node.concept.difficulty.value
                    }
                ]
                node.recommended_resources.extend(extra_resources)
                
                # 检查是否需要添加先修
                if struggle_data.get('attempts', 0) >= 3:
                    prereqs = self.kg.get_prerequisites(concept_id, recursive=False)
                    for prereq_id in prereqs:
                        if prereq_id not in [n.concept.id for n in nodes]:
                            if prereq_id not in self.user_profile.mastered_concepts:
                                # 插入先修概念
                                prereq_concept = self.kg.get_concept(prereq_id)
                                if prereq_concept:
                                    new_node = PathNode(
                                        node_id=f"inserted_{prereq_id}",
                                        concept=prereq_concept,
                                        order=i,
                                        status=PathStatus.PENDING,
                                        estimated_time=prereq_concept.estimated_time
                                    )
                                    nodes.insert(i, new_node)
                
                break
    
    def _handle_mastery_concept(self, nodes: List[PathNode],
                               concept_id: str,
                               mastery_data: Dict):
        """处理掌握良好的概念 - 可能跳过或标记为快速通过"""
        for node in nodes:
            if node.concept.id == concept_id:
                # 如果掌握度很高，标记为已完成
                if mastery_data.get('score', 0) >= 90:
                    node.status = PathStatus.COMPLETED
                    node.estimated_time = max(node.estimated_time // 3, 5)
                
                # 减少资源推荐
                node.recommended_resources = node.recommended_resources[:2]
                break
    
    def _reduce_difficulty(self, nodes: List[PathNode]) -> List[PathNode]:
        """降低路径难度 - 替换或移除高难度概念"""
        filtered_nodes = []
        
        for node in nodes:
            difficulty_order = [
                DifficultyLevel.BEGINNER,
                DifficultyLevel.INTERMEDIATE,
                DifficultyLevel.ADVANCED,
                DifficultyLevel.EXPERT
            ]
            
            current_idx = difficulty_order.index(node.concept.difficulty)
            user_idx = difficulty_order.index(self.user_profile.current_level)
            
            # 如果概念难度远高于用户水平，尝试替换
            if current_idx > user_idx + 1:
                # 查找简化版本或跳过
                # 简化：暂时保留但增加辅助资源
                node.difficulty_adjustment = -1
                node.recommended_resources.insert(0, {
                    'id': f"simplified_{node.concept.id}",
                    'title': f"简化介绍 - {node.concept.name}",
                    'type': 'text',
                    'difficulty': 'beginner'
                })
                filtered_nodes.append(node)
            else:
                filtered_nodes.append(node)
        
        return filtered_nodes
    
    def _increase_difficulty(self, nodes: List[PathNode]) -> List[PathNode]:
        """增加路径难度 - 添加进阶内容"""
        for node in nodes:
            if node.status == PathStatus.COMPLETED or node.status == PathStatus.IN_PROGRESS:
                # 添加进阶资源
                advanced_resource = {
                    'id': f"advanced_{node.concept.id}",
                    'title': f"进阶探索 - {node.concept.name}",
                    'type': 'exercise',
                    'difficulty': 'advanced'
                }
                if advanced_resource not in node.recommended_resources:
                    node.recommended_resources.append(advanced_resource)
        
        return nodes
    
    def _optimize_pace(self, nodes: List[PathNode]) -> List[PathNode]:
        """优化学习节奏 - 合并或简化节点"""
        optimized = []
        i = 0
        
        while i < len(nodes):
            node = nodes[i]
            
            # 如果已完成，保留
            if node.status == PathStatus.COMPLETED:
                optimized.append(node)
                i += 1
                continue
            
            # 检查是否可以与下一个节点合并
            if i < len(nodes) - 1:
                next_node = nodes[i + 1]
                
                # 如果两个概念相关且都未开始，考虑简化
                if (node.status == PathStatus.PENDING and 
                    next_node.status == PathStatus.PENDING and
                    next_node.concept.id in self.kg.get_related_concepts(node.concept.id)):
                    
                    # 减少时间估计
                    node.estimated_time = int(node.estimated_time * 0.7)
                    optimized.append(node)
                else:
                    optimized.append(node)
            else:
                optimized.append(node)
            
            i += 1
        
        return optimized
    
    def _reorder_nodes(self, nodes: List[PathNode]) -> List[PathNode]:
        """重新排序节点 - 确保先修关系正确"""
        # 基于先修关系的拓扑排序
        concept_ids = [n.concept.id for n in nodes]
        
        # 构建子图
        ordered = []
        visited = set()
        
        def visit(node: PathNode):
            if node.concept.id in visited:
                return
            
            # 先访问先修
            for prereq_id in node.concept.prerequisites:
                if prereq_id in concept_ids:
                    prereq_node = next(
                        (n for n in nodes if n.concept.id == prereq_id), None
                    )
                    if prereq_node:
                        visit(prereq_node)
            
            visited.add(node.concept.id)
            ordered.append(node)
        
        for node in nodes:
            visit(node)
        
        # 更新顺序
        for i, node in enumerate(ordered):
            node.order = i
        
        return ordered
    
    def suggest_immediate_action(self, current_concept_id: str,
                                 recent_activities: List[LearningActivity]) -> Dict:
        """
        建议即时学习行动
        
        基于最近表现给出实时建议
        """
        suggestion = {
            'action': 'continue',
            'message': '继续保持当前学习节奏',
            'resources': [],
            'adjustments': {}
        }
        
        if not recent_activities:
            return suggestion
        
        # 计算最近表现
        recent_scores = [a.score for a in recent_activities 
                        if a.score is not None][-3:]
        
        if not recent_scores:
            return suggestion
        
        avg_recent = np.mean(recent_scores)
        
        if avg_recent < 40:
            suggestion['action'] = 'review'
            suggestion['message'] = '建议回顾基础概念，难度可能过高'
            suggestion['resources'] = [
                {'type': 'review', 'title': '基础概念回顾'},
                {'type': 'example', 'title': '简单示例'}
            ]
        elif avg_recent < 60:
            suggestion['action'] = 'practice'
            suggestion['message'] = '建议多做练习巩固'
            suggestion['resources'] = [
                {'type': 'exercise', 'title': '针对性练习'},
                {'type': 'hint', 'title': '解题提示'}
            ]
        elif avg_recent > 85:
            suggestion['action'] = 'accelerate'
            suggestion['message'] = '掌握良好，可以适当加速'
            suggestion['resources'] = [
                {'type': 'challenge', 'title': '挑战题目'},
                {'type': 'next', 'title': '预习下一概念'}
            ]
        
        return suggestion


def adjust_learning_path(user_profile: UserProfile,
                        path: LearningPath,
                        activities: List[LearningActivity]) -> Optional[PathAdjustment]:
    """
    根据学习表现调整路径的主函数
    
    Args:
        user_profile: 用户画像
        path: 当前学习路径
        activities: 学习活动记录
        
    Returns:
        路径调整方案，如果不需要调整则返回 None
    """
    adjuster = PathAdjuster(user_profile)
    
    # 评估表现
    evaluation = adjuster.evaluate_performance(activities, path)
    
    # 判断是否需要调整
    should_adjust, reason = adjuster.should_adjust(evaluation)
    
    if not should_adjust:
        return None
    
    evaluation['adjustment_reason'] = reason
    
    # 执行调整
    adjustment = adjuster.adjust_path(path, evaluation, reason)
    
    return adjustment
