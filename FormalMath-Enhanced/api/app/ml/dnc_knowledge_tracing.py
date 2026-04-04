"""
DNC (Differentiable Neural Computer) 知识追踪模型
使用记忆增强神经网络实现高精度知识状态追踪
"""
import math
import numpy as np
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from collections import deque
import json


@dataclass
class MemorySlot:
    """DNC记忆槽位"""
    key: np.ndarray
    value: np.ndarray
    usage: float = 0.0
    timestamp: datetime = field(default_factory=datetime.utcnow)
    access_count: int = 0


@dataclass
class KnowledgeState:
    """知识状态"""
    concept_id: str
    mastery_level: float  # 0-1
    confidence: float  # 置信度
    last_updated: datetime
    interaction_history: List[Dict] = field(default_factory=list)
    prerequisite_mastery: Dict[str, float] = field(default_factory=dict)
    
    def to_dict(self) -> Dict:
        return {
            'concept_id': self.concept_id,
            'mastery_level': self.mastery_level,
            'confidence': self.confidence,
            'last_updated': self.last_updated.isoformat(),
            'interaction_count': len(self.interaction_history)
        }


class TemporalLinkage:
    """时序关联矩阵 - 记录知识概念间的时间关联"""
    
    def __init__(self, max_concepts: int = 1000):
        self.max_concepts = max_concepts
        self.linkage_matrix = np.zeros((max_concepts, max_concepts))
        self.concept_to_idx: Dict[str, int] = {}
        self.idx_to_concept: Dict[int, str] = {}
        self.next_idx = 0
    
    def _get_idx(self, concept_id: str) -> int:
        if concept_id not in self.concept_to_idx:
            if self.next_idx >= self.max_concepts:
                # 循环使用或扩展
                self._compact_matrix()
            self.concept_to_idx[concept_id] = self.next_idx
            self.idx_to_concept[self.next_idx] = concept_id
            self.next_idx += 1
        return self.concept_to_idx[concept_id]
    
    def _compact_matrix(self):
        """压缩矩阵，移除低频概念"""
        # 保留活跃的概念
        active_indices = set(self.concept_to_idx.values())
        # 重新映射
        new_mapping = {c: i for i, c in enumerate(self.concept_to_idx.keys())}
        self.concept_to_idx = new_mapping
        self.idx_to_concept = {v: k for k, v in new_mapping.items()}
        self.next_idx = len(new_mapping)
        
        # 重建矩阵
        new_matrix = np.zeros((self.max_concepts, self.max_concepts))
        for old_i, new_i in enumerate(new_mapping.values()):
            for old_j, new_j in enumerate(new_mapping.values()):
                new_matrix[new_i, new_j] = self.linkage_matrix[old_i, old_j]
        self.linkage_matrix = new_matrix
    
    def update_linkage(self, concept_a: str, concept_b: str, strength: float):
        """更新概念间关联强度"""
        idx_a = self._get_idx(concept_a)
        idx_b = self._get_idx(concept_b)
        
        # 对称更新
        self.linkage_matrix[idx_a, idx_b] = max(
            self.linkage_matrix[idx_a, idx_b],
            strength
        )
        self.linkage_matrix[idx_b, idx_a] = self.linkage_matrix[idx_a, idx_b]
    
    def get_related_concepts(self, concept_id: str, threshold: float = 0.3) -> List[Tuple[str, float]]:
        """获取相关概念及其关联强度"""
        if concept_id not in self.concept_to_idx:
            return []
        
        idx = self.concept_to_idx[concept_id]
        linkages = self.linkage_matrix[idx]
        
        related = []
        for i, strength in enumerate(linkages):
            if strength >= threshold and i in self.idx_to_concept:
                related.append((self.idx_to_concept[i], float(strength)))
        
        return sorted(related, key=lambda x: x[1], reverse=True)


class DNCKnowledgeTracer:
    """
    DNC知识追踪器
    
    结合Differentiable Neural Computer架构实现：
    1. 外部可寻址记忆
    2. 时序关联维护
    3. 注意力读写机制
    """
    
    def __init__(
        self,
        memory_size: int = 128,
        memory_vector_dim: int = 64,
        controller_dim: int = 128,
        num_reads: int = 4,
        num_writes: int = 1
    ):
        self.memory_size = memory_size
        self.memory_vector_dim = memory_vector_dim
        self.controller_dim = controller_dim
        self.num_reads = num_reads
        self.num_writes = num_writes
        
        # 记忆矩阵
        self.memory = np.zeros((memory_size, memory_vector_dim))
        
        # 读写权重
        self.read_weights = np.ones((num_reads, memory_size)) / memory_size
        self.write_weights = np.ones((num_writes, memory_size)) / memory_size
        
        # 时序关联
        self.temporal_linkage = TemporalLinkage()
        
        # 知识状态缓存
        self.knowledge_states: Dict[str, KnowledgeState] = {}
        
        # 控制器状态
        self.controller_state = np.zeros(controller_dim)
        
        # 使用情况向量（用于分配策略）
        self.usage_vector = np.zeros(memory_size)
        
        # 学习率参数
        self.learning_rate = 0.1
        self.decay_factor = 0.95
    
    def _content_addressing(
        self,
        key: np.ndarray,
        strength: float = 1.0
    ) -> np.ndarray:
        """
        基于内容的寻址
        
        Args:
            key: 查询键向量
            strength: 聚焦强度
        
        Returns:
            注意力权重分布
        """
        # 计算余弦相似度
        norm_key = key / (np.linalg.norm(key) + 1e-8)
        norm_memory = self.memory / (np.linalg.norm(self.memory, axis=1, keepdims=True) + 1e-8)
        
        similarity = np.dot(norm_memory, norm_key)
        
        # 应用聚焦
        weighted_similarity = similarity * strength
        
        # softmax
        exp_sim = np.exp(weighted_similarity - np.max(weighted_similarity))
        weights = exp_sim / (np.sum(exp_sim) + 1e-8)
        
        return weights
    
    def _allocation_addressing(self) -> np.ndarray:
        """
        基于使用情况的动态分配寻址
        
        Returns:
            分配权重，优先选择使用少的记忆槽位
        """
        # 根据使用情况排序
        sorted_indices = np.argsort(self.usage_vector)
        
        # 分配概率与使用情况成反比
        allocation = np.zeros(self.memory_size)
        for i, idx in enumerate(sorted_indices):
            allocation[idx] = (1 - self.usage_vector[idx]) * np.exp(-0.1 * i)
        
        return allocation / (np.sum(allocation) + 1e-8)
    
    def _update_usage(self, read_weights: np.ndarray, write_weights: np.ndarray):
        """更新使用情况向量"""
        # 衰减
        self.usage_vector *= self.decay_factor
        
        # 增加新的使用
        self.usage_vector += np.sum(read_weights, axis=0)
        self.usage_vector += np.sum(write_weights, axis=0)
        
        # 限制到[0,1]
        self.usage_vector = np.clip(self.usage_vector, 0, 1)
    
    def read(self, keys: List[np.ndarray], strengths: List[float]) -> List[np.ndarray]:
        """
        从记忆中读取
        
        Args:
            keys: 查询键列表
            strengths: 聚焦强度列表
        
        Returns:
            读取的向量列表
        """
        results = []
        new_read_weights = np.zeros((self.num_reads, self.memory_size))
        
        for i, (key, strength) in enumerate(zip(keys, strengths)):
            weights = self._content_addressing(key, strength)
            new_read_weights[i] = weights
            
            # 加权读取
            read_vector = np.dot(weights, self.memory)
            results.append(read_vector)
        
        self.read_weights = new_read_weights
        return results
    
    def write(self, key: np.ndarray, value: np.ndarray, erase_vector: Optional[np.ndarray] = None):
        """
        写入记忆
        
        Args:
            key: 写入键
            value: 写入值
            erase_vector: 擦除向量（用于选择性遗忘）
        """
        # 获取写入位置
        allocation_weights = self._allocation_addressing()
        content_weights = self._content_addressing(key)
        
        # 插值：新内容 vs 分配新位置
        gate = 0.5  # 可学习的门控
        write_weights = gate * content_weights + (1 - gate) * allocation_weights
        write_weights = write_weights / (np.sum(write_weights) + 1e-8)
        
        self.write_weights[0] = write_weights
        
        # 执行擦除（如果有）
        if erase_vector is not None:
            erase_weights = erase_vector.reshape(-1, 1) * write_weights.reshape(1, -1)
            self.memory *= (1 - erase_weights.T)
        
        # 执行写入
        add_matrix = np.outer(write_weights, value)
        self.memory += add_matrix
        
        # 更新使用情况
        self._update_usage(self.read_weights, self.write_weights)
    
    def encode_interaction(
        self,
        concept_id: str,
        interaction_type: str,
        result: str,
        duration: int,
        difficulty: float,
        timestamp: Optional[datetime] = None
    ) -> np.ndarray:
        """
        编码学习交互为向量
        
        Args:
            concept_id: 概念ID
            interaction_type: 交互类型 (exercise, video, reading, etc.)
            result: 结果 (correct, incorrect, partial)
            duration: 持续时间（秒）
            difficulty: 难度 0-1
            timestamp: 时间戳
        
        Returns:
            编码向量
        """
        # 简单的编码方案
        vector = np.zeros(self.memory_vector_dim)
        
        # 概念ID哈希到前32维
        concept_hash = hash(concept_id) % (2**31)
        np.random.seed(concept_hash)
        vector[:32] = np.random.randn(32) * 0.1
        
        # 交互类型编码 (32-40)
        type_encoding = {
            'exercise': [1, 0, 0, 0],
            'video': [0, 1, 0, 0],
            'reading': [0, 0, 1, 0],
            'quiz': [0, 0, 0, 1]
        }
        vector[32:36] = type_encoding.get(interaction_type, [0, 0, 0, 0])
        
        # 结果编码 (36-40)
        result_encoding = {
            'correct': [1, 0, 0],
            'partial': [0, 1, 0],
            'incorrect': [0, 0, 1]
        }
        vector[36:39] = result_encoding.get(result, [0, 0, 0])
        
        # 归一化的持续时间和难度 (39-41)
        vector[39] = min(duration / 3600, 1.0)  # 最大1小时
        vector[40] = difficulty
        
        # 时间特征 (41-48)
        if timestamp is None:
            timestamp = datetime.utcnow()
        hour = timestamp.hour / 24.0
        day_of_week = timestamp.weekday() / 7.0
        vector[41] = np.sin(2 * np.pi * hour)
        vector[42] = np.cos(2 * np.pi * hour)
        vector[43] = np.sin(2 * np.pi * day_of_week)
        vector[44] = np.cos(2 * np.pi * day_of_week)
        
        # 剩余维度添加噪声用于区分
        vector[45:] = np.random.randn(self.memory_vector_dim - 45) * 0.01
        
        return vector
    
    def update_knowledge_state(
        self,
        concept_id: str,
        interaction_data: Dict[str, Any]
    ) -> KnowledgeState:
        """
        更新知识状态
        
        Args:
            concept_id: 概念ID
            interaction_data: 交互数据
        
        Returns:
            更新后的知识状态
        """
        # 编码交互
        interaction_vector = self.encode_interaction(
            concept_id=concept_id,
            interaction_type=interaction_data.get('type', 'exercise'),
            result=interaction_data.get('result', 'incorrect'),
            duration=interaction_data.get('duration', 0),
            difficulty=interaction_data.get('difficulty', 0.5),
            timestamp=interaction_data.get('timestamp', datetime.utcnow())
        )
        
        # 写入记忆
        key = interaction_vector[:32]  # 使用概念部分作为键
        self.write(key, interaction_vector)
        
        # 计算新的掌握程度
        result = interaction_data.get('result', 'incorrect')
        difficulty = interaction_data.get('difficulty', 0.5)
        
        # 基础更新规则
        if result == 'correct':
            delta = 0.1 * (1 + difficulty)
        elif result == 'partial':
            delta = 0.05 * difficulty
        else:
            delta = -0.05
        
        # 获取或创建知识状态
        if concept_id not in self.knowledge_states:
            current_mastery = 0.0
            history = []
        else:
            current_mastery = self.knowledge_states[concept_id].mastery_level
            history = self.knowledge_states[concept_id].interaction_history
        
        # 应用学习曲线衰减
        n_interactions = len(history)
        learning_rate = self.learning_rate / (1 + 0.1 * n_interactions)  # 递减学习率
        
        new_mastery = current_mastery + learning_rate * delta
        new_mastery = np.clip(new_mastery, 0, 1)
        
        # 计算置信度（基于交互次数的一致性）
        if len(history) > 0:
            recent_results = [
                1 if h.get('result') == 'correct' else 0.5 if h.get('result') == 'partial' else 0
                for h in history[-10:]
            ]
            consistency = 1.0 - np.std(recent_results) if len(recent_results) > 1 else 0.5
            confidence = min(0.5 + 0.05 * len(history), 0.95) * consistency
        else:
            confidence = 0.3
        
        # 更新历史
        history.append({
            'timestamp': datetime.utcnow().isoformat(),
            **interaction_data
        })
        
        # 更新知识状态
        state = KnowledgeState(
            concept_id=concept_id,
            mastery_level=new_mastery,
            confidence=confidence,
            last_updated=datetime.utcnow(),
            interaction_history=history[-100:]  # 保留最近100条
        )
        
        self.knowledge_states[concept_id] = state
        
        # 更新时序关联
        # 如果有前置知识，更新关联
        for prereq_id, prereq_mastery in interaction_data.get('prerequisites', {}).items():
            if prereq_id in self.knowledge_states:
                self.temporal_linkage.update_linkage(
                    concept_id, prereq_id,
                    strength=prereq_mastery * new_mastery
                )
        
        return state
    
    def predict_performance(
        self,
        concept_id: str,
        difficulty: float = 0.5
    ) -> Tuple[float, float]:
        """
        预测在概念上的表现
        
        Args:
            concept_id: 概念ID
            difficulty: 题目难度
        
        Returns:
            (预测正确率, 置信度)
        """
        if concept_id not in self.knowledge_states:
            # 尝试基于相关概念推断
            related = self.temporal_linkage.get_related_concepts(concept_id)
            if related:
                weighted_mastery = 0
                total_weight = 0
                for rel_id, weight in related[:5]:
                    if rel_id in self.knowledge_states:
                        rel_state = self.knowledge_states[rel_id]
                        weighted_mastery += rel_state.mastery_level * weight
                        total_weight += weight
                if total_weight > 0:
                    inferred_mastery = weighted_mastery / total_weight
                    return max(0.1, inferred_mastery * (1 - difficulty * 0.5)), 0.3
            
            return 0.2, 0.1  # 默认低掌握、低置信度
        
        state = self.knowledge_states[concept_id]
        
        # 基于掌握程度和难度预测
        # 难度越高，需要更高的掌握程度才能达到高正确率
        performance = state.mastery_level * (1 - difficulty * 0.3)
        
        # 考虑置信度
        confidence = state.confidence
        
        return max(0, performance), confidence
    
    def get_learning_path_suggestions(
        self,
        target_concepts: List[str],
        current_concepts: Optional[List[str]] = None,
        max_suggestions: int = 5
    ) -> List[Dict]:
        """
        生成学习路径建议
        
        Args:
            target_concepts: 目标概念列表
            current_concepts: 当前已学概念
            max_suggestions: 最大建议数
        
        Returns:
            建议列表
        """
        suggestions = []
        
        for concept_id in target_concepts:
            if concept_id in self.knowledge_states:
                state = self.knowledge_states[concept_id]
                if state.mastery_level >= 0.8:
                    continue  # 已掌握
            
            # 预测表现
            pred_perf, conf = self.predict_performance(concept_id)
            
            # 获取相关概念
            related = self.temporal_linkage.get_related_concepts(concept_id)
            related_mastery = []
            for rel_id, weight in related[:3]:
                if rel_id in self.knowledge_states:
                    related_mastery.append({
                        'concept_id': rel_id,
                        'mastery': self.knowledge_states[rel_id].mastery_level,
                        'relevance': weight
                    })
            
            suggestions.append({
                'concept_id': concept_id,
                'predicted_performance': pred_perf,
                'confidence': conf,
                'priority': 1 - pred_perf,  # 优先级与预测表现成反比
                'related_mastery': related_mastery,
                'estimated_time': self._estimate_learning_time(concept_id, pred_perf)
            })
        
        # 按优先级排序
        suggestions.sort(key=lambda x: x['priority'], reverse=True)
        
        return suggestions[:max_suggestions]
    
    def _estimate_learning_time(self, concept_id: str, current_mastery: float) -> int:
        """估计学习时间（分钟）"""
        # 基于掌握程度和概念复杂度
        base_time = 30  # 基础30分钟
        
        # 需要提升的程度
        mastery_gap = max(0, 0.8 - current_mastery)
        
        # 基于历史交互估计
        if concept_id in self.knowledge_states:
            history = self.knowledge_states[concept_id].interaction_history
            if history:
                avg_time = np.mean([h.get('duration', 300) for h in history]) / 60
                return int(max(avg_time * mastery_gap / 0.1, 10))
        
        return int(base_time * (1 + mastery_gap * 2))
    
    def get_knowledge_state_summary(self) -> Dict:
        """获取知识状态摘要"""
        if not self.knowledge_states:
            return {'total_concepts': 0, 'average_mastery': 0, 'concepts': []}
        
        masteries = [s.mastery_level for s in self.knowledge_states.values()]
        confidences = [s.confidence for s in self.knowledge_states.values()]
        
        return {
            'total_concepts': len(self.knowledge_states),
            'average_mastery': float(np.mean(masteries)),
            'average_confidence': float(np.mean(confidences)),
            'mastered_concepts': sum(1 for m in masteries if m >= 0.8),
            'concepts': [
                {
                    'concept_id': cid,
                    'mastery': state.mastery_level,
                    'confidence': state.confidence,
                    'last_updated': state.last_updated.isoformat()
                }
                for cid, state in self.knowledge_states.items()
            ]
        }
    
    def export_state(self) -> Dict:
        """导出状态用于持久化"""
        return {
            'knowledge_states': {
                cid: {
                    'concept_id': s.concept_id,
                    'mastery_level': s.mastery_level,
                    'confidence': s.confidence,
                    'last_updated': s.last_updated.isoformat(),
                    'interaction_history': s.interaction_history
                }
                for cid, s in self.knowledge_states.items()
            },
            'memory_snapshot': self.memory.tolist(),
            'usage_vector': self.usage_vector.tolist()
        }
    
    def import_state(self, state_dict: Dict):
        """从持久化状态恢复"""
        # 恢复知识状态
        for cid, s in state_dict.get('knowledge_states', {}).items():
            self.knowledge_states[cid] = KnowledgeState(
                concept_id=s['concept_id'],
                mastery_level=s['mastery_level'],
                confidence=s['confidence'],
                last_updated=datetime.fromisoformat(s['last_updated']),
                interaction_history=s.get('interaction_history', [])
            )
        
        # 恢复记忆
        if 'memory_snapshot' in state_dict:
            self.memory = np.array(state_dict['memory_snapshot'])
        
        if 'usage_vector' in state_dict:
            self.usage_vector = np.array(state_dict['usage_vector'])


class MultiHeadKnowledgeTracer:
    """多头知识追踪器 - 同时追踪多个知识维度"""
    
    def __init__(self, num_heads: int = 3):
        self.num_heads = num_heads
        self.tracers = [
            DNCKnowledgeTracer(
                memory_size=64,
                memory_vector_dim=32,
                controller_dim=64
            )
            for _ in range(num_heads)
        ]
        
        # 不同追踪器的专长
        self.head_specializations = [
            'concept_mastery',  # 概念掌握
            'problem_solving',  # 问题解决能力
            'retention',        # 知识保持
        ]
    
    def update(self, concept_id: str, interaction_data: Dict, head_weights: Optional[List[float]] = None):
        """更新所有追踪器"""
        if head_weights is None:
            head_weights = [1.0] * self.num_heads
        
        results = []
        for tracer, weight in zip(self.tracers, head_weights):
            # 根据权重调整数据
            adjusted_data = interaction_data.copy()
            if 'difficulty' in adjusted_data:
                adjusted_data['difficulty'] *= weight
            
            result = tracer.update_knowledge_state(concept_id, adjusted_data)
            results.append(result)
        
        return results
    
    def get_ensemble_prediction(self, concept_id: str) -> Dict:
        """获取集成预测"""
        predictions = []
        for tracer, spec in zip(self.tracers, self.head_specializations):
            pred, conf = tracer.predict_performance(concept_id)
            predictions.append({
                'specialization': spec,
                'prediction': pred,
                'confidence': conf
            })
        
        # 加权平均
        total_conf = sum(p['confidence'] for p in predictions)
        if total_conf > 0:
            ensemble_pred = sum(
                p['prediction'] * p['confidence'] / total_conf
                for p in predictions
            )
        else:
            ensemble_pred = 0.2
        
        return {
            'ensemble_prediction': ensemble_pred,
            'head_predictions': predictions,
            'uncertainty': np.std([p['prediction'] for p in predictions])
        }
