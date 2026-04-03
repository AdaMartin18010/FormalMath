"""
HCD (Hierarchy-Constrained Diagnosis) Algorithm
层次约束感知认知诊断算法

基于设计文档实现的核心诊断算法
"""
import numpy as np
from typing import Dict, List, Tuple, Optional, Any
from dataclasses import dataclass, field
from datetime import datetime
from scipy.special import expit, logit
import json


@dataclass
class DiagnosisResult:
    """诊断结果数据类"""
    student_id: str
    knowledge_state: Dict[str, float]
    knowledge_confidence: Dict[str, float]
    ability_level: Dict[str, Dict]
    weak_areas: List[Dict]
    strong_areas: List[Dict]
    suggestions: List[Dict]
    overall_confidence: float
    diagnosis_timestamp: str
    
    def to_dict(self) -> Dict:
        """转换为字典"""
        return {
            'student_id': self.student_id,
            'knowledge_state': self.knowledge_state,
            'knowledge_confidence': self.knowledge_confidence,
            'ability_level': self.ability_level,
            'weak_areas': self.weak_areas,
            'strong_areas': self.strong_areas,
            'suggestions': self.suggestions,
            'overall_confidence': self.overall_confidence,
            'diagnosis_timestamp': self.diagnosis_timestamp
        }


@dataclass
class Question:
    """题目数据类"""
    id: str
    type: str
    level: int
    difficulty: float
    branch: str
    concepts: List[str]
    q_vector: Optional[np.ndarray] = None
    discriminations: float = 1.0
    guess: float = 0.25
    slip: float = 0.1
    
    def __post_init__(self):
        if self.q_vector is None:
            self.q_vector = np.zeros(10)


class KnowledgeGraph:
    """知识图谱类"""
    
    def __init__(self):
        self.concepts = {}
        self.edges = []
        self.hierarchy = {0: [], 1: [], 2: [], 3: []}
        
    def add_concept(self, concept_id: str, name: str, level: int, 
                    prerequisites: List[str] = None):
        """添加知识点"""
        self.concepts[concept_id] = {
            'name': name,
            'level': level,
            'prerequisites': prerequisites or []
        }
        self.hierarchy[level].append(concept_id)
        
        # 添加先修关系边
        if prerequisites:
            for prereq in prerequisites:
                self.edges.append({
                    'from': prereq,
                    'to': concept_id,
                    'type': 'prerequisite',
                    'weight': 0.95
                })
    
    def get_concepts_by_level(self, level: int) -> List[str]:
        """获取某层次的所有知识点"""
        return self.hierarchy.get(level, [])
    
    def get_prerequisites(self, concept_id: str) -> List[str]:
        """获取知识点的先修知识"""
        return self.concepts.get(concept_id, {}).get('prerequisites', [])
    
    def get_level(self, concept_id: str) -> int:
        """获取知识点的层次"""
        return self.concepts.get(concept_id, {}).get('level', 0)


class HCDAlgorithm:
    """
    层次约束感知认知诊断算法
    
    核心功能：
    1. 知识状态估计 - 使用EM算法估计各知识点掌握度
    2. 能力水平评估 - 评估L0-L3各层次能力
    3. 层次约束应用 - 应用层次依赖约束
    4. 学习建议生成 - 基于诊断结果生成个性化建议
    """
    
    def __init__(self, knowledge_graph: KnowledgeGraph, 
                 max_iter: int = 50,
                 tolerance: float = 1e-5,
                 learning_rate: float = 0.1):
        """
        初始化HCD算法
        
        Args:
            knowledge_graph: 知识图谱对象
            max_iter: 最大迭代次数
            tolerance: 收敛阈值
            learning_rate: 学习率
        """
        self.kg = knowledge_graph
        self.max_iter = max_iter
        self.tolerance = tolerance
        self.lr = learning_rate
        
        # 构建约束矩阵
        self._build_constraint_matrix()
        
    def _build_constraint_matrix(self):
        """构建层次约束矩阵"""
        concepts = list(self.kg.concepts.keys())
        K = len(concepts)
        
        # 约束矩阵 C[i,j] 表示概念i对概念j的约束强度
        self.constraint_matrix = np.zeros((K, K))
        self.concept_index = {c: i for i, c in enumerate(concepts)}
        
        # 添加层次约束
        for level in range(1, 4):
            lower_concepts = self.kg.get_concepts_by_level(level - 1)
            upper_concepts = self.kg.get_concepts_by_level(level)
            
            for upper in upper_concepts:
                i = self.concept_index[upper]
                for lower in lower_concepts:
                    j = self.concept_index[lower]
                    self.constraint_matrix[j, i] = 0.8
        
        # 添加先修约束
        for edge in self.kg.edges:
            if edge['type'] == 'prerequisite':
                i = self.concept_index[edge['from']]
                j = self.concept_index[edge['to']]
                self.constraint_matrix[i, j] = edge['weight']
    
    def diagnose(self, responses: List[Dict],
                 questions: List[Question],
                 student_id: str = None) -> DiagnosisResult:
        """
        执行认知诊断
        
        Args:
            responses: 答题响应列表
            questions: 题目列表
            student_id: 学生ID
            
        Returns:
            DiagnosisResult: 诊断结果
        """
        print(f"[HCD] 开始诊断: student_id={student_id}")
        
        # 1. 准备数据
        R, Q_matrix = self._prepare_data(responses, questions)
        
        # 2. 初始化参数
        K = len(self.kg.concepts)
        alpha = np.random.beta(2, 2, K)  # 知识状态初始化
        theta = np.zeros(4)  # 能力水平初始化
        
        # 3. EM迭代
        for iteration in range(self.max_iter):
            alpha_old = alpha.copy()
            
            # E步: 估计知识状态
            alpha = self._e_step(R, Q_matrix, alpha, questions)
            
            # M步: 更新能力参数
            theta = self._m_step(R, Q_matrix, alpha, questions)
            
            # 应用层次约束
            alpha = self._apply_hierarchy_constraints(alpha)
            
            # 检查收敛
            delta = np.linalg.norm(alpha - alpha_old)
            if delta < self.tolerance:
                print(f"[HCD] 算法收敛于第{iteration+1}次迭代")
                break
        
        # 4. 计算置信度
        confidence = self._calculate_confidence(R, Q_matrix, alpha, questions)
        
        # 5. 识别强弱领域
        weak_areas, strong_areas = self._identify_areas(alpha, confidence)
        
        # 6. 评估层次能力
        ability_level = self._assess_ability_level(alpha)
        
        # 7. 生成学习建议
        suggestions = self._generate_suggestions(alpha, ability_level, weak_areas)
        
        # 8. 构建结果
        result = DiagnosisResult(
            student_id=student_id or "anonymous",
            knowledge_state=self._alpha_to_dict(alpha),
            knowledge_confidence=self._confidence_to_dict(confidence),
            ability_level=ability_level,
            weak_areas=weak_areas,
            strong_areas=strong_areas,
            suggestions=suggestions,
            overall_confidence=float(np.mean(confidence)),
            diagnosis_timestamp=datetime.now().isoformat()
        )
        
        print(f"[HCD] 诊断完成: overall_confidence={result.overall_confidence:.3f}")
        return result
    
    def _prepare_data(self, responses: List[Dict], 
                      questions: List[Question]) -> Tuple[np.ndarray, np.ndarray]:
        """准备响应矩阵和Q矩阵"""
        M = len(questions)
        K = len(self.kg.concepts)
        
        R = np.array([r['is_correct'] for r in responses])
        Q_matrix = np.array([q.q_vector for q in questions])
        
        return R, Q_matrix
    
    def _e_step(self, R: np.ndarray, Q: np.ndarray, 
                alpha: np.ndarray, questions: List[Question]) -> np.ndarray:
        """E步: 贝叶斯知识状态估计"""
        K = len(alpha)
        alpha_new = alpha.copy()
        
        for k in range(K):
            likelihood_correct = 0
            likelihood_incorrect = 0
            
            for i, q in enumerate(questions):
                if Q[i, k] > 0:
                    eta = q.discriminations * (alpha[k] - q.difficulty)
                    p_correct = expit(eta) * (1 - q.slip) + q.guess
                    
                    if R[i] == 1:
                        likelihood_correct += np.log(p_correct + 1e-10)
                    else:
                        likelihood_incorrect += np.log(1 - p_correct + 1e-10)
            
            log_posterior = logit(alpha[k]) + self.lr * (likelihood_correct - likelihood_incorrect)
            alpha_new[k] = expit(np.clip(log_posterior, -10, 10))
        
        return np.clip(alpha_new, 0.01, 0.99)
    
    def _m_step(self, R: np.ndarray, Q: np.ndarray,
                alpha: np.ndarray, questions: List[Question]) -> np.ndarray:
        """M步: 更新能力参数"""
        theta = np.zeros(4)
        
        for level in range(4):
            concepts = self.kg.get_concepts_by_level(level)
            if concepts:
                indices = [self.concept_index[c] for c in concepts]
                theta[level] = logit(np.mean(alpha[indices]) + 1e-10)
        
        return theta
    
    def _apply_hierarchy_constraints(self, alpha: np.ndarray) -> np.ndarray:
        """应用层次约束"""
        alpha_constrained = alpha.copy()
        
        # 约束1: 层次间约束
        for level in range(1, 4):
            lower_concepts = self.kg.get_concepts_by_level(level - 1)
            upper_concepts = self.kg.get_concepts_by_level(level)
            
            if not lower_concepts or not upper_concepts:
                continue
            
            lower_indices = [self.concept_index[c] for c in lower_concepts]
            upper_indices = [self.concept_index[c] for c in upper_concepts]
            
            lower_mean = np.mean(alpha[lower_indices])
            upper_mean = np.mean(alpha[upper_indices])
            
            max_upper = min(1.0, lower_mean + 0.3)
            
            if upper_mean > max_upper:
                scale = max_upper / (upper_mean + 1e-10)
                for idx in upper_indices:
                    alpha_constrained[idx] = alpha[idx] * scale
        
        # 约束2: 先修约束
        for edge in self.kg.edges:
            if edge['type'] == 'prerequisite':
                prereq_idx = self.concept_index[edge['from']]
                concept_idx = self.concept_index[edge['to']]
                
                prereq_level = alpha[prereq_idx]
                concept_level = alpha_constrained[concept_idx]
                
                max_allowed = min(1.0, prereq_level + 0.2)
                alpha_constrained[concept_idx] = min(concept_level, max_allowed)
        
        return np.clip(alpha_constrained, 0.01, 0.99)
    
    def _calculate_confidence(self, R: np.ndarray, Q: np.ndarray,
                              alpha: np.ndarray, questions: List[Question]) -> np.ndarray:
        """计算知识状态估计的置信度"""
        K = len(alpha)
        confidence = np.ones(K)
        
        for k in range(K):
            relevant_questions = sum(Q[:, k] > 0)
            
            if relevant_questions == 0:
                confidence[k] = 0.1
            else:
                confidence[k] = min(0.95, 0.3 + 0.15 * np.sqrt(relevant_questions))
        
        return confidence
    
    def _identify_areas(self, alpha: np.ndarray, 
                        confidence: np.ndarray) -> Tuple[List[Dict], List[Dict]]:
        """识别薄弱环节和优势领域"""
        concepts = list(self.kg.concepts.keys())
        
        weak_threshold = 0.4
        weak_areas = []
        for i, concept in enumerate(concepts):
            if alpha[i] < weak_threshold and confidence[i] > 0.5:
                weak_areas.append({
                    'concept_id': concept,
                    'concept_name': self.kg.concepts[concept]['name'],
                    'current_level': float(alpha[i]),
                    'target_level': 0.7,
                    'improvement_needed': float(0.7 - alpha[i])
                })
        
        strong_threshold = 0.8
        strong_areas = []
        for i, concept in enumerate(concepts):
            if alpha[i] > strong_threshold:
                strong_areas.append({
                    'concept_id': concept,
                    'concept_name': self.kg.concepts[concept]['name'],
                    'current_level': float(alpha[i])
                })
        
        weak_areas.sort(key=lambda x: x['improvement_needed'], reverse=True)
        strong_areas.sort(key=lambda x: x['current_level'], reverse=True)
        
        return weak_areas[:5], strong_areas[:5]
    
    def _assess_ability_level(self, alpha: np.ndarray) -> Dict[str, Dict]:
        """评估L0-L3层次能力水平"""
        ability = {}
        
        for level in range(4):
            concepts = self.kg.get_concepts_by_level(level)
            if not concepts:
                ability[f'L{level}'] = {
                    'score': 0.0,
                    'level': 'none',
                    'description': '该层次无知识点'
                }
                continue
            
            indices = [self.concept_index[c] for c in concepts]
            level_score = float(np.mean(alpha[indices]))
            
            if level_score < 0.4:
                level_name = 'beginner'
                description = '初学者'
            elif level_score < 0.6:
                level_name = 'developing'
                description = '发展中'
            elif level_score < 0.8:
                level_name = 'intermediate'
                description = '中级'
            else:
                level_name = 'advanced'
                description = '高级'
            
            ability[f'L{level}'] = {
                'score': level_score,
                'level': level_name,
                'description': description,
                'concept_count': len(concepts),
                'mastered_concepts': int(sum(alpha[indices] > 0.7))
            }
        
        return ability
    
    def _generate_suggestions(self, alpha: np.ndarray, 
                              ability: Dict,
                              weak_areas: List[Dict]) -> List[Dict]:
        """生成学习建议"""
        suggestions = []
        
        # 优先级1: 基础层次薄弱
        if ability['L0']['score'] < 0.5:
            suggestions.append({
                'type': 'foundation',
                'priority': 1,
                'title': '加强基础概念学习',
                'description': '您的L0基础概念掌握度较低，建议先巩固基础知识。',
                'action': '学习L0层次的核心概念，完成基础练习题',
                'estimated_time': '2-3周'
            })
        
        # 优先级2: 具体薄弱知识点
        for i, area in enumerate(weak_areas[:3]):
            suggestions.append({
                'type': 'concept',
                'priority': 2 + i,
                'title': f'强化：{area["concept_name"]}',
                'description': f'该知识点掌握度为{area["current_level"]:.0%}，需要重点提升。',
                'action': '复习相关概念，完成针对性练习',
                'target_concept': area['concept_id']
            })
        
        # 优先级3: 层次能力提升
        current_max_level = max(
            [l for l in range(4) if ability[f'L{l}']['score'] > 0.5],
            default=-1
        )
        if current_max_level < 3:
            next_level = current_max_level + 1
            suggestions.append({
                'type': 'level_up',
                'priority': 5,
                'title': f'向L{next_level}层次进阶',
                'description': f'建议在当前层次巩固后，尝试L{next_level}层次的内容。',
                'action': '完成当前层次的综合练习，再学习进阶内容',
                'prerequisite': f'L{current_max_level}掌握度达到70%'
            })
        
        # 优先级4: 学习方法建议
        suggestions.append({
            'type': 'method',
            'priority': 6,
            'title': '推荐学习方法',
            'description': '基于您的诊断结果，推荐以下学习方法。',
            'actions': [
                '使用间隔重复法复习薄弱知识点',
                '完成概念-例子-证明的学习闭环',
                '定期进行自测，跟踪学习进展'
            ]
        })
        
        return suggestions
    
    def _alpha_to_dict(self, alpha: np.ndarray) -> Dict[str, float]:
        """将知识状态向量转换为字典"""
        concepts = list(self.kg.concepts.keys())
        return {c: float(alpha[i]) for i, c in enumerate(concepts)}
    
    def _confidence_to_dict(self, confidence: np.ndarray) -> Dict[str, float]:
        """将置信度向量转换为字典"""
        concepts = list(self.kg.concepts.keys())
        return {c: float(confidence[i]) for i, c in enumerate(concepts)}


def build_default_knowledge_graph() -> KnowledgeGraph:
    """构建默认知识图谱"""
    kg = KnowledgeGraph()
    
    # L0层：基础概念
    kg.add_concept('set_basic', '集合基础', 0)
    kg.add_concept('func_basic', '函数基础', 0)
    kg.add_concept('limit_basic', '极限直观理解', 0)
    kg.add_concept('group_basic', '群的基本概念', 0)
    kg.add_concept('ring_basic', '环的基本概念', 0)
    kg.add_concept('topo_basic', '拓扑直观理解', 0)
    
    # L1层：定义理解
    kg.add_concept('set_def', '集合严格定义', 1, ['set_basic'])
    kg.add_concept('func_def', '函数严格定义', 1, ['func_basic'])
    kg.add_concept('limit_def', '极限严格定义', 1, ['limit_basic'])
    kg.add_concept('group_axiom', '群公理', 1, ['group_basic'])
    kg.add_concept('subgroup', '子群', 1, ['group_axiom'])
    kg.add_concept('homomorphism', '同态', 1, ['group_axiom'])
    kg.add_concept('ring_def', '环的定义', 1, ['ring_basic'])
    kg.add_concept('topo_def', '拓扑空间定义', 1, ['topo_basic'])
    
    # L2层：定理应用
    kg.add_concept('cont_theory', '连续性理论', 2, ['limit_def'])
    kg.add_concept('deriv_app', '导数应用', 2, ['limit_def'])
    kg.add_concept('lagrange', 'Lagrange定理', 2, ['subgroup'])
    kg.add_concept('isomorphism_thm', '同态基本定理', 2, ['homomorphism'])
    kg.add_concept('field_ext', '域扩张', 2, ['ring_def'])
    kg.add_concept('compactness', '紧致性理论', 2, ['topo_def'])
    
    # L3层：综合证明
    kg.add_concept('anal_proof', '分析学综合证明', 3, ['cont_theory', 'deriv_app'])
    kg.add_concept('galois_theory', 'Galois理论', 3, ['lagrange', 'isomorphism_thm', 'field_ext'])
    kg.add_concept('alg_geo', '代数几何基础', 3, ['galois_theory'])
    kg.add_concept('alg_topo', '代数拓扑基础', 3, ['compactness'])
    
    return kg
