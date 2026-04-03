"""
题库管理服务
"""
import yaml
import json
import random
from typing import List, Dict, Optional, Any
from pathlib import Path

from app.core.config import settings


class QuestionBank:
    """题库管理类"""
    
    def __init__(self, question_file: str = None):
        """
        初始化题库
        
        Args:
            question_file: 题库文件路径
        """
        self.question_file = question_file or settings.QUESTION_BANK_PATH
        self.questions: List[Dict] = []
        self.concept_index: Dict[str, List[int]] = {}
        self.level_index: Dict[int, List[int]] = {0: [], 1: [], 2: [], 3: []}
        self.branch_index: Dict[str, List[int]] = {}
        
        # 加载题库
        self._load_questions()
    
    def _load_questions(self):
        """从YAML文件加载题目"""
        try:
            if Path(self.question_file).exists():
                with open(self.question_file, 'r', encoding='utf-8') as f:
                    data = yaml.safe_load(f)
                    self.questions = data.get('questions', [])
            else:
                # 使用内置题目
                self.questions = self._get_builtin_questions()
            
            # 构建索引
            self._build_index()
            print(f"[QuestionBank] 加载了 {len(self.questions)} 道题目")
        except Exception as e:
            print(f"[QuestionBank] 加载失败: {e}")
            self.questions = self._get_builtin_questions()
            self._build_index()
    
    def _build_index(self):
        """构建题目索引"""
        for idx, q in enumerate(self.questions):
            # 按概念索引
            for concept in q.get('concepts', []):
                if concept not in self.concept_index:
                    self.concept_index[concept] = []
                self.concept_index[concept].append(idx)
            
            # 按层次索引
            level = q.get('level', 0)
            if level in self.level_index:
                self.level_index[level].append(idx)
            
            # 按分支索引
            branch = q.get('branch', '其他')
            if branch not in self.branch_index:
                self.branch_index[branch] = []
            self.branch_index[branch].append(idx)
    
    def get_questions(self, 
                      level: Optional[int] = None,
                      branch: Optional[str] = None,
                      concepts: List[str] = None,
                      count: int = 30,
                      exclude_ids: List[str] = None) -> List[Dict]:
        """
        获取题目
        
        Args:
            level: 知识层次筛选
            branch: 分支筛选
            concepts: 概念筛选
            count: 题目数量
            exclude_ids: 排除的题目ID
            
        Returns:
            题目列表
        """
        exclude_ids = exclude_ids or []
        candidates = []
        
        # 根据条件筛选
        if level is not None and level in self.level_index:
            candidates = [self.questions[i] for i in self.level_index[level]]
        elif branch and branch in self.branch_index:
            candidates = [self.questions[i] for i in self.branch_index[branch]]
        elif concepts:
            concept_set = set()
            for concept in concepts:
                if concept in self.concept_index:
                    concept_set.update(self.concept_index[concept])
            candidates = [self.questions[i] for i in concept_set]
        else:
            candidates = self.questions[:]
        
        # 排除已做过的题目
        candidates = [q for q in candidates if q.get('id') not in exclude_ids]
        
        # 随机选择
        if len(candidates) > count:
            candidates = random.sample(candidates, count)
        
        # 移除答案信息
        return [self._sanitize_question(q) for q in candidates]
    
    def get_diagnostic_questions(self, 
                                  target_level: Optional[int] = None,
                                  count: int = 30) -> List[Dict]:
        """
        获取诊断测试题目
        
        按层次分布：L0(25%), L1(30%), L2(30%), L3(15%)
        
        Args:
            target_level: 目标层次
            count: 题目总数
            
        Returns:
            题目列表
        """
        if target_level is not None:
            # 针对特定层次的诊断
            level_counts = {
                0: count,
                1: [max(3, count//4), count - max(3, count//4)],
                2: [count//4, count//2, count//4],
                3: [count//4, count//4, count//4, count//4]
            }[min(target_level, 3)]
            
            questions = []
            if target_level == 0:
                questions.extend(self.get_questions(level=0, count=count))
            else:
                for i, c in enumerate(level_counts if isinstance(level_counts, list) else [count]):
                    level_q = self.get_questions(level=i, count=c)
                    questions.extend(level_q)
        else:
            # 全面诊断
            l0_count = int(count * 0.25)
            l1_count = int(count * 0.30)
            l2_count = int(count * 0.30)
            l3_count = count - l0_count - l1_count - l2_count
            
            questions = []
            questions.extend(self.get_questions(level=0, count=l0_count))
            questions.extend(self.get_questions(level=1, count=l1_count))
            questions.extend(self.get_questions(level=2, count=l2_count))
            questions.extend(self.get_questions(level=3, count=l3_count))
        
        random.shuffle(questions)
        return questions[:count]
    
    def get_question_by_id(self, question_id: str) -> Optional[Dict]:
        """通过ID获取题目（含答案）"""
        for q in self.questions:
            if q.get('id') == question_id:
                return q
        return None
    
    def check_answer(self, question_id: str, answer: str) -> Dict:
        """
        检查答案
        
        Args:
            question_id: 题目ID
            answer: 学生答案
            
        Returns:
            检查结果
        """
        question = self.get_question_by_id(question_id)
        if not question:
            return {'correct': False, 'error': '题目不存在'}
        
        q_type = question.get('type')
        correct_answer = question.get('answer')
        
        # 自动判题
        if q_type in ['SC', 'FB']:
            is_correct = answer.strip().upper() == str(correct_answer).strip().upper()
        elif q_type == 'MC':
            student_ans = set(answer.replace(' ', '').split(','))
            correct_ans = set(str(correct_answer).replace(' ', '').split(','))
            is_correct = student_ans == correct_ans
        else:
            # SA/PR需要人工评分
            is_correct = None
        
        return {
            'correct': is_correct,
            'correct_answer': correct_answer,
            'explanation': question.get('explanation', ''),
            'score': question.get('score', 5) if is_correct else 0
        }
    
    def _sanitize_question(self, question: Dict) -> Dict:
        """清理题目（移除答案信息）"""
        return {
            'id': question.get('id'),
            'content': question.get('content'),
            'type': question.get('type'),
            'level': question.get('level'),
            'difficulty': question.get('difficulty'),
            'branch': question.get('branch'),
            'concepts': question.get('concepts', []),
            'time_estimate': question.get('time_estimate', 60),
            'score': question.get('score', 5),
            'options': question.get('options') if question.get('type') in ['SC', 'MC'] else None
        }
    
    def get_statistics(self) -> Dict:
        """获取题库统计信息"""
        stats = {
            'total': len(self.questions),
            'by_level': {f'L{i}': len(self.level_index[i]) for i in range(4)},
            'by_branch': {branch: len(indices) for branch, indices in self.branch_index.items()},
            'by_type': {}
        }
        
        type_count = {}
        for q in self.questions:
            q_type = q.get('type', 'Unknown')
            type_count[q_type] = type_count.get(q_type, 0) + 1
        stats['by_type'] = type_count
        
        return stats
    
    def _get_builtin_questions(self) -> List[Dict]:
        """获取内置题目（当题库文件不存在时使用）"""
        return [
            # L0 基础概念
            {
                'id': 'CDS-L0-A-001',
                'content': '下列哪个集合与运算构成群？\n\nA. 自然数集 ℕ 与加法运算\nB. 整数集 ℤ 与加法运算\nC. 整数集 ℤ 与乘法运算\nD. 偶数集 2ℤ 与乘法运算',
                'type': 'SC',
                'level': 0,
                'difficulty': 1,
                'branch': '代数学',
                'concepts': ['群', '代数结构'],
                'answer': 'B',
                'explanation': '群需要满足四个条件：封闭性、结合律、单位元、逆元。整数加法是群（单位元0，逆元是相反数）。',
                'time_estimate': 60,
                'score': 5
            },
            {
                'id': 'CDS-L0-AN-001',
                'content': '数列极限 lim(n→∞) aₙ = a 的直观含义是什么？\n\nA. 数列的项最终会等于a\nB. 数列的项会无限接近a\nC. 数列的每一项都小于a\nD. 数列单调递减趋向a',
                'type': 'SC',
                'level': 0,
                'difficulty': 1,
                'branch': '分析学',
                'concepts': ['极限', '数列'],
                'answer': 'B',
                'explanation': '极限的直观含义是"无限接近但不一定达到"。',
                'time_estimate': 60,
                'score': 5
            },
            {
                'id': 'CDS-L0-T-001',
                'content': '拓扑学的"橡皮几何学"绰号体现了什么特点？\n\nA. 拓扑研究的对象像橡皮一样柔软\nB. 拓扑性质在连续变形下保持不变\nC. 拓扑空间的元素可以任意拉伸\nD. 拓扑学研究橡皮形状的物体',
                'type': 'SC',
                'level': 0,
                'difficulty': 1,
                'branch': '几何与拓扑',
                'concepts': ['拓扑空间', '拓扑'],
                'answer': 'B',
                'explanation': '拓扑学研究在连续变形（拉伸、压缩，但不撕裂、不粘合）下保持不变的性质。',
                'time_estimate': 75,
                'score': 5
            },
            # L1 定义理解
            {
                'id': 'CDS-L1-A-001',
                'content': '验证 (ℤ₅, +) 是否构成群，需要验证哪些条件？\n\nA. 只需验证加法封闭\nB. 验证封闭性、结合律、单位元、逆元\nC. 只需验证交换律\nD. 验证加法和乘法',
                'type': 'SC',
                'level': 1,
                'difficulty': 2,
                'branch': '代数学',
                'concepts': ['群', '群公理'],
                'answer': 'B',
                'explanation': '群的四个公理：封闭性、结合律、单位元、逆元。',
                'time_estimate': 90,
                'score': 5
            },
            {
                'id': 'CDS-L1-AN-001',
                'content': '数列极限的严格定义（ε-N定义）：对于任意ε>0，存在N∈ℕ，使得当n>N时，有______。',
                'type': 'FB',
                'level': 1,
                'difficulty': 3,
                'branch': '分析学',
                'concepts': ['极限', 'ε-N定义'],
                'answer': '|aₙ - a| < ε',
                'explanation': '数列极限的ε-N定义：∀ε>0, ∃N∈ℕ, ∀n>N, |aₙ-a|<ε',
                'time_estimate': 120,
                'score': 10
            },
            # L2 定理应用
            {
                'id': 'CDS-L2-A-001',
                'content': '设G是有限群，|G|=12。根据Sylow定理，G的Sylow 3-子群的个数n₃满足什么条件？',
                'type': 'SC',
                'level': 2,
                'difficulty': 4,
                'branch': '代数学',
                'concepts': ['Sylow定理', '有限群'],
                'answer': 'A',
                'options': {
                    'A': 'n₃ ≡ 1 (mod 3) 且 n₃ | 4',
                    'B': 'n₃ ≡ 1 (mod 12) 且 n₃ | 3',
                    'C': 'n₃ ≡ 0 (mod 3) 且 n₃ | 12',
                    'D': 'n₃ = 1'
                },
                'explanation': 'Sylow第三定理：nₚ ≡ 1 (mod p) 且 nₚ | m，其中|G|=p^k·m。',
                'time_estimate': 180,
                'score': 10
            },
            # L3 综合证明
            {
                'id': 'CDS-L3-A-001',
                'content': '设φ: G → H是群同态，证明：G/Ker(φ) ≅ Im(φ)',
                'type': 'PR',
                'level': 3,
                'difficulty': 5,
                'branch': '代数学',
                'concepts': ['同态基本定理', '商群'],
                'answer': '证明要点：构造映射 ψ: G/Ker(φ) → Im(φ)，ψ(gKer(φ)) = φ(g)，证明ψ是同构。',
                'explanation': '这是群同态基本定理，是群论中最重要的定理之一。',
                'time_estimate': 300,
                'score': 20
            }
        ]


# 全局题库实例
question_bank = QuestionBank()
