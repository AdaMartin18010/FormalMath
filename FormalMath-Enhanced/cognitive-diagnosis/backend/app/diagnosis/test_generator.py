"""
诊断测试题生成器
"""

import random
from typing import List, Dict, Optional
from datetime import datetime

from app.models.question import Question, QuestionType, KnowledgeLevel
from app.models.knowledge_graph import KnowledgeGraph
from app.models.diagnosis import DiagnosisSession


class TestGenerator:
    """诊断测试生成器"""
    
    def __init__(self, knowledge_graph: KnowledgeGraph, question_bank: List[Question]):
        self.knowledge_graph = knowledge_graph
        self.question_bank = question_bank
        
        # 按层次和知识点索引题目
        self._build_index()
    
    def _build_index(self):
        """构建题目索引"""
        self.questions_by_level: Dict[int, List[Question]] = {0: [], 1: [], 2: [], 3: []}
        self.questions_by_knowledge: Dict[str, List[Question]] = {}
        
        for question in self.question_bank:
            # 按层次索引
            self.questions_by_level[question.knowledge_level].append(question)
            
            # 按知识点索引
            for tag in question.knowledge_tags:
                if tag not in self.questions_by_knowledge:
                    self.questions_by_knowledge[tag] = []
                self.questions_by_knowledge[tag].append(question)
    
    def generate_diagnosis_test(
        self,
        user_id: str,
        question_count: int = 20,
        target_levels: Optional[List[int]] = None,
        focus_areas: Optional[List[str]] = None
    ) -> DiagnosisSession:
        """
        生成诊断测试
        
        Args:
            user_id: 用户ID
            question_count: 题目数量
            target_levels: 目标层次列表，默认覆盖所有层次
            focus_areas: 重点关注区域（知识点ID列表）
            
        Returns:
            DiagnosisSession: 诊断会话
        """
        if target_levels is None:
            target_levels = [0, 1, 2, 3]
        
        # 生成题目列表
        selected_questions = self._select_questions(
            question_count=question_count,
            target_levels=target_levels,
            focus_areas=focus_areas
        )
        
        # 创建诊断会话
        session = DiagnosisSession(
            id=f"diag_{user_id}_{int(datetime.now().timestamp())}",
            user_id=user_id,
            question_count=len(selected_questions),
            question_ids=[q.id for q in selected_questions]
        )
        
        return session
    
    def _select_questions(
        self,
        question_count: int,
        target_levels: List[int],
        focus_areas: Optional[List[str]] = None
    ) -> List[Question]:
        """选择题目"""
        selected = []
        
        # 如果指定了重点知识点，优先选择
        if focus_areas:
            for area in focus_areas:
                if area in self.questions_by_knowledge:
                    questions = self.questions_by_knowledge[area]
                    selected.extend(questions[:2])  # 每个知识点最多选2题
        
        # 确保各层次都有覆盖
        level_distribution = self._calculate_level_distribution(
            question_count, target_levels
        )
        
        for level, count in level_distribution.items():
            if level not in target_levels:
                continue
                
            level_questions = self.questions_by_level[level]
            
            # 排除已选的
            available = [q for q in level_questions if q not in selected]
            
            # 按难度分布选择（简单:中等:困难 = 4:4:2）
            easy = [q for q in available if q.difficulty < -0.5]
            medium = [q for q in available if -0.5 <= q.difficulty <= 0.5]
            hard = [q for q in available if q.difficulty > 0.5]
            
            # 选择题目
            needed = count
            for pool, ratio in [(easy, 0.4), (medium, 0.4), (hard, 0.2)]:
                pick_count = min(int(count * ratio), len(pool), needed)
                selected.extend(random.sample(pool, pick_count) if pool else [])
                needed -= pick_count
            
            # 如果还不够，从剩余题目中补充
            if needed > 0 and available:
                remaining = [q for q in available if q not in selected]
                if remaining:
                    selected.extend(random.sample(remaining, min(needed, len(remaining))))
        
        # 打乱顺序
        random.shuffle(selected)
        
        return selected[:question_count]
    
    def _calculate_level_distribution(
        self,
        total: int,
        target_levels: List[int]
    ) -> Dict[int, int]:
        """计算各层次题目数量分布"""
        n_levels = len(target_levels)
        
        if n_levels == 0:
            return {}
        
        # 基础分布：L0占30%，L1占35%，L2占25%，L3占10%
        base_distribution = {0: 0.30, 1: 0.35, 2: 0.25, 3: 0.10}
        
        distribution = {}
        for level in target_levels:
            distribution[level] = int(total * base_distribution.get(level, 0.25))
        
        # 调整确保总数正确
        current_total = sum(distribution.values())
        diff = total - current_total
        
        if diff > 0 and target_levels:
            # 优先给低层次增加题目
            for level in sorted(target_levels):
                if diff <= 0:
                    break
                distribution[level] += 1
                diff -= 1
        
        return distribution
    
    def get_question_by_id(self, question_id: str) -> Optional[Question]:
        """根据ID获取题目"""
        for question in self.question_bank:
            if question.id == question_id:
                return question
        return None
    
    def get_questions_for_session(
        self,
        session: DiagnosisSession
    ) -> List[Question]:
        """获取诊断会话的题目列表"""
        questions = []
        for qid in session.question_ids:
            q = self.get_question_by_id(qid)
            if q:
                questions.append(q)
        return questions
    
    def get_next_question(
        self,
        session: DiagnosisSession,
        adaptive: bool = True
    ) -> Optional[Question]:
        """
        获取下一道题目（支持自适应）
        
        Args:
            session: 诊断会话
            adaptive: 是否使用自适应策略
            
        Returns:
            下一道题目或None（如果已完成）
        """
        if session.current_question_index >= len(session.question_ids):
            return None
        
        next_qid = session.question_ids[session.current_question_index]
        return self.get_question_by_id(next_qid)
    
    def score_response(
        self,
        question: Question,
        user_answer: any
    ) -> tuple[bool, float]:
        """
        评分
        
        Returns:
            (是否正确, 得分)
        """
        correct_answer = question.correct_answer
        
        if isinstance(correct_answer, list):
            is_correct = (
                set(user_answer) == set(correct_answer) 
                if isinstance(user_answer, list) 
                else user_answer in correct_answer
            )
        else:
            is_correct = str(user_answer).strip().lower() == str(correct_answer).strip().lower()
        
        score = question.score if is_correct else 0.0
        return is_correct, score
