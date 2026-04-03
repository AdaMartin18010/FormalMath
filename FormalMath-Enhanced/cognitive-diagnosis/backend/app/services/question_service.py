"""
题目服务
"""

import random
from typing import List, Optional

from app.models.question import Question, QuestionType, KnowledgeTag
from app.database.in_memory_db import InMemoryDatabase


class QuestionService:
    """题目服务"""
    
    def __init__(self):
        self.db = InMemoryDatabase()
    
    def get_questions(
        self,
        level: Optional[int] = None,
        question_type: Optional[QuestionType] = None,
        knowledge_tag: Optional[str] = None,
        limit: int = 20,
        offset: int = 0
    ) -> List[Question]:
        """获取题目列表"""
        questions = self.db.get_all_questions()
        
        # 应用过滤条件
        if level is not None:
            questions = [q for q in questions if q.knowledge_level == level]
        
        if question_type:
            questions = [q for q in questions if q.type == question_type]
        
        if knowledge_tag:
            questions = [q for q in questions if knowledge_tag in q.knowledge_tags]
        
        # 分页
        return questions[offset:offset + limit]
    
    def get_question_by_id(self, question_id: str) -> Optional[Question]:
        """根据ID获取题目"""
        return self.db.get_question(question_id)
    
    def count_questions(
        self,
        level: Optional[int] = None,
        question_type: Optional[QuestionType] = None,
        knowledge_tag: Optional[str] = None
    ) -> int:
        """统计题目数量"""
        questions = self.db.get_all_questions()
        
        if level is not None:
            questions = [q for q in questions if q.knowledge_level == level]
        
        if question_type:
            questions = [q for q in questions if q.type == question_type]
        
        if knowledge_tag:
            questions = [q for q in questions if knowledge_tag in q.knowledge_tags]
        
        return len(questions)
    
    def get_random_questions(
        self,
        count: int = 10,
        level: Optional[int] = None
    ) -> List[Question]:
        """获取随机题目"""
        questions = self.db.get_all_questions()
        
        if level is not None:
            questions = [q for q in questions if q.knowledge_level == level]
        
        if len(questions) <= count:
            return questions
        
        return random.sample(questions, count)
    
    def get_knowledge_tags(self, level: Optional[int] = None) -> List[KnowledgeTag]:
        """获取知识点标签"""
        tags = self.db.get_all_knowledge_tags()
        
        if level is not None:
            tags = [t for t in tags if t.level == level]
        
        return tags
    
    def get_questions_by_knowledge(self, knowledge_tag_id: str) -> List[Question]:
        """根据知识点获取题目"""
        questions = self.db.get_all_questions()
        return [q for q in questions if knowledge_tag_id in q.knowledge_tags]
