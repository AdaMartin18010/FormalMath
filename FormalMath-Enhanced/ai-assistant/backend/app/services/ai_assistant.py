"""
AI助手核心服务
整合LLM、知识库和数学专用功能
"""
import re
import json
import logging
from typing import Dict, List, Optional, AsyncGenerator, Any
from dataclasses import dataclass, field
from datetime import datetime

from ..llm.client import LLMClient, get_llm_client, LLMConfig, LLMResponse
from ..llm.math_prompts import get_math_prompts
from ..knowledge.knowledge_service import get_knowledge_service
from ..knowledge.context_builder import get_context_builder

logger = logging.getLogger(__name__)


@dataclass
class AssistantResponse:
    """助手响应"""
    answer: str
    answer_type: str  # 'concept', 'proof', 'advice', 'problem', 'general'
    confidence: float
    context_used: Dict[str, Any] = field(default_factory=dict)
    suggestions: List[str] = field(default_factory=list)
    references: List[Dict] = field(default_factory=list)
    latex_formulas: List[str] = field(default_factory=list)
    proof_steps: List[str] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)


@dataclass
class QuestionIntent:
    """问题意图"""
    primary_type: str  # 'concept_explanation', 'proof_hint', 'learning_advice', 'problem_solving', 'lean_help', 'general'
    concept: Optional[str] = None
    difficulty_level: str = "intermediate"
    requires_step_by_step: bool = False
    math_domain: Optional[str] = None


class IntentClassifier:
    """问题意图分类器"""
    
    # 意图识别模式
    INTENT_PATTERNS = {
        'concept_explanation': [
            r'什么是(.+?)[?？]',
            r'解释(.+?)',
            r'(.+?)的定义',
            r'请介绍(.+?)',
            r'what is (.+?)\?',
            r'explain (.+?)',
            r'define (.+?)',
        ],
        'proof_hint': [
            r'证明(.+?)',
            r'如何证明(.+?)',
            r'(.+?)的证明',
            r'prove (.+?)',
            r'how to prove (.+?)',
            r'proof of (.+?)',
            r'证明思路',
        ],
        'learning_advice': [
            r'如何学习(.+?)',
            r'学习(.+?)的建议',
            r'(.+?)的学习路径',
            r'推荐(.+?)',
            r'how to learn (.+?)',
            r'study plan for (.+?)',
            r'learning path',
        ],
        'problem_solving': [
            r'求解(.+?)',
            r'计算(.+?)',
            r'解(.+?)',
            r'solve (.+?)',
            r'calculate (.+?)',
            r'compute (.+?)',
        ],
        'lean_help': [
            r'lean',
            r'形式化',
            r'formaliz',
            r'tactic',
            r'lemma',
        ]
    }
    
    # 难度级别关键词
    DIFFICULTY_KEYWORDS = {
        'beginner': ['基础', '入门', '简单', 'basic', 'beginner', 'introduction', '简单'],
        'advanced': ['高级', '深入', '复杂', 'advanced', 'deep', 'complex', '严格']
    }
    
    def classify(self, question: str) -> QuestionIntent:
        """分类问题意图"""
        question_lower = question.lower()
        
        # 检测主要意图
        primary_type = 'general'
        matched_concept = None
        
        for intent_type, patterns in self.INTENT_PATTERNS.items():
            for pattern in patterns:
                match = re.search(pattern, question, re.IGNORECASE)
                if match:
                    primary_type = intent_type
                    # 提取概念（如果有捕获组）
                    if match.groups():
                        matched_concept = match.group(1).strip()
                    break
            if primary_type != 'general':
                break
        
        # 检测难度级别
        difficulty = 'intermediate'
        for level, keywords in self.DIFFICULTY_KEYWORDS.items():
            if any(kw in question_lower for kw in keywords):
                difficulty = level
                break
        
        # 检测是否需要逐步解答
        step_keywords = ['步骤', '详细', 'step', 'detailed', '一步一步', '逐步']
        requires_step = any(kw in question_lower for kw in step_keywords)
        
        # 检测数学领域
        domains = self._detect_domain(question)
        
        return QuestionIntent(
            primary_type=primary_type,
            concept=matched_concept,
            difficulty_level=difficulty,
            requires_step_by_step=requires_step,
            math_domain=domains[0] if domains else None
        )
    
    def _detect_domain(self, question: str) -> List[str]:
        """检测数学领域"""
        domains = []
        domain_keywords = {
            'algebra': ['代数', 'group', 'ring', 'field', 'polynomial', 'linear'],
            'analysis': ['分析', '极限', '微分', '积分', 'convergence', 'continuous'],
            'geometry': ['几何', 'topology', 'space', 'manifold', 'metric'],
            'number_theory': ['数论', 'prime', 'modular', 'integer', 'diophantine'],
            'logic': ['逻辑', 'proof', 'formal', 'axiom', 'proposition'],
            'probability': ['概率', '统计', 'random', 'distribution', 'expectation']
        }
        
        question_lower = question.lower()
        for domain, keywords in domain_keywords.items():
            if any(kw in question_lower for kw in keywords):
                domains.append(domain)
        
        return domains


class AIAssistantService:
    """
    AI助手核心服务
    提供数学概念问答、证明辅助、学习建议等功能
    """
    
    def __init__(
        self,
        llm_client: LLMClient = None,
        knowledge_service = None
    ):
        self.llm = llm_client or get_llm_client()
        self.knowledge = knowledge_service or get_knowledge_service()
        self.context_builder = get_context_builder()
        self.prompts = get_math_prompts()
        self.intent_classifier = IntentClassifier()
        
        # 统计
        self._stats = {
            'total_queries': 0,
            'by_type': {},
            'avg_response_time_ms': 0.0
        }
    
    async def ask(
        self,
        question: str,
        context_id: Optional[str] = None,
        user_id: Optional[str] = None,
        **kwargs
    ) -> AssistantResponse:
        """
        通用问答接口
        
        Args:
            question: 用户问题
            context_id: 对话上下文ID
            user_id: 用户ID（用于个性化）
        """
        start_time = datetime.now()
        self._stats['total_queries'] += 1
        
        # 1. 分类问题意图
        intent = self.intent_classifier.classify(question)
        
        # 2. 根据意图路由到对应处理
        if intent.primary_type == 'concept_explanation':
            response = await self.explain_concept(
                concept=intent.concept or question,
                level=intent.difficulty_level,
                context_id=context_id
            )
        elif intent.primary_type == 'proof_hint':
            response = await self.get_proof_hint(
                theorem=intent.concept or question,
                context_id=context_id
            )
        elif intent.primary_type == 'learning_advice':
            response = await self.get_learning_advice(
                goal=intent.concept or question,
                user_id=user_id,
                context_id=context_id
            )
        elif intent.primary_type == 'problem_solving':
            response = await self.solve_problem(
                problem=question,
                show_steps=intent.requires_step_by_step,
                context_id=context_id
            )
        elif intent.primary_type == 'lean_help':
            response = await self.help_lean_formalization(
                statement=intent.concept or question,
                context_id=context_id
            )
        else:
            # 通用问答
            response = await self._general_qa(question, context_id)
        
        # 更新统计
        self._update_stats(intent.primary_type, start_time)
        
        return response
    
    async def explain_concept(
        self,
        concept: str,
        level: str = "intermediate",
        context_id: Optional[str] = None
    ) -> AssistantResponse:
        """解释数学概念"""
        # 构建上下文
        llm_context = self.context_builder.build_for_concept_explanation(concept, level)
        
        # 构建提示词
        prompt = self.prompts.get_concept_explain_prompt(concept, level)
        
        # 调用LLM
        llm_response = await self.llm.chat(
            message=prompt,
            context_id=context_id,
            system_prompt=llm_context.system_prompt
        )
        
        # 获取建议问题
        suggestions = self.knowledge.suggest_questions(concept, k=3)
        
        return AssistantResponse(
            answer=llm_response.content,
            answer_type='concept',
            confidence=llm_response.confidence_score,
            context_used={'concept': concept, 'level': level},
            suggestions=suggestions,
            latex_formulas=llm_response.latex_formulas[:5],
            references=[{'source': r['source'], 'preview': r['preview']} 
                       for r in llm_context.references[:3]]
        )
    
    async def get_proof_hint(
        self,
        theorem: str,
        user_attempt: Optional[str] = None,
        context_id: Optional[str] = None
    ) -> AssistantResponse:
        """获取证明提示"""
        # 构建上下文
        llm_context = self.context_builder.build_for_proof_hint(theorem, user_attempt)
        
        # 构建提示词
        prompt = self.prompts.get_proof_hint_prompt(theorem)
        if user_attempt:
            prompt += f"\n\n我的尝试:\n{user_attempt}"
        
        # 调用LLM
        llm_response = await self.llm.chat(
            message=prompt,
            context_id=context_id,
            system_prompt=llm_context.system_prompt
        )
        
        return AssistantResponse(
            answer=llm_response.content,
            answer_type='proof',
            confidence=llm_response.confidence_score,
            context_used={'theorem': theorem},
            proof_steps=llm_response.proof_steps,
            latex_formulas=llm_response.latex_formulas[:5],
            suggestions=[
                '能详细解释第一步吗？',
                '这个证明使用了什么技巧？',
                '有什么类似的定理？'
            ]
        )
    
    async def get_learning_advice(
        self,
        goal: str,
        user_id: Optional[str] = None,
        context_id: Optional[str] = None
    ) -> AssistantResponse:
        """获取学习建议"""
        # 构建上下文
        llm_context = self.context_builder.build_for_learning_advice(goal, user_id)
        
        # 构建提示词
        user_context = llm_context.metadata.get('user_context', {})
        prompt = self.prompts.get_learning_advice_prompt(
            knowledge_level=user_context.get('knowledge_level', 'intermediate'),
            weak_areas=user_context.get('weak_areas', []),
            learning_goal=goal,
            available_time=user_context.get('available_time', '每周5小时')
        )
        
        # 调用LLM
        llm_response = await self.llm.chat(
            message=prompt,
            context_id=context_id,
            system_prompt=llm_context.system_prompt
        )
        
        # 构建学习路径
        learning_path = llm_context.metadata.get('learning_path', [])
        
        return AssistantResponse(
            answer=llm_response.content,
            answer_type='advice',
            confidence=llm_response.confidence_score,
            context_used={'goal': goal, 'user_id': user_id},
            suggestions=[
                f"我应该先学习{learning_path[0]}吗？" if learning_path else "有哪些入门资源？",
                "需要多长时间才能达到目标？",
                "有什么推荐的练习题目？"
            ]
        )
    
    async def solve_problem(
        self,
        problem: str,
        show_steps: bool = True,
        context_id: Optional[str] = None
    ) -> AssistantResponse:
        """解答数学问题"""
        # 构建上下文
        llm_context = self.context_builder.build_for_problem_solving(problem, show_steps)
        
        # 构建提示词
        prompt = self.prompts.get_problem_solving_prompt(problem)
        
        # 调用LLM
        llm_response = await self.llm.chat(
            message=prompt,
            context_id=context_id,
            system_prompt=llm_context.system_prompt
        )
        
        return AssistantResponse(
            answer=llm_response.content,
            answer_type='problem',
            confidence=llm_response.confidence_score,
            context_used={'problem': problem},
            latex_formulas=llm_response.latex_formulas[:5],
            suggestions=[
                '能解释关键步骤吗？',
                '有没有其他解法？',
                '类似的问题如何求解？'
            ]
        )
    
    async def help_lean_formalization(
        self,
        statement: str,
        context_id: Optional[str] = None
    ) -> AssistantResponse:
        """Lean 4形式化帮助"""
        # 构建上下文
        llm_context = self.context_builder.build_for_lean_formalization(statement)
        
        # 调用LLM
        llm_response = await self.llm.chat(
            message=f"请将以下数学陈述转换为Lean 4代码:\n\n{statement}",
            context_id=context_id,
            system_prompt=llm_context.system_prompt
        )
        
        return AssistantResponse(
            answer=llm_response.content,
            answer_type='lean',
            confidence=llm_response.confidence_score,
            context_used={'statement': statement},
            suggestions=[
                '这个证明需要哪些引理？',
                '如何验证这段代码？',
                '有类似的例子吗？'
            ]
        )
    
    async def _general_qa(
        self,
        question: str,
        context_id: Optional[str] = None
    ) -> AssistantResponse:
        """通用问答（后备方案）"""
        # 尝试使用现有QA系统
        qa_answer = self.knowledge.ask_question(question)
        
        if qa_answer and qa_answer.confidence > 0.6:
            return AssistantResponse(
                answer=qa_answer.text,
                answer_type='general',
                confidence=qa_answer.confidence,
                references=qa_answer.sources[:3]
            )
        
        # 使用LLM直接回答
        llm_response = await self.llm.chat(
            message=question,
            context_id=context_id,
            system_prompt="你是一位专业的数学AI助手。请用清晰、准确的语言回答数学问题。"
        )
        
        return AssistantResponse(
            answer=llm_response.content,
            answer_type='general',
            confidence=llm_response.confidence_score
        )
    
    def _update_stats(self, query_type: str, start_time: datetime):
        """更新统计信息"""
        # 按类型统计
        if query_type not in self._stats['by_type']:
            self._stats['by_type'][query_type] = 0
        self._stats['by_type'][query_type] += 1
        
        # 更新平均响应时间
        elapsed_ms = (datetime.now() - start_time).total_seconds() * 1000
        n = self._stats['total_queries']
        self._stats['avg_response_time_ms'] = (
            (self._stats['avg_response_time_ms'] * (n - 1) + elapsed_ms) / n
        )
    
    def get_stats(self) -> Dict:
        """获取服务统计"""
        return {
            **self._stats,
            'llm_stats': self.llm.get_stats()
        }


# 全局AI助手服务实例
_ai_assistant: Optional[AIAssistantService] = None


def get_ai_assistant() -> AIAssistantService:
    """获取全局AI助手服务实例"""
    global _ai_assistant
    if _ai_assistant is None:
        _ai_assistant = AIAssistantService()
    return _ai_assistant
