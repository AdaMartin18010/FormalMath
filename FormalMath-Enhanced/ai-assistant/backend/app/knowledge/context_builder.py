"""
上下文构建器
为LLM构建丰富的数学上下文
"""
from typing import Dict, List, Optional, Any
from dataclasses import dataclass, field
import json

from .knowledge_service import KnowledgeService, get_knowledge_service, KnowledgeContext


@dataclass
class LLMContext:
    """用于LLM的上下文"""
    system_prompt: str = ""
    concept_context: List[str] = field(default_factory=list)
    formulas: List[str] = field(default_factory=list)
    references: List[Dict] = field(default_factory=list)
    conversation_history: List[Dict] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)


class ContextBuilder:
    """
    上下文构建器
    根据用户查询构建适合LLM的上下文
    """
    
    def __init__(self, knowledge_service: KnowledgeService = None):
        self.knowledge = knowledge_service or get_knowledge_service()
    
    def build_for_concept_explanation(
        self,
        concept: str,
        level: str = "intermediate",
        user_context: Optional[Dict] = None
    ) -> LLMContext:
        """为概念解释构建上下文"""
        # 获取知识上下文
        knowledge_ctx = self.knowledge.build_knowledge_context(concept)
        
        # 构建系统提示词
        system_prompt = self._build_concept_system_prompt(concept, level, knowledge_ctx)
        
        # 收集概念上下文
        concept_context = []
        for info in knowledge_ctx.concepts:
            concept_context.append(f"{info.name}: {info.definition[:200]}")
            if info.properties:
                concept_context.append(f"主要性质: {', '.join(info.properties[:3])}")
        
        # 收集参考
        references = []
        for doc in knowledge_ctx.documents[:3]:
            references.append({
                'source': doc.source,
                'preview': doc.content[:150],
                'relevance': doc.score
            })
        
        return LLMContext(
            system_prompt=system_prompt,
            concept_context=concept_context,
            formulas=knowledge_ctx.related_formulas[:5],
            references=references,
            metadata={
                'concept': concept,
                'level': level,
                'related_concepts': [c.name for c in knowledge_ctx.concepts[1:]] if len(knowledge_ctx.concepts) > 1 else []
            }
        )
    
    def build_for_proof_hint(
        self,
        theorem: str,
        user_attempt: Optional[str] = None,
        proof_strategy: Optional[str] = None
    ) -> LLMContext:
        """为证明提示构建上下文"""
        # 搜索相关定理和证明
        knowledge_ctx = self.knowledge.build_knowledge_context(theorem)
        
        # 构建系统提示词
        system_prompt = f"""你是一位证明辅助导师，帮助学生理解如何证明数学命题。

当前定理: {theorem}

指导原则：
1. 不要直接给出完整证明，而是提供启发式提示
2. 引导学生自己发现证明路径
3. 提供关键引理和证明策略的建议
4. 如果学生提供了尝试，分析其思路并给出反馈
"""
        
        # 收集相关定理和引理
        related_theorems = []
        for info in knowledge_ctx.concepts:
            related_theorems.extend(info.theorems[:3])
        
        context = LLMContext(
            system_prompt=system_prompt,
            concept_context=[f"相关定理: {t}" for t in related_theorems[:5]],
            formulas=knowledge_ctx.related_formulas[:5],
            metadata={
                'theorem': theorem,
                'user_attempt': user_attempt,
                'proof_strategy': proof_strategy
            }
        )
        
        # 如果用户提供了尝试，添加到上下文
        if user_attempt:
            context.conversation_history.append({
                'role': 'user',
                'content': f"我的证明尝试:\n{user_attempt}"
            })
        
        return context
    
    def build_for_learning_advice(
        self,
        goal: str,
        user_id: Optional[str] = None,
        knowledge_service=None
    ) -> LLMContext:
        """为学习建议构建上下文"""
        # 获取用户诊断信息
        user_context = {}
        if user_id:
            user_context = self.knowledge.get_diagnosis_context(user_id)
        
        # 搜索目标相关的知识
        knowledge_ctx = self.knowledge.build_knowledge_context(goal)
        
        # 构建系统提示词
        system_prompt = f"""你是一位个性化的数学学习顾问。

学习目标: {goal}
学生水平: {user_context.get('knowledge_level', 'intermediate')}
薄弱环节: {', '.join(user_context.get('weak_areas', [])[:3])}

请提供：
1. 具体的学习路径建议
2. 推荐的资源和练习
3. 克服薄弱环节的方法
4. 学习时间安排建议
5. 进度检查点
"""
        
        # 构建学习路径上下文
        learning_context = []
        if knowledge_ctx.learning_path:
            learning_context.append(f"建议学习顺序: {' → '.join(knowledge_ctx.learning_path[:5])}")
        
        for info in knowledge_ctx.concepts:
            if info.prerequisites:
                learning_context.append(f"{info.name}的先修: {', '.join(info.prerequisites[:3])}")
        
        return LLMContext(
            system_prompt=system_prompt,
            concept_context=learning_context,
            metadata={
                'goal': goal,
                'user_context': user_context,
                'learning_path': knowledge_ctx.learning_path
            }
        )
    
    def build_for_problem_solving(
        self,
        problem: str,
        show_steps: bool = True
    ) -> LLMContext:
        """为问题解答构建上下文"""
        # 分析问题涉及的概念
        knowledge_ctx = self.knowledge.build_knowledge_context(problem)
        
        system_prompt = f"""你正在帮助学生解决一个数学问题。

请按以下步骤解答：
1. 理解问题：重述问题并明确已知和未知
2. 制定策略：说明选择的解题方法
3. 执行求解：详细展示求解过程
4. 验证答案：检查结果的正确性
5. 反思总结：总结关键思路和方法

{'请提供详细的逐步解答。' if show_steps else '请给出简洁的解答。'}
"""
        
        # 收集相关公式和定理
        formulas = knowledge_ctx.related_formulas[:5]
        theorems = []
        for info in knowledge_ctx.concepts:
            theorems.extend(info.theorems[:2])
        
        return LLMContext(
            system_prompt=system_prompt,
            concept_context=[f"相关定理: {t}" for t in theorems],
            formulas=formulas,
            metadata={
                'problem': problem,
                'related_concepts': [c.name for c in knowledge_ctx.concepts[:3]]
            }
        )
    
    def build_for_lean_formalization(
        self,
        math_statement: str
    ) -> LLMContext:
        """为Lean 4形式化构建上下文"""
        system_prompt = """你是一位Lean 4形式化专家。

请提供：
1. 对应的Lean 4代码框架
2. 关键tactic的解释
3. 形式化过程中的注意事项
4. 类似定理的参考实现

请确保代码语法正确，使用mathlib4风格。
"""
        
        # 分析数学陈述涉及的概念
        knowledge_ctx = self.knowledge.build_knowledge_context(math_statement)
        
        return LLMContext(
            system_prompt=system_prompt,
            concept_context=[f"相关概念: {c.name}" for c in knowledge_ctx.concepts[:3]],
            formulas=knowledge_ctx.related_formulas[:3],
            metadata={
                'statement': math_statement,
                'target': 'lean4'
            }
        )
    
    def _build_concept_system_prompt(
        self,
        concept: str,
        level: str,
        knowledge_ctx: KnowledgeContext
    ) -> str:
        """构建概念解释的系统提示词"""
        level_guidance = {
            'beginner': '用通俗易懂的语言解释，使用日常类比，避免过于抽象的符号。',
            'intermediate': '给出标准的技术性解释，包含必要的定义和定理，适当使用LaTeX。',
            'advanced': '提供严格的数学定义和深层性质，可以涉及形式化表示和研究前沿。'
        }
        
        guidance = level_guidance.get(level, level_guidance['intermediate'])
        
        prompt = f"""你是一位专业的数学AI助手，正在解释概念：{concept}

难度级别：{level}
指导原则：{guidance}

"""
        
        # 添加相关概念信息
        if knowledge_ctx.concepts:
            main_concept = knowledge_ctx.concepts[0]
            if main_concept.prerequisites:
                prompt += f"\n先修概念：{', '.join(main_concept.prerequisites[:3])}"
            if main_concept.related_concepts:
                prompt += f"\n相关概念：{', '.join(main_concept.related_concepts[:3])}"
        
        prompt += "\n\n对于数学公式，请使用LaTeX格式（$行内$，$$独立$）。"
        
        return prompt
    
    def context_to_prompt(self, context: LLMContext) -> str:
        """将上下文转换为提示词字符串"""
        parts = [context.system_prompt]
        
        if context.concept_context:
            parts.append("\n相关概念信息：")
            for ctx in context.concept_context:
                parts.append(f"- {ctx}")
        
        if context.formulas:
            parts.append("\n相关公式：")
            for formula in context.formulas:
                parts.append(f"- ${formula}$")
        
        return '\n'.join(parts)
    
    def format_for_api(self, context: LLMContext) -> Dict[str, Any]:
        """格式化为API响应"""
        return {
            'system_prompt': context.system_prompt,
            'concept_context': context.concept_context,
            'formulas': context.formulas,
            'references': context.references,
            'metadata': context.metadata
        }


# 全局上下文构建器实例
_context_builder: Optional[ContextBuilder] = None


def get_context_builder() -> ContextBuilder:
    """获取全局上下文构建器实例"""
    global _context_builder
    if _context_builder is None:
        _context_builder = ContextBuilder()
    return _context_builder
