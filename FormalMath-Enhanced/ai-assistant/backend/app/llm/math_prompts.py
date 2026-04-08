"""
数学专用提示词模板
"""
from typing import Dict, List, Optional
from dataclasses import dataclass


@dataclass
class MathPromptTemplates:
    """数学提示词模板集合"""
    
    # ========== 概念解释提示词 ==========
    
    CONCEPT_EXPLAIN_BEGINNER = """你是一位耐心的数学导师，正在向初学者解释数学概念。

概念：{concept}

请用以下方式解释：
1. 使用日常生活中的类比
2. 避免过于抽象的符号和公式
3. 提供1-2个简单的例子
4. 解释这个概念为什么重要

请用通俗易懂的中文回答。"""
    
    CONCEPT_EXPLAIN_INTERMEDIATE = """你是一位专业的数学教师，正在向有一定基础的学生解释数学概念。

概念：{concept}
相关概念：{related_concepts}

请用以下方式解释：
1. 给出正式的定义
2. 解释核心性质和定理
3. 提供技术性的例子
4. 说明与其他概念的联系
5. 适当使用LaTeX公式

请用专业的数学语言回答。"""
    
    CONCEPT_EXPLAIN_ADVANCED = """你是一位数学研究者，正在向同行或高级学生解释数学概念。

概念：{concept}
相关概念：{related_concepts}

请用以下方式解释：
1. 给出严格的数学定义
2. 讨论深层性质和推广
3. 提及相关的重要定理
4. 可以涉及形式化表示（Lean 4风格）
5. 指出开放问题和研究方向

请用严谨的数学语言回答。"""
    
    # ========== 证明辅助提示词 ==========
    
    PROOF_HINT_TEMPLATE = """你是一位证明辅助导师，帮助学生理解如何证明数学命题。

命题：{theorem}
已知条件：{conditions}
需要证明：{conclusion}

请提供证明提示，但不要直接给出完整证明：
1. 建议一个证明策略（如反证法、归纳法、构造法等）
2. 指出关键引理或中间步骤
3. 提示可能用到的定理或性质
4. 如果适用，给出证明的大致结构

请用启发式的方式引导学生自己完成证明。"""
    
    PROOF_VERIFICATION_TEMPLATE = """你是一位严谨的数学审阅者，正在检查一个数学证明。

命题：{theorem}
学生证明：
{proof}

请分析这个证明：
1. 证明思路是否正确？
2. 是否有逻辑漏洞或遗漏？
3. 符号使用是否准确？
4. 给出具体的改进建议
5. 如果证明正确，给出肯定评价

请用建设性的语气给出反馈。"""
    
    PROOF_STEP_BY_STEP = """你正在展示一个数学证明的详细步骤。

定理：{theorem}

请按以下结构给出证明：
1. 定理陈述和符号说明
2. 证明思路概述
3. 详细步骤（编号）
4. 关键步骤的解释
5. 结论

每一步都要清晰明了，适当使用LaTeX公式。"""
    
    # ========== 学习建议提示词 ==========
    
    LEARNING_ADVICE_TEMPLATE = """你是一位个性化的数学学习顾问。

学生当前状态：
- 知识水平：{knowledge_level}
- 薄弱环节：{weak_areas}
- 学习目标：{learning_goal}
- 可用时间：{available_time}

请提供个性化的学习建议：
1. 推荐学习路径（概念先后顺序）
2. 推荐学习资源类型
3. 练习题目难度建议
4. 学习方法和技巧
5. 如何克服薄弱环节

请给出具体、可执行的建议。"""
    
    STUDY_PLAN_TEMPLATE = """你正在为学生制定数学学习计划。

学习目标：{goal}
当前水平：{current_level}
目标水平：{target_level}
可用时间：{time_available}
时间跨度：{time_span}

请制定一个详细的学习计划：
1. 分阶段目标
2. 每个阶段的重点概念
3. 推荐的练习和题目
4. 自我检测点
5. 灵活调整建议

计划应该既有挑战性又可实现。"""
    
    # ========== 问题解答提示词 ==========
    
    PROBLEM_SOLVING_TEMPLATE = """你正在帮助学生解决一个数学问题。

问题：{problem}

请按以下步骤解答：
1. 理解问题：重述问题并明确已知和未知
2. 制定策略：说明选择的解题方法
3. 执行求解：详细展示求解过程
4. 验证答案：检查结果的正确性
5. 反思总结：总结关键思路和方法

请使用LaTeX格式表示数学公式。"""
    
    ERROR_ANALYSIS_TEMPLATE = """你正在分析学生解题中的错误。

题目：{problem}
学生解答：
{student_solution}
正确答案：{correct_answer}

请分析错误：
1. 错误类型（概念错误/计算错误/理解错误/其他）
2. 错误的具体位置和原因
3. 如何纠正这个错误
4. 类似的常见错误和预防方法
5. 推荐的相关练习

请用鼓励的语气帮助学生从错误中学习。"""
    
    # ========== Lean 4 相关提示词 ==========
    
    LEAN_FORMALIZATION_TEMPLATE = """你是一位Lean 4形式化专家，帮助将数学概念转换为形式化代码。

数学陈述：{math_statement}

请提供：
1. 对应的Lean 4代码框架
2. 关键tactic的解释
3. 形式化过程中的注意事项
4. 类似定理的参考实现

请确保代码语法正确。"""
    
    LEAN_PROOF_HINT_TEMPLATE = """你正在指导学生在Lean 4中完成证明。

目标：{goal}
当前证明状态：{proof_state}

请提供：
1. 下一步建议的tactic
2. 为什么使用这个tactic
3. 可能的其他策略
4. 相关lemma的提示

请引导学生自己发现证明路径。"""
    
    # ========== 公式相关提示词 ==========
    
    FORMULA_EXPLANATION_TEMPLATE = """你正在解释一个数学公式的含义和用法。

公式：{formula}
上下文：{context}

请解释：
1. 公式中每个符号的含义
2. 公式的数学意义
3. 公式的适用条件
4. 如何记忆和理解这个公式
5. 相关的变式或推广

请使用LaTeX清晰展示公式。"""
    
    FORMULA_DERIVATION_TEMPLATE = """你正在推导一个数学公式。

公式：{formula}
从基本原理出发

请展示：
1. 推导的起点（定义或已知定理）
2. 每一步的推导过程
3. 使用的数学技巧
4. 最终结果

推导应该清晰、严谨。"""
    
    def get_concept_explain_prompt(
        self,
        concept: str,
        level: str = "intermediate",
        related_concepts: Optional[List[str]] = None
    ) -> str:
        """获取概念解释提示词"""
        if level == "beginner":
            return self.CONCEPT_EXPLAIN_BEGINNER.format(concept=concept)
        elif level == "advanced":
            return self.CONCEPT_EXPLAIN_ADVANCED.format(
                concept=concept,
                related_concepts=", ".join(related_concepts or [])
            )
        else:
            return self.CONCEPT_EXPLAIN_INTERMEDIATE.format(
                concept=concept,
                related_concepts=", ".join(related_concepts or [])
            )
    
    def get_proof_hint_prompt(
        self,
        theorem: str,
        conditions: str = "",
        conclusion: str = ""
    ) -> str:
        """获取证明提示提示词"""
        return self.PROOF_HINT_TEMPLATE.format(
            theorem=theorem,
            conditions=conditions,
            conclusion=conclusion
        )
    
    def get_learning_advice_prompt(
        self,
        knowledge_level: str,
        weak_areas: List[str],
        learning_goal: str,
        available_time: str
    ) -> str:
        """获取学习建议提示词"""
        return self.LEARNING_ADVICE_TEMPLATE.format(
            knowledge_level=knowledge_level,
            weak_areas=", ".join(weak_areas),
            learning_goal=learning_goal,
            available_time=available_time
        )
    
    def get_problem_solving_prompt(self, problem: str) -> str:
        """获取问题解答提示词"""
        return self.PROBLEM_SOLVING_TEMPLATE.format(problem=problem)


# 全局提示词模板实例
_math_prompts: Optional[MathPromptTemplates] = None


def get_math_prompts() -> MathPromptTemplates:
    """获取全局提示词模板实例"""
    global _math_prompts
    if _math_prompts is None:
        _math_prompts = MathPromptTemplates()
    return _math_prompts
