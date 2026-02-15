"""
认知诊断系统 - 诊断引擎模块

基于 HCD (Hierarchical Cognitive Diagnosis) 框架
实现知识状态估计、能力水平评估和学习建议生成
"""

from dataclasses import dataclass, field
from typing import List, Dict, Tuple, Optional
from enum import Enum
import math
from collections import defaultdict

from questions_bank import (
    Question, QuestionBank, KnowledgeLevel, MathBranch, 
    QuestionType, get_question_bank
)


class ResponseType(Enum):
    """答题响应类型"""
    CORRECT = "正确"
    INCORRECT = "错误"
    PARTIAL = "部分正确"
    UNANSWERED = "未作答"


@dataclass
class Response:
    """答题响应"""
    question_id: str
    answer: str
    is_correct: bool
    time_spent: int  # 答题时间（秒）
    response_type: ResponseType = ResponseType.CORRECT
    confidence: float = 1.0  # 答题信心度 (0-1)


@dataclass
class KnowledgeState:
    """知识状态"""
    concept_mastery: Dict[str, float]  # 各概念掌握程度 (0-1)
    level_ability: Dict[int, float]    # 各层次能力 (0-1)
    branch_ability: Dict[str, float]   # 各分支能力 (0-1)
    overall_ability: float = 0.0       # 整体能力
    
    def get_weak_concepts(self, threshold: float = 0.5) -> List[str]:
        """获取薄弱概念（掌握度低于阈值）"""
        return [
            concept for concept, mastery in self.concept_mastery.items()
            if mastery < threshold
        ]
    
    def get_strong_concepts(self, threshold: float = 0.7) -> List[str]:
        """获取强项概念（掌握度高于阈值）"""
        return [
            concept for concept, mastery in self.concept_mastery.items()
            if mastery > threshold
        ]


@dataclass
class Suggestion:
    """学习建议"""
    type: str                          # 建议类型
    content: str                       # 建议内容
    priority: int                      # 优先级 (1-5)
    related_concepts: List[str]        # 相关概念
    resources: List[str]               # 推荐资源
    estimated_time: int                # 预计学习时间（小时）


@dataclass
class DiagnosisResult:
    """诊断结果"""
    student_id: str
    knowledge_state: KnowledgeState
    suggestions: List[Suggestion]
    raw_score: float                   # 原始得分 (0-1)
    diagnosis_time: str                # 诊断时间
    
    def get_summary(self) -> str:
        """获取诊断摘要"""
        lines = [
            f"学生ID: {self.student_id}",
            f"原始得分: {self.raw_score:.2%}",
            f"整体能力: {self.knowledge_state.overall_ability:.2%}",
            "",
            "各层次能力:",
        ]
        for level, ability in sorted(self.knowledge_state.level_ability.items()):
            level_name = ["L0-基础", "L1-理解", "L2-应用", "L3-创新"][level]
            lines.append(f"  {level_name}: {ability:.2%}")
        
        lines.extend([
            "",
            "薄弱概念:",
        ])
        weak = self.knowledge_state.get_weak_concepts()
        if weak:
            for concept in weak[:5]:
                mastery = self.knowledge_state.concept_mastery[concept]
                lines.append(f"  - {concept}: {mastery:.2%}")
        else:
            lines.append("  无")
        
        return "\n".join(lines)


class HCDAlgorithm:
    """
    HCD (Hierarchical Cognitive Diagnosis) 算法
    
    基于层次约束感知的认知诊断框架
    """
    
    def __init__(self, question_bank: QuestionBank):
        self.bank = question_bank
        self.constraints = self._build_hierarchy_constraints()
        
        # 模型参数
        self.guess_prob = 0.25  # 猜测概率（选择题）
        self.slip_prob = 0.1    # 失误概率
        self.learning_rate = 0.1  # 学习率
    
    def _build_hierarchy_constraints(self) -> Dict:
        """构建层次约束关系"""
        # L0 -> L1 -> L2 -> L3 的先修约束
        constraints = {
            "prerequisites": {
                KnowledgeLevel.L1: [KnowledgeLevel.L0],
                KnowledgeLevel.L2: [KnowledgeLevel.L1],
                KnowledgeLevel.L3: [KnowledgeLevel.L2],
            },
            "constraint_strength": {
                (KnowledgeLevel.L0, KnowledgeLevel.L1): 0.8,
                (KnowledgeLevel.L1, KnowledgeLevel.L2): 0.7,
                (KnowledgeLevel.L2, KnowledgeLevel.L3): 0.6,
            }
        }
        return constraints
    
    def diagnose(
        self,
        student_id: str,
        responses: List[Response]
    ) -> DiagnosisResult:
        """
        执行认知诊断
        
        Args:
            student_id: 学生ID
            responses: 答题响应列表
        
        Returns:
            诊断结果
        """
        # 1. 估计知识状态
        knowledge_state = self._estimate_knowledge_state(responses)
        
        # 2. 应用层次约束
        knowledge_state = self._apply_hierarchy_constraints(knowledge_state)
        
        # 3. 评估能力水平
        knowledge_state = self._assess_ability_levels(knowledge_state, responses)
        
        # 4. 生成学习建议
        suggestions = self._generate_suggestions(knowledge_state)
        
        # 5. 计算原始得分
        raw_score = self._calculate_raw_score(responses)
        
        # 6. 构建诊断结果
        from datetime import datetime
        result = DiagnosisResult(
            student_id=student_id,
            knowledge_state=knowledge_state,
            suggestions=suggestions,
            raw_score=raw_score,
            diagnosis_time=datetime.now().isoformat()
        )
        
        return result
    
    def _estimate_knowledge_state(self, responses: List[Response]) -> KnowledgeState:
        """
        估计知识状态
        
        使用改进的 DINA-like 模型结合 IRT 思想
        """
        # 收集概念-答题数据
        concept_responses = defaultdict(list)
        
        for resp in responses:
            question = self.bank.get_question(resp.question_id)
            if question:
                for concept in question.concepts:
                    concept_responses[concept].append({
                        "correct": resp.is_correct,
                        "difficulty": question.difficulty,
                        "level": question.knowledge_level.value,
                        "weight": self._get_question_weight(question)
                    })
        
        # 估计各概念掌握度
        concept_mastery = {}
        for concept, data_list in concept_responses.items():
            mastery = self._calculate_concept_mastery(data_list)
            concept_mastery[concept] = mastery
        
        # 初始化层次和分支能力
        level_ability = {i: 0.0 for i in range(4)}
        branch_ability = {branch.value: 0.0 for branch in MathBranch}
        
        return KnowledgeState(
            concept_mastery=concept_mastery,
            level_ability=level_ability,
            branch_ability=branch_ability,
            overall_ability=0.0
        )
    
    def _get_question_weight(self, question: Question) -> float:
        """获取题目权重"""
        # 根据题型和层次分配权重
        weights = {
            QuestionType.CONCEPT: 1.0,
            QuestionType.CALCULATION: 1.2,
            QuestionType.THEOREM: 1.5,
            QuestionType.METHOD: 1.5,
            QuestionType.PROOF: 2.0,
        }
        base_weight = weights.get(question.question_type, 1.0)
        
        # 层次系数
        level_factor = 1 + question.knowledge_level.value * 0.2
        
        return base_weight * level_factor
    
    def _calculate_concept_mastery(self, data_list: List[Dict]) -> float:
        """计算概念掌握度"""
        if not data_list:
            return 0.0
        
        total_weight = 0.0
        weighted_score = 0.0
        
        for data in data_list:
            weight = data["weight"]
            # 考虑难度的正确率调整
            difficulty = data["difficulty"]
            
            # 预期正确率 = (掌握度 * (1-失误) + (1-掌握度) * 猜测)
            # 简化模型：直接根据答题情况估计
            if data["correct"]:
                # 正确：掌握度应较高，但需考虑猜测
                score = min(1.0, 0.7 + (1 - difficulty) * 0.3)
            else:
                # 错误：掌握度应较低，但需考虑失误
                score = max(0.0, 0.3 - difficulty * 0.3)
            
            weighted_score += score * weight
            total_weight += weight
        
        mastery = weighted_score / total_weight if total_weight > 0 else 0.0
        return min(1.0, max(0.0, mastery))
    
    def _apply_hierarchy_constraints(
        self, 
        knowledge_state: KnowledgeState
    ) -> KnowledgeState:
        """
        应用层次约束
        
        L(n) 能力不应显著超过 L(n-1) 能力
        """
        # 计算各层次平均掌握度
        level_mastery = defaultdict(list)
        
        # 获取所有题目，建立概念到层次的映射
        for question in self.bank.get_all_questions():
            for concept in question.concepts:
                if concept in knowledge_state.concept_mastery:
                    level_mastery[question.knowledge_level.value].append(
                        knowledge_state.concept_mastery[concept]
                    )
        
        # 计算各层次能力
        for level in range(4):
            if level_mastery[level]:
                avg_mastery = sum(level_mastery[level]) / len(level_mastery[level])
                knowledge_state.level_ability[level] = avg_mastery
        
        # 应用约束：高层次能力受限于低层次能力
        for level in range(1, 4):
            lower_ability = knowledge_state.level_ability[level - 1]
            current_ability = knowledge_state.level_ability[level]
            
            # 约束强度
            strength = self.constraints["constraint_strength"].get(
                (KnowledgeLevel(level - 1), KnowledgeLevel(level)), 0.7
            )
            
            # 应用约束：当前层次能力不超过低层次能力 + (1-约束强度)
            max_allowed = lower_ability + (1 - strength)
            knowledge_state.level_ability[level] = min(current_ability, max_allowed)
        
        return knowledge_state
    
    def _assess_ability_levels(
        self,
        knowledge_state: KnowledgeState,
        responses: List[Response]
    ) -> KnowledgeState:
        """评估各维度能力水平"""
        # 1. 重新计算整体能力（加权平均）
        level_weights = [0.2, 0.3, 0.3, 0.2]  # L0-L3 权重
        weighted_sum = sum(
            knowledge_state.level_ability[i] * level_weights[i]
            for i in range(4)
        )
        knowledge_state.overall_ability = weighted_sum
        
        # 2. 计算各分支能力
        branch_scores = defaultdict(lambda: defaultdict(list))
        
        for resp in responses:
            question = self.bank.get_question(resp.question_id)
            if question:
                score = 1.0 if resp.is_correct else 0.0
                weight = self._get_question_weight(question)
                branch_scores[question.math_branch.value][question.knowledge_level.value].append({
                    "score": score,
                    "weight": weight
                })
        
        for branch, level_data in branch_scores.items():
            total_weight = 0.0
            weighted_score = 0.0
            
            for level, scores in level_data.items():
                for item in scores:
                    weighted_score += item["score"] * item["weight"]
                    total_weight += item["weight"]
            
            if total_weight > 0:
                knowledge_state.branch_ability[branch] = weighted_score / total_weight
        
        return knowledge_state
    
    def _generate_suggestions(self, knowledge_state: KnowledgeState) -> List[Suggestion]:
        """生成学习建议"""
        suggestions = []
        
        # 1. 识别薄弱环节
        weak_concepts = knowledge_state.get_weak_concepts(threshold=0.5)
        
        # 2. 按层次分析
        for level in range(4):
            ability = knowledge_state.level_ability[level]
            level_names = ["L0-基础", "L1-理解", "L2-应用", "L3-创新"]
            
            if ability < 0.4:
                priority = 5 - level  # 低层次问题优先级更高
                suggestions.append(Suggestion(
                    type="基础强化",
                    content=f"{level_names[level]}层次能力较弱({ability:.0%})，建议系统复习该层次内容",
                    priority=priority,
                    related_concepts=self._get_level_concepts(level, weak_concepts),
                    resources=self._recommend_resources(level, "基础"),
                    estimated_time=10 + level * 5
                ))
            elif ability < 0.6:
                suggestions.append(Suggestion(
                    type="能力提升",
                    content=f"{level_names[level]}层次有提升空间，建议针对性练习",
                    priority=3,
                    related_concepts=self._get_level_concepts(level, weak_concepts),
                    resources=self._recommend_resources(level, "进阶"),
                    estimated_time=5 + level * 3
                ))
        
        # 3. 分支能力分析
        weak_branches = [
            (branch, ability) for branch, ability in knowledge_state.branch_ability.items()
            if ability < 0.5
        ]
        
        for branch, ability in sorted(weak_branches, key=lambda x: x[1])[:3]:
            suggestions.append(Suggestion(
                type="分支强化",
                content=f"{branch}分支能力较弱({ability:.0%})，建议加强该领域学习",
                priority=3,
                related_concepts=[c for c in weak_concepts if self._is_in_branch(c, branch)],
                resources=self._recommend_branch_resources(branch),
                estimated_time=8
            ))
        
        # 4. 学习路径建议
        suggestions.extend(self._generate_learning_path_suggestions(knowledge_state))
        
        # 按优先级排序
        suggestions.sort(key=lambda x: x.priority, reverse=True)
        
        return suggestions
    
    def _get_level_concepts(self, level: int, weak_concepts: List[str]) -> List[str]:
        """获取指定层次的薄弱概念"""
        level_concepts = []
        for question in self.bank.get_questions_by_level(KnowledgeLevel(level)):
            for concept in question.concepts:
                if concept in weak_concepts and concept not in level_concepts:
                    level_concepts.append(concept)
        return level_concepts[:5]
    
    def _is_in_branch(self, concept: str, branch: str) -> bool:
        """判断概念是否属于某分支"""
        for question in self.bank.get_questions_by_concept(concept):
            if question.math_branch.value == branch:
                return True
        return False
    
    def _recommend_resources(self, level: int, resource_type: str) -> List[str]:
        """推荐学习资源"""
        resources = {
            0: {
                "基础": ["《数学分析教程》(上) 第1-3章", "3Blue1Brown 微积分系列", "Khan Academy 基础数学"],
                "进阶": ["《数学分析》(卓里奇) 相关章节", "MIT 18.01 单变量微积分"]
            },
            1: {
                "基础": ["《实变函数论》", "《点集拓扑学》基础", "《近世代数》群论部分"],
                "进阶": ["《数学分析》(卓里奇)", "《代数学引论》(柯斯特利金)"]
            },
            2: {
                "基础": ["《实分析与复分析》(Rudin)", "《代数拓扑》基础", "《微分几何》"],
                "进阶": ["《泛函分析》(Rudin)", "《交换代数》(Atiyah)"]
            },
            3: {
                "基础": ["《集合论》(Jech)", "《数理逻辑》(Shoenfield)", "研究生前沿课题阅读"],
                "进阶": ["最新研究论文", "学术研讨会", "导师指导的专题研究"]
            }
        }
        return resources.get(level, {}).get(resource_type, ["参考 FormalMath 知识库相关文档"])
    
    def _recommend_branch_resources(self, branch: str) -> List[str]:
        """推荐分支资源"""
        branch_resources = {
            "代数": ["《代数学引论》(柯斯特利金)", "《近世代数》(熊全淹)", "FormalMath/代数/"],
            "数学分析": ["《数学分析》(卓里奇)", "《数学分析教程》(常庚哲)", "FormalMath/分析/"],
            "几何": ["《微分几何》(陈省身)", "《微分几何》(Do Carmo)", "FormalMath/几何/"],
            "拓扑": ["《点集拓扑学》(熊金城)", "《代数拓扑》(Hatcher)", "FormalMath/拓扑/"],
            "数理逻辑": ["《数理逻辑》(汪芳庭)", "《Set Theory》(Jech)", "FormalMath/逻辑/"],
            "数论": ["《初等数论》(潘承洞)", "《解析数论》(Apostol)", "FormalMath/数论/"],
            "概率论": ["《概率论基础》(李贤平)", "《概率论》(Billingsley)", "FormalMath/概率/"],
            "线性代数": ["《线性代数》(李炯生)", "《线性代数应该这样学》", "FormalMath/线性代数/"],
        }
        return branch_resources.get(branch, ["FormalMath 知识库相关章节"])
    
    def _generate_learning_path_suggestions(
        self, 
        knowledge_state: KnowledgeState
    ) -> List[Suggestion]:
        """生成学习路径建议"""
        suggestions = []
        
        # 找到最高可学习层次
        current_level = 0
        for level in range(4):
            if knowledge_state.level_ability[level] >= 0.6:
                current_level = level + 1
        
        current_level = min(current_level, 3)
        
        level_names = ["L0-基础", "L1-理解", "L2-应用", "L3-创新"]
        
        suggestions.append(Suggestion(
            type="学习路径",
            content=f"建议从 {level_names[current_level]} 层次开始，逐步向更高层次推进",
            priority=4,
            related_concepts=[],
            resources=[f"FormalMath {level_names[current_level]} 学习路径"],
            estimated_time=20
        ))
        
        # 先修概念建议
        if current_level > 0:
            prereq_level = current_level - 1
            if knowledge_state.level_ability[prereq_level] < 0.8:
                suggestions.append(Suggestion(
                    type="先修巩固",
                    content=f"在学习{level_names[current_level]}前，建议巩固{level_names[prereq_level]}至80%以上",
                    priority=5,
                    related_concepts=[],
                    resources=[f"{level_names[prereq_level]} 复习指南"],
                    estimated_time=15
                ))
        
        return suggestions
    
    def _calculate_raw_score(self, responses: List[Response]) -> float:
        """计算原始得分"""
        if not responses:
            return 0.0
        
        correct_count = sum(1 for r in responses if r.is_correct)
        return correct_count / len(responses)


class DiagnosisEngine:
    """诊断引擎主类"""
    
    def __init__(self, question_bank: Optional[QuestionBank] = None):
        self.bank = question_bank or get_question_bank()
        self.algorithm = HCDAlgorithm(self.bank)
    
    def run_diagnosis(
        self,
        student_id: str,
        responses: List[Response]
    ) -> DiagnosisResult:
        """运行诊断"""
        return self.algorithm.diagnose(student_id, responses)
    
    def quick_diagnosis(
        self,
        student_id: str,
        answers: Dict[str, Tuple[str, bool]]  # {question_id: (answer, is_correct)}
    ) -> DiagnosisResult:
        """
        快速诊断接口
        
        Args:
            student_id: 学生ID
            answers: 简化的答题数据
        """
        responses = []
        for qid, (answer, is_correct) in answers.items():
            responses.append(Response(
                question_id=qid,
                answer=answer,
                is_correct=is_correct,
                time_spent=300  # 默认5分钟
            ))
        
        return self.run_diagnosis(student_id, responses)


if __name__ == "__main__":
    # 测试诊断引擎
    print("=" * 60)
    print("认知诊断引擎测试")
    print("=" * 60)
    
    bank = get_question_bank()
    engine = DiagnosisEngine(bank)
    
    # 模拟一些答题数据
    test_responses = [
        Response("ALG_L0_001", "D", True, 120),
        Response("ALG_L0_002", "B", True, 150),
        Response("ANA_L0_001", "B", True, 100),
        Response("ANA_L0_002", "A", True, 180),
        Response("LALG_L0_001", "A", True, 200),
        Response("ALG_L1_002", "A", True, 250),
        Response("ANA_L1_002", "D", True, 180),
        Response("LALG_L1_002", "D", True, 300),
        Response("PROB_L1_001", "A", False, 240),
        Response("ANA_L2_002", "B", False, 600),
        Response("TOP_L2_002", "B", False, 300),
        Response("LOG_L3_001", "A", True, 180),
    ]
    
    result = engine.run_diagnosis("test_student_001", test_responses)
    
    print("\n" + result.get_summary())
    
    print("\n" + "=" * 60)
    print("学习建议:")
    print("=" * 60)
    
    for i, suggestion in enumerate(result.suggestions[:5], 1):
        print(f"\n[{i}] {suggestion.type} (优先级: {suggestion.priority})")
        print(f"    内容: {suggestion.content}")
        print(f"    相关概念: {', '.join(suggestion.related_concepts) if suggestion.related_concepts else '无'}")
        print(f"    预计时间: {suggestion.estimated_time} 小时")
