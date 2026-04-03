"""
诊断报告生成器
"""

from typing import Dict, List, Any, Optional
from datetime import datetime

from app.models.diagnosis import (
    DiagnosisReport, DiagnosisSession, DiagnosisResponse,
    AbilityAssessment, LearningSuggestion
)
from app.models.question import Question
from app.models.knowledge_graph import KnowledgeGraph, KnowledgeNode
from app.diagnosis.hcd_engine import HCDResult


class ReportGenerator:
    """诊断报告生成器"""
    
    def __init__(self, knowledge_graph: KnowledgeGraph):
        self.knowledge_graph = knowledge_graph
    
    def generate_report(
        self,
        session: DiagnosisSession,
        hcd_result: HCDResult,
        questions: Dict[str, Question]
    ) -> DiagnosisReport:
        """
        生成诊断报告
        
        Args:
            session: 诊断会话
            hcd_result: HCD诊断结果
            questions: 题目字典
            
        Returns:
            DiagnosisReport: 诊断报告
        """
        # 1. 计算统计信息
        stats = self._calculate_statistics(session, questions)
        
        # 2. 生成能力评估
        ability_assessments = self._generate_ability_assessments(hcd_result)
        
        # 3. 生成学习建议
        suggestions = self._generate_learning_suggestions(hcd_result, ability_assessments)
        
        # 4. 生成可视化数据
        visualization_data = self._generate_visualization_data(hcd_result, ability_assessments)
        
        # 5. 创建报告
        report = DiagnosisReport(
            id=f"report_{session.id}",
            diagnosis_id=session.id,
            user_id=session.user_id,
            knowledge_state=hcd_result.knowledge_state,
            ability_level=hcd_result.ability_level,
            ability_assessments=ability_assessments,
            suggestions=suggestions,
            total_questions=stats["total"],
            correct_count=stats["correct"],
            accuracy=stats["accuracy"],
            avg_time_per_question=stats["avg_time"],
            visualization_data=visualization_data
        )
        
        return report
    
    def _calculate_statistics(
        self,
        session: DiagnosisSession,
        questions: Dict[str, Question]
    ) -> Dict[str, Any]:
        """计算统计信息"""
        total = len(session.responses)
        correct = sum(1 for r in session.responses if r.is_correct)
        accuracy = correct / total if total > 0 else 0.0
        
        total_time = sum(r.time_spent for r in session.responses)
        avg_time = total_time / total if total > 0 else 0.0
        
        return {
            "total": total,
            "correct": correct,
            "accuracy": accuracy,
            "avg_time": avg_time,
            "total_time": total_time
        }
    
    def _generate_ability_assessments(
        self,
        hcd_result: HCDResult
    ) -> List[AbilityAssessment]:
        """生成各层次能力评估"""
        assessments = []
        
        level_descriptions = {
            0: {
                "high": "基础概念掌握扎实，能够直观理解数学概念",
                "medium": "基础概念掌握尚可，需要巩固部分基本概念",
                "low": "基础概念薄弱，建议从基础开始系统学习"
            },
            1: {
                "high": "形式化定义和定理掌握良好，具备严格的数学思维",
                "medium": "形式化能力有待提高，需要加强定理证明练习",
                "low": "形式化基础薄弱，建议重点学习定义和定理"
            },
            2: {
                "high": "深入定理和应用能力较强，能解决复杂问题",
                "medium": "应用能力一般，需要更多综合练习",
                "low": "深入内容掌握不足，建议逐步提升难度"
            },
            3: {
                "high": "具备研究能力，能够理解前沿数学问题",
                "medium": "研究意识初步形成，可接触开放问题",
                "low": "研究层内容待探索，建议先夯实基础"
            }
        }
        
        for level in range(4):
            score = hcd_result.ability_level.get(level, 0.0)
            
            # 确定描述级别
            if score >= 0.7:
                desc_level = "high"
                mastered = self._get_mastered_concepts(hcd_result, level, 0.7)
                weak = self._get_weak_concepts(hcd_result, level, 0.6)
            elif score >= 0.4:
                desc_level = "medium"
                mastered = self._get_mastered_concepts(hcd_result, level, 0.7)
                weak = self._get_weak_concepts(hcd_result, level, 0.5)
            else:
                desc_level = "low"
                mastered = self._get_mastered_concepts(hcd_result, level, 0.7)
                weak = self._get_weak_concepts(hcd_result, level, 0.4)
            
            assessment = AbilityAssessment(
                level=level,
                score=score,
                description=level_descriptions[level][desc_level],
                mastered_concepts=mastered,
                weak_concepts=weak
            )
            assessments.append(assessment)
        
        return assessments
    
    def _get_mastered_concepts(
        self,
        hcd_result: HCDResult,
        level: int,
        threshold: float
    ) -> List[str]:
        """获取已掌握的概念"""
        mastered = []
        
        for node_id, mastery in hcd_result.knowledge_state.items():
            if mastery >= threshold:
                node = self.knowledge_graph.nodes.get(node_id)
                if node and node.level == level:
                    mastered.append(node.name)
        
        return mastered[:5]  # 最多返回5个
    
    def _get_weak_concepts(
        self,
        hcd_result: HCDResult,
        level: int,
        threshold: float
    ) -> List[str]:
        """获取薄弱概念"""
        weak = []
        
        for node_id, mastery in hcd_result.knowledge_state.items():
            if mastery < threshold:
                node = self.knowledge_graph.nodes.get(node_id)
                if node and node.level == level:
                    weak.append(node.name)
        
        return weak[:5]  # 最多返回5个
    
    def _generate_learning_suggestions(
        self,
        hcd_result: HCDResult,
        ability_assessments: List[AbilityAssessment]
    ) -> List[LearningSuggestion]:
        """生成学习建议"""
        suggestions = []
        
        # 1. 路径建议
        path_suggestion = self._generate_path_suggestion(hcd_result, ability_assessments)
        if path_suggestion:
            suggestions.append(path_suggestion)
        
        # 2. 方法建议
        method_suggestion = self._generate_method_suggestion(ability_assessments)
        if method_suggestion:
            suggestions.append(method_suggestion)
        
        # 3. 练习建议
        practice_suggestion = self._generate_practice_suggestion(hcd_result, ability_assessments)
        if practice_suggestion:
            suggestions.append(practice_suggestion)
        
        # 4. 针对薄弱环节的建议
        for assessment in ability_assessments:
            if assessment.score < 0.6 and assessment.weak_concepts:
                weak_suggestion = LearningSuggestion(
                    type="weak_area",
                    title=f"L{assessment.level} 薄弱点强化",
                    content=f"重点加强：{', '.join(assessment.weak_concepts[:3])}",
                    priority=5 - assessment.level,  # 低层次优先
                    related_concepts=assessment.weak_concepts,
                    recommended_resources=self._recommend_resources(assessment.level, assessment.weak_concepts)
                )
                suggestions.append(weak_suggestion)
        
        # 按优先级排序
        suggestions.sort(key=lambda x: x.priority)
        
        return suggestions
    
    def _generate_path_suggestion(
        self,
        hcd_result: HCDResult,
        ability_assessments: List[AbilityAssessment]
    ) -> Optional[LearningSuggestion]:
        """生成学习路径建议"""
        # 找到第一个薄弱环节
        target_level = None
        for assessment in ability_assessments:
            if assessment.score < 0.7:
                target_level = assessment.level
                break
        
        if target_level is None:
            target_level = 3  # 全部掌握，建议探索研究层
        
        level_names = ["基础层(L0)", "中级层(L1)", "高级层(L2)", "研究层(L3)"]
        
        content = f"建议重点学习{level_names[target_level]}内容。"
        
        if target_level > 0 and ability_assessments[target_level - 1].score < 0.8:
            content += f"同时巩固{level_names[target_level - 1]}的基础知识。"
        
        weak_concepts = ability_assessments[target_level].weak_concepts
        
        return LearningSuggestion(
            type="learning_path",
            title="推荐学习路径",
            content=content,
            priority=1,
            related_concepts=weak_concepts,
            recommended_resources=self._recommend_resources(target_level, weak_concepts)
        )
    
    def _generate_method_suggestion(
        self,
        ability_assessments: List[AbilityAssessment]
    ) -> Optional[LearningSuggestion]:
        """生成学习方法建议"""
        l0_score = ability_assessments[0].score
        l1_score = ability_assessments[1].score
        
        if l0_score < 0.6:
            method = "从基础开始，通过直观例子和图形化方式理解概念"
            strategies = ["使用思维导图整理概念", "观看教学视频", "做基础练习题"]
        elif l1_score < 0.6:
            method = "加强形式化训练，注重定理证明和严格推导"
            strategies = ["阅读经典教材的证明", "模仿证明步骤", "尝试自己证明简单定理"]
        else:
            method = "深入应用，通过综合题目提升解题能力"
            strategies = ["挑战综合应用题", "学习多种解题方法", "总结解题模式"]
        
        return LearningSuggestion(
            type="learning_method",
            title="学习方法建议",
            content=method,
            priority=2,
            related_concepts=[],
            recommended_resources=[
                {"type": "strategy", "content": s} for s in strategies
            ]
        )
    
    def _generate_practice_suggestion(
        self,
        hcd_result: HCDResult,
        ability_assessments: List[AbilityAssessment]
    ) -> Optional[LearningSuggestion]:
        """生成练习建议"""
        # 找到需要练习的知识点
        practice_concepts = []
        for node_id, mastery in hcd_result.knowledge_state.items():
            if 0.3 <= mastery < 0.8:  # 部分掌握，最需要练习
                node = self.knowledge_graph.nodes.get(node_id)
                if node:
                    practice_concepts.append(node.name)
        
        if not practice_concepts:
            # 如果没有部分掌握的知识点，找薄弱点
            for assessment in ability_assessments:
                if assessment.score < 0.6:
                    practice_concepts.extend(assessment.weak_concepts)
        
        practice_concepts = practice_concepts[:5]
        
        # 确定难度
        avg_ability = sum(a.score for a in ability_assessments) / 4
        if avg_ability < 0.5:
            difficulty = "基础题为主(70%)，少量中等题(30%)"
        elif avg_ability < 0.75:
            difficulty = "中等题为主(60%)，基础题(20%)，难题(20%)"
        else:
            difficulty = "难题为主(50%)，中等题(30%)，挑战题(20%)"
        
        return LearningSuggestion(
            type="practice",
            title="练习建议",
            content=f"推荐难度分布：{difficulty}",
            priority=3,
            related_concepts=practice_concepts,
            recommended_resources=[
                {"type": "frequency", "content": "每天练习30-60分钟"},
                {"type": "quantity", "content": "每天10-15道题目"}
            ]
        )
    
    def _recommend_resources(
        self,
        level: int,
        concepts: List[str]
    ) -> List[Dict[str, Any]]:
        """推荐学习资源"""
        resources = []
        
        level_resource_types = {
            0: ["教材章节", "视频教程", "基础练习"],
            1: ["定理证明", "例题分析", "概念对比"],
            2: ["综合题目", "应用案例", "进阶阅读"],
            3: ["研究论文", "开放问题", "前沿讲座"]
        }
        
        for i, res_type in enumerate(level_resource_types.get(level, ["综合资源"])):
            resources.append({
                "type": res_type,
                "priority": i + 1
            })
        
        return resources
    
    def _generate_visualization_data(
        self,
        hcd_result: HCDResult,
        ability_assessments: List[AbilityAssessment]
    ) -> Dict[str, Any]:
        """生成可视化数据"""
        # 1. 雷达图数据 - 能力水平
        radar_data = {
            "labels": ["L0-基础", "L1-中级", "L2-高级", "L3-研究"],
            "datasets": [{
                "label": "能力水平",
                "data": [hcd_result.ability_level.get(i, 0.0) * 100 for i in range(4)],
                "backgroundColor": "rgba(54, 162, 235, 0.2)",
                "borderColor": "rgba(54, 162, 235, 1)",
            }]
        }
        
        # 2. 知识状态分布
        knowledge_dist = {"high": 0, "medium": 0, "low": 0}
        for mastery in hcd_result.knowledge_state.values():
            if mastery >= 0.7:
                knowledge_dist["high"] += 1
            elif mastery >= 0.4:
                knowledge_dist["medium"] += 1
            else:
                knowledge_dist["low"] += 1
        
        pie_data = {
            "labels": ["掌握良好(≥70%)", "部分掌握(40-70%)", "需加强(<40%)"],
            "datasets": [{
                "data": [knowledge_dist["high"], knowledge_dist["medium"], knowledge_dist["low"]],
                "backgroundColor": ["#4CAF50", "#FFC107", "#F44336"]
            }]
        }
        
        # 3. 层次对比
        level_comparison = {
            "labels": [f"L{i}" for i in range(4)],
            "current": [hcd_result.ability_level.get(i, 0.0) for i in range(4)],
            "target": [0.8, 0.7, 0.6, 0.4],  # 目标水平
        }
        
        return {
            "radar": radar_data,
            "pie": pie_data,
            "comparison": level_comparison,
            "knowledge_state": hcd_result.knowledge_state
        }
