#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath 内容质量评估系统
Content Quality Assessment System for FormalMath

功能：自动化评估数学文档的内容质量
作者：FormalMath AI
版本：1.0.0
"""

import re
import json
import os
from pathlib import Path
from dataclasses import dataclass, field, asdict
from typing import Dict, List, Tuple, Optional, Set
from enum import Enum
import math


class QualityLevel(Enum):
    """质量等级"""
    EXCELLENT = 5    # 优秀
    GOOD = 4         # 良好
    ACCEPTABLE = 3   # 可接受
    NEEDS_IMPROVEMENT = 2  # 需改进
    POOR = 1         # 差


@dataclass
class CompletenessMetrics:
    """完整性指标"""
    has_concept_definition: bool = False
    has_theorem_proof: bool = False
    has_examples: bool = False
    has_references: bool = False
    has_msc_code: bool = False
    concept_coverage_score: float = 0.0
    theorem_count: int = 0
    proof_count: int = 0
    example_count: int = 0
    missing_elements: List[str] = field(default_factory=list)
    
    @property
    def overall_score(self) -> float:
        """计算完整性总分"""
        scores = [
            1.0 if self.has_concept_definition else 0.0,
            1.0 if self.has_theorem_proof else 0.0,
            1.0 if self.has_examples else 0.0,
            0.5 if self.has_references else 0.0,
            0.5 if self.has_msc_code else 0.0,
            min(self.concept_coverage_score, 1.0),
            min(self.theorem_count / 3, 1.0),
            min(self.proof_count / 3, 1.0),
            min(self.example_count / 3, 1.0)
        ]
        return sum(scores) / len(scores) * 100


@dataclass
class AccuracyMetrics:
    """准确性指标"""
    math_formula_syntax_errors: int = 0
    citation_errors: int = 0
    broken_links: List[str] = field(default_factory=list)
    inconsistent_notations: List[str] = field(default_factory=list)
    logic_gaps: List[str] = field(default_factory=list)
    
    @property
    def overall_score(self) -> float:
        """计算准确性总分"""
        error_count = (
            self.math_formula_syntax_errors +
            self.citation_errors +
            len(self.broken_links) +
            len(self.inconsistent_notations) +
            len(self.logic_gaps)
        )
        return max(0, 100 - error_count * 5)


@dataclass
class ReadabilityMetrics:
    """可读性指标"""
    avg_sentence_length: float = 0.0
    avg_paragraph_length: float = 0.0
    complex_word_ratio: float = 0.0
    heading_structure_score: float = 0.0
    code_block_ratio: float = 0.0
    formula_density: float = 0.0
    
    @property
    def overall_score(self) -> float:
        """计算可读性总分"""
        # 句子长度评分（理想：15-25字）
        sentence_score = 100 - abs(self.avg_sentence_length - 20) * 2
        sentence_score = max(0, min(100, sentence_score))
        
        # 段落长度评分（理想：3-5句）
        para_score = 100 - abs(self.avg_paragraph_length - 4) * 10
        para_score = max(0, min(100, para_score))
        
        # 复杂度评分（理想：10-20%）
        complex_score = 100 - abs(self.complex_word_ratio - 0.15) * 200
        complex_score = max(0, min(100, complex_score))
        
        # 结构评分
        structure_score = self.heading_structure_score * 100
        
        return (sentence_score + para_score + complex_score + structure_score) / 4


@dataclass
class InternationalizationMetrics:
    """国际化指标"""
    has_english_terms: bool = False
    term_consistency_score: float = 0.0
    cultural_adaptation_score: float = 0.0
    translation_completeness: float = 0.0
    inconsistent_translations: List[str] = field(default_factory=list)
    
    @property
    def overall_score(self) -> float:
        """计算国际化总分"""
        scores = [
            1.0 if self.has_english_terms else 0.5,
            self.term_consistency_score,
            self.cultural_adaptation_score,
            self.translation_completeness
        ]
        return sum(scores) / len(scores) * 100


@dataclass
class LearningEffectMetrics:
    """学习效果预测指标"""
    estimated_difficulty: str = "unknown"  # beginner, intermediate, advanced
    estimated_study_time: int = 0  # 分钟
    mastery_probability: float = 0.0
    prerequisite_clarity: float = 0.0
    exercise_diversity: float = 0.0
    
    @property
    def overall_score(self) -> float:
        """计算学习效果总分"""
        return (self.prerequisite_clarity * 50 + 
                self.exercise_diversity * 50)


@dataclass
class QualityAssessmentResult:
    """质量评估结果"""
    file_path: str
    file_name: str
    completeness: CompletenessMetrics
    accuracy: AccuracyMetrics
    readability: ReadabilityMetrics
    internationalization: InternationalizationMetrics
    learning_effect: LearningEffectMetrics
    overall_score: float = 0.0
    quality_level: str = ""
    recommendations: List[str] = field(default_factory=list)
    issues: List[Dict] = field(default_factory=list)
    
    def calculate_overall(self):
        """计算总体评分"""
        weights = {
            'completeness': 0.25,
            'accuracy': 0.25,
            'readability': 0.20,
            'internationalization': 0.15,
            'learning_effect': 0.15
        }
        
        self.overall_score = (
            self.completeness.overall_score * weights['completeness'] +
            self.accuracy.overall_score * weights['accuracy'] +
            self.readability.overall_score * weights['readability'] +
            self.internationalization.overall_score * weights['internationalization'] +
            self.learning_effect.overall_score * weights['learning_effect']
        )
        
        # 确定质量等级
        if self.overall_score >= 90:
            self.quality_level = "EXCELLENT"
        elif self.overall_score >= 80:
            self.quality_level = "GOOD"
        elif self.overall_score >= 60:
            self.quality_level = "ACCEPTABLE"
        elif self.overall_score >= 40:
            self.quality_level = "NEEDS_IMPROVEMENT"
        else:
            self.quality_level = "POOR"


class ContentQualityAssessor:
    """内容质量评估器"""
    
    def __init__(self, project_root: str = "."):
        self.project_root = Path(project_root)
        self.results: List[QualityAssessmentResult] = []
        
        # 数学术语词典
        self.math_terms = self._load_math_terms()
        
        # 常见数学符号模式
        self.formula_patterns = [
            r'\$[^$]+\$',  # 行内公式
            r'\$\$[^$]+\$\$',  # 行间公式
            r'\\\([^)]+\\\)',  # \( \) 格式
            r'\\\[[^\]]+\\\]',  # \[ \] 格式
        ]
        
    def _load_math_terms(self) -> Set[str]:
        """加载数学术语词典"""
        return {
            '定理', 'lemma', 'proposition', 'corollary',
            '证明', 'proof', '定义', 'definition',
            '例子', 'example', 'remark', 'note',
            '公理', 'axiom', '假设', 'hypothesis',
            '引理', 'lemma', '命题', 'proposition'
        }
    
    def assess_file(self, file_path: str) -> QualityAssessmentResult:
        """评估单个文件"""
        path = Path(file_path)
        content = path.read_text(encoding='utf-8')
        
        result = QualityAssessmentResult(
            file_path=str(path),
            file_name=path.name,
            completeness=self._assess_completeness(content),
            accuracy=self._assess_accuracy(content),
            readability=self._assess_readability(content),
            internationalization=self._assess_internationalization(content),
            learning_effect=self._assess_learning_effect(content)
        )
        
        result.calculate_overall()
        result.recommendations = self._generate_recommendations(result)
        result.issues = self._extract_issues(result)
        
        return result
    
    def _assess_completeness(self, content: str) -> CompletenessMetrics:
        """评估完整性"""
        metrics = CompletenessMetrics()
        
        # 检查概念定义
        metrics.has_concept_definition = bool(
            re.search(r'#{1,3}.*(?:定义|definition|概念|concept)', content, re.I)
        )
        
        # 检查定理证明
        theorem_pattern = r'(?:定理|theorem|lemma|引理|proposition|命题)'
        metrics.has_theorem_proof = bool(
            re.search(theorem_pattern, content, re.I) and
            re.search(r'(?:证明|proof)', content, re.I)
        )
        
        # 检查示例
        metrics.has_examples = bool(
            re.search(r'#{1,3}.*(?:例子|example|示例)', content, re.I)
        )
        
        # 检查引用
        metrics.has_references = bool(
            re.search(r'#{1,3}.*(?:参考|reference|文献|bibliography)', content, re.I) or
            re.search(r'\[\^?\d+\]', content)
        )
        
        # 检查MSC编码
        metrics.has_msc_code = bool(
            re.search(r'msc_primary|MSC| Mathematics Subject Classification', content, re.I)
        )
        
        # 统计数量
        metrics.theorem_count = len(re.findall(
            r'(?:定理|theorem)\s*\d*[.:]?\s*', content, re.I
        ))
        metrics.proof_count = len(re.findall(
            r'(?:证明|proof)[:：]', content, re.I
        ))
        metrics.example_count = len(re.findall(
            r'(?:例子|example)\s*\d*[.:]?\s*', content, re.I
        ))
        
        # 计算概念覆盖度
        found_terms = sum(1 for term in self.math_terms if term in content.lower())
        metrics.concept_coverage_score = found_terms / len(self.math_terms)
        
        # 识别缺失元素
        if not metrics.has_concept_definition:
            metrics.missing_elements.append("概念定义")
        if not metrics.has_theorem_proof:
            metrics.missing_elements.append("定理证明")
        if not metrics.has_examples:
            metrics.missing_elements.append("示例")
        if not metrics.has_references:
            metrics.missing_elements.append("参考文献")
        if not metrics.has_msc_code:
            metrics.missing_elements.append("MSC编码")
            
        return metrics
    
    def _assess_accuracy(self, content: str) -> AccuracyMetrics:
        """评估准确性"""
        metrics = AccuracyMetrics()
        
        # 检查数学公式语法错误
        # 检测不匹配的括号、未闭合的公式等
        inline_math = re.findall(r'\$[^$]*\$', content)
        for formula in inline_math:
            if formula.count('{') != formula.count('}'):
                metrics.math_formula_syntax_errors += 1
            if formula.count('(') != formula.count(')'):
                metrics.math_formula_syntax_errors += 1
        
        # 检查引用格式
        citation_patterns = [
            r'\[\d+\]',
            r'\[\w+\s+\d{4}\]',
            r'@\w+',
            r'\(\w+\s*,?\s*\d{4}\)'
        ]
        for pattern in citation_patterns:
            matches = re.findall(pattern, content)
            # 简单检查：如果引用格式不一致，标记为潜在错误
            if len(matches) > 0:
                # 检查是否混用不同格式
                if len(set(type(m).__name__ for m in matches)) > 1:
                    metrics.citation_errors += 1
        
        # 检查链接完整性
        link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
        links = re.findall(link_pattern, content)
        for text, url in links:
            if url.startswith('#'):
                # 锚点链接，检查是否存在
                anchor = url[1:]
                if not re.search(rf'id=["\']?{anchor}["\']?|name=["\']?{anchor}["\']?', content):
                    metrics.broken_links.append(url)
        
        # 检查符号一致性
        notation_variants = {
            'epsilon': [r'\\epsilon', r'\\varepsilon'],
            'phi': [r'\\phi', r'\\varphi'],
            'emptyset': [r'\\emptyset', r'\\varnothing'],
        }
        for name, variants in notation_variants.items():
            found = [v for v in variants if re.search(v, content)]
            if len(found) > 1:
                metrics.inconsistent_notations.append(f"{name}: {found}")
        
        # 检查逻辑一致性
        # 检测"详见下文"但无下文的情况
        if re.search(r'详见下文|见下文|see below', content, re.I):
            if not re.search(r'#{2,}.*', content.split('详见下文')[1] if '详见下文' in content else ''):
                metrics.logic_gaps.append("缺少'详见下文'指向的内容")
        
        return metrics
    
    def _assess_readability(self, content: str) -> ReadabilityMetrics:
        """评估可读性"""
        metrics = ReadabilityMetrics()
        
        # 移除代码块和公式
        clean_content = re.sub(r'```[\s\S]*?```', '', content)
        clean_content = re.sub(r'\$[^$]+\$', '[FORMULA]', clean_content)
        
        # 计算句子平均长度
        sentences = re.split(r'[。！？.!?]+', clean_content)
        sentences = [s.strip() for s in sentences if s.strip()]
        if sentences:
            total_chars = sum(len(s) for s in sentences)
            metrics.avg_sentence_length = total_chars / len(sentences)
        
        # 计算段落平均长度
        paragraphs = [p.strip() for p in clean_content.split('\n\n') if p.strip()]
        if paragraphs:
            metrics.avg_paragraph_length = len(sentences) / len(paragraphs) if paragraphs else 0
        
        # 计算复杂词比例
        words = re.findall(r'\b\w+\b', clean_content)
        if words:
            complex_words = [w for w in words if len(w) > 6]
            metrics.complex_word_ratio = len(complex_words) / len(words)
        
        # 评估标题结构
        headings = re.findall(r'^(#{1,6})', content, re.M)
        if headings:
            levels = [len(h) for h in headings]
            # 检查层级是否连续
            expected_levels = list(range(1, max(levels) + 1))
            actual_levels = sorted(set(levels))
            metrics.heading_structure_score = len(set(expected_levels) & set(actual_levels)) / len(expected_levels)
        
        # 计算代码块比例
        code_blocks = re.findall(r'```[\s\S]*?```', content)
        code_chars = sum(len(block) for block in code_blocks)
        metrics.code_block_ratio = code_chars / len(content) if content else 0
        
        # 计算公式密度
        formulas = []
        for pattern in self.formula_patterns:
            formulas.extend(re.findall(pattern, content))
        metrics.formula_density = len(formulas) / len(content) * 1000 if content else 0
        
        return metrics
    
    def _assess_internationalization(self, content: str) -> InternationalizationMetrics:
        """评估国际化"""
        metrics = InternationalizationMetrics()
        
        # 检查是否包含英文术语
        english_terms = re.findall(r'[a-zA-Z]+', content)
        technical_terms = [t for t in english_terms if len(t) > 3]
        metrics.has_english_terms = len(technical_terms) > 10
        
        # 检查术语一致性
        # 中英术语对照检查
        term_pairs = [
            (r'群\s*\(group\)', r'group\s*\(群\)'),
            (r'环\s*\(ring\)', r'ring\s*\(环\)'),
            (r'域\s*\(field\)', r'field\s*\(域\)'),
        ]
        for zh_first, en_first in term_pairs:
            zh_count = len(re.findall(zh_first, content, re.I))
            en_count = len(re.findall(en_first, content, re.I))
            if zh_count > 0 and en_count > 0:
                metrics.inconsistent_translations.append(f"术语混用: {zh_first}")
        
        # 术语一致性评分
        if not metrics.inconsistent_translations:
            metrics.term_consistency_score = 1.0
        else:
            metrics.term_consistency_score = max(0, 1 - len(metrics.inconsistent_translations) * 0.1)
        
        # 文化适应性评分（基于内容国际化特征）
        international_markers = [
            r'international|global|worldwide',
            r'historical|history|historical',
            r'application|applied|real-world'
        ]
        marker_count = sum(1 for pattern in international_markers if re.search(pattern, content, re.I))
        metrics.cultural_adaptation_score = marker_count / len(international_markers)
        
        # 翻译完整性
        # 检查是否有未翻译的内容
        untranslated_patterns = [
            r'[\u4e00-\u9fff]+[a-zA-Z]+[\u4e00-\u9fff]+',  # 中英文混用
        ]
        metrics.translation_completeness = 1.0  # 默认为完整
        
        return metrics
    
    def _assess_learning_effect(self, content: str) -> LearningEffectMetrics:
        """评估学习效果预测"""
        metrics = LearningEffectMetrics()
        
        # 评估难度等级
        advanced_keywords = ['advanced', 'research', '前沿', '猜想', 'conjecture']
        intermediate_keywords = ['theorem', '证明', 'application', '应用']
        beginner_keywords = ['basic', 'introduction', '基础', '入门']
        
        advanced_count = sum(1 for kw in advanced_keywords if kw in content.lower())
        intermediate_count = sum(1 for kw in intermediate_keywords if kw in content.lower())
        beginner_count = sum(1 for kw in beginner_keywords if kw in content.lower())
        
        if advanced_count > 3:
            metrics.estimated_difficulty = "advanced"
        elif intermediate_count > 3:
            metrics.estimated_difficulty = "intermediate"
        else:
            metrics.estimated_difficulty = "beginner"
        
        # 预估学习时长（基于内容长度和复杂度）
        char_count = len(content)
        formula_count = len(re.findall(r'\$[^$]+\$', content))
        
        # 基础阅读时间 + 公式理解时间
        base_time = char_count / 300  # 每分钟300字符
        formula_time = formula_count * 2  # 每个公式2分钟
        metrics.estimated_study_time = int(base_time + formula_time)
        
        # 掌握概率预测
        # 基于完整性、可读性和练习数量
        exercise_count = len(re.findall(r'(?:练习|exercise|problem|问题)\s*\d*[.:]?', content, re.I))
        completeness_factor = 0.5 if exercise_count > 0 else 0.3
        readability_factor = min(1.0, 1000 / char_count) if char_count > 0 else 0.5
        metrics.mastery_probability = completeness_factor * readability_factor
        
        # 前置知识清晰度
        prereq_section = re.search(
            r'(?:前置知识|prerequisite|预备).*?\n(.*?)(?=\n#{2,}|$)',
            content,
            re.I | re.S
        )
        if prereq_section:
            metrics.prerequisite_clarity = 1.0
        else:
            # 检查是否有前置知识提示
            if re.search(r'需要|require|假设|assume', content, re.I):
                metrics.prerequisite_clarity = 0.5
            else:
                metrics.prerequisite_clarity = 0.0
        
        # 练习多样性
        exercise_types = {
            'proof': bool(re.search(r'证明|proof', content, re.I)),
            'calculation': bool(re.search(r'计算|calculate|compute', content, re.I)),
            'example': bool(re.search(r'例子|example', content, re.I)),
            'application': bool(re.search(r'应用|application', content, re.I))
        }
        metrics.exercise_diversity = sum(1 for v in exercise_types.values() if v) / len(exercise_types)
        
        return metrics
    
    def _generate_recommendations(self, result: QualityAssessmentResult) -> List[str]:
        """生成改进建议"""
        recommendations = []
        
        # 完整性建议
        if not result.completeness.has_concept_definition:
            recommendations.append("添加清晰的概念定义部分")
        if not result.completeness.has_examples:
            recommendations.append("增加具体示例以帮助理解")
        if result.completeness.theorem_count > 0 and result.completeness.proof_count < result.completeness.theorem_count:
            recommendations.append(f"为所有定理提供证明（当前有{result.completeness.theorem_count}个定理，{result.completeness.proof_count}个证明）")
        
        # 准确性建议
        if result.accuracy.math_formula_syntax_errors > 0:
            recommendations.append(f"修复{result.accuracy.math_formula_syntax_errors}处公式语法错误")
        if result.accuracy.inconsistent_notations:
            recommendations.append("统一数学符号使用")
        
        # 可读性建议
        if result.readability.avg_sentence_length > 30:
            recommendations.append("缩短句子长度，提高可读性")
        if result.readability.heading_structure_score < 0.8:
            recommendations.append("改进文档标题层级结构")
        
        # 国际化建议
        if not result.internationalization.has_english_terms:
            recommendations.append("添加关键术语的英文对照")
        if result.internationalization.inconsistent_translations:
            recommendations.append("统一中英文术语的使用方式")
        
        # 学习效果建议
        if result.learning_effect.estimated_difficulty == "advanced" and result.learning_effect.prerequisite_clarity < 0.5:
            recommendations.append("高级内容需要更详细的前置知识说明")
        if result.learning_effect.exercise_diversity < 0.5:
            recommendations.append("增加不同类型的练习（证明、计算、应用等）")
        
        return recommendations
    
    def _extract_issues(self, result: QualityAssessmentResult) -> List[Dict]:
        """提取问题清单"""
        issues = []
        
        # 完整性问题
        for element in result.completeness.missing_elements:
            issues.append({
                'type': 'completeness',
                'severity': 'medium',
                'description': f"缺少{element}",
                'suggestion': f"请添加{element}部分"
            })
        
        # 准确性问题
        if result.accuracy.math_formula_syntax_errors > 0:
            issues.append({
                'type': 'accuracy',
                'severity': 'high',
                'description': f"发现{result.accuracy.math_formula_syntax_errors}处公式语法错误",
                'suggestion': "检查公式中的括号匹配"
            })
        
        for notation in result.accuracy.inconsistent_notations:
            issues.append({
                'type': 'accuracy',
                'severity': 'low',
                'description': f"符号不一致: {notation}",
                'suggestion': "统一使用一种符号表示"
            })
        
        # 可读性问题
        if result.readability.avg_sentence_length > 35:
            issues.append({
                'type': 'readability',
                'severity': 'medium',
                'description': f"句子过长（平均{result.readability.avg_sentence_length:.1f}字）",
                'suggestion': "将长句拆分为短句"
            })
        
        # 国际化问题
        for translation in result.internationalization.inconsistent_translations:
            issues.append({
                'type': 'internationalization',
                'severity': 'low',
                'description': translation,
                'suggestion': "统一术语翻译"
            })
        
        return issues
    
    def assess_directory(self, directory: str, pattern: str = "**/*.md") -> List[QualityAssessmentResult]:
        """评估整个目录"""
        path = Path(directory)
        files = list(path.glob(pattern))
        
        for file_path in files:
            try:
                result = self.assess_file(str(file_path))
                self.results.append(result)
            except Exception as e:
                print(f"Error assessing {file_path}: {e}")
        
        return self.results
    
    def get_summary(self) -> Dict:
        """获取评估摘要"""
        if not self.results:
            return {}
        
        scores = [r.overall_score for r in self.results]
        quality_levels = [r.quality_level for r in self.results]
        
        return {
            'total_files': len(self.results),
            'average_score': sum(scores) / len(scores),
            'min_score': min(scores),
            'max_score': max(scores),
            'quality_distribution': {
                level: quality_levels.count(level)
                for level in set(quality_levels)
            },
            'high_priority_issues': sum(
                1 for r in self.results
                for i in r.issues if i['severity'] == 'high'
            )
        }


def main():
    """主函数"""
    import argparse
    
    parser = argparse.ArgumentParser(description='FormalMath内容质量评估工具')
    parser.add_argument('path', help='要评估的文件或目录路径')
    parser.add_argument('-o', '--output', help='输出结果文件路径')
    parser.add_argument('-f', '--format', choices=['json', 'html', 'markdown'], 
                        default='json', help='输出格式')
    parser.add_argument('-r', '--recursive', action='store_true',
                        help='递归评估目录')
    
    args = parser.parse_args()
    
    assessor = ContentQualityAssessor()
    
    if os.path.isfile(args.path):
        result = assessor.assess_file(args.path)
        results = [result]
    else:
        results = assessor.assess_directory(args.path)
    
    # 输出结果
    summary = assessor.get_summary()
    print(f"评估完成: {summary.get('total_files', 1)}个文件")
    print(f"平均分: {summary.get('average_score', result.overall_score):.2f}")
    
    if args.output:
        output_path = Path(args.output)
        
        if args.format == 'json':
            data = {
                'summary': summary,
                'results': [asdict(r) for r in results]
            }
            output_path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding='utf-8')
        
        print(f"结果已保存至: {args.output}")


if __name__ == '__main__':
    main()
