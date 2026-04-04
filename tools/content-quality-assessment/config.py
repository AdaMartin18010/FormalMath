#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath 内容质量评估系统 - 配置文件
Configuration for Content Quality Assessment System

版本：1.0.0
"""

from typing import Dict, List, Set


class AssessmentConfig:
    """评估配置类"""
    
    # 权重配置（总和应为1.0）
    WEIGHTS = {
        'completeness': 0.25,
        'accuracy': 0.25,
        'readability': 0.20,
        'internationalization': 0.15,
        'learning_effect': 0.15
    }
    
    # 质量等级阈值
    QUALITY_THRESHOLDS = {
        'EXCELLENT': 90,
        'GOOD': 80,
        'ACCEPTABLE': 60,
        'NEEDS_IMPROVEMENT': 40,
        'POOR': 0
    }
    
    # 可读性指标理想值
    READABILITY_IDEALS = {
        'avg_sentence_length': (15, 25),  # 理想句子长度范围
        'avg_paragraph_length': (3, 5),   # 理想段落句子数
        'complex_word_ratio': (0.10, 0.20),  # 理想复杂词比例
        'formula_density': (0.01, 0.05),   # 理想公式密度
        'code_block_ratio': (0, 0.30)      # 理想代码块比例
    }
    
    # 数学术语词典
    MATH_TERMS: Set[str] = {
        # 基础术语
        '定理', 'theorem',
        '引理', 'lemma',
        '命题', 'proposition',
        '推论', 'corollary',
        '证明', 'proof',
        '定义', 'definition',
        '公理', 'axiom',
        '假设', 'hypothesis',
        '猜想', 'conjecture',
        
        # 例子和说明
        '例子', 'example',
        '示例', 'demonstration',
        '注', 'remark',
        '注释', 'note',
        '说明', 'explanation',
        
        # 数学对象
        '集合', 'set',
        '函数', 'function',
        '映射', 'map',
        '群', 'group',
        '环', 'ring',
        '域', 'field',
        '空间', 'space',
        '结构', 'structure',
        
        # 运算符和关系
        '等价', 'equivalent',
        '同构', 'isomorphism',
        '同态', 'homomorphism',
        '单射', 'injective',
        '满射', 'surjective',
        '双射', 'bijective',
        
        # 逻辑用语
        '当且仅当', 'if and only if',
        '充分必要', 'necessary and sufficient',
        '任意', 'arbitrary',
        '存在', 'exists',
        '唯一', 'unique',
        '有限', 'finite',
        '无限', 'infinite',
        
        # 证明用语
        '显然', 'obviously',
        '易证', 'easy to prove',
        '不妨设', 'without loss of generality',
        '假设', 'assume',
        '设', 'let',
        '令', 'define',
        '因为', 'because',
        '所以', 'therefore',
        '由...得', 'from ... we have',
    }
    
    # 公式匹配模式
    FORMULA_PATTERNS: List[str] = [
        r'\$[^$]+\$',           # 行内公式 $...$
        r'\$\$[^$]+\$\$',       # 行间公式 $$...$$
        r'\\\([^)]+\\\)',       # \( ... \) 格式
        r'\\\[[^\]]+\\\]',     # \[ ... \] 格式
        r'`[^`]+`',            # 行内代码
        r'```[\s\S]*?```',     # 代码块
    ]
    
    # 符号一致性检查
    NOTATION_VARIANTS: Dict[str, List[str]] = {
        'epsilon': [r'\\epsilon', r'\\varepsilon'],
        'phi': [r'\\phi', r'\\varphi'],
        'emptyset': [r'\\emptyset', r'\\varnothing'],
        'subset': [r'\\subset', r'\\subseteq'],
        'to': [r'\\to', r'\\rightarrow', r'\\longrightarrow'],
        'mapsto': [r'\\mapsto', r'\\longmapsto'],
        'implies': [r'\\Rightarrow', r'\\Longrightarrow', r'\\implies'],
        'iff': [r'\\Leftrightarrow', r'\\Longleftrightarrow', r'\\iff'],
    }
    
    # 章节结构要求
    REQUIRED_SECTIONS: Dict[str, List[str]] = {
        'standard': [
            r'定义|definition',
            r'定理|theorem|命题|proposition',
            r'证明|proof',
            r'例子|example',
        ],
        'advanced': [
            r'定义|definition',
            r'定理|theorem',
            r'证明|proof',
            r'应用|application',
            r'参考|reference',
        ]
    }
    
    # 引用格式模式
    CITATION_PATTERNS: List[str] = [
        r'\[\d+\]',                     # [1], [2]
        r'\[\w+\s+\d{4}\]',              # [Author 2020]
        r'@\w+',                        # @citation
        r'\(\w+\s*,?\s*\d{4}[a-z]?\)',  # (Author, 2020)
        r'\[\^\d+\]',                   # [^1] 脚注引用
    ]
    
    # 国际化检查模式
    I18N_PATTERNS: Dict[str, List[str]] = {
        'term_pairs': [
            (r'群\s*\(group\)', r'group\s*\(群\)'),
            (r'环\s*\(ring\)', r'ring\s*\(环\)'),
            (r'域\s*\(field\)', r'field\s*\(域\)'),
            (r'集合\s*\(set\)', r'set\s*\(集合\)'),
            (r'函数\s*\(function\)', r'function\s*\(函数\)'),
        ],
        'international_markers': [
            r'international|global|worldwide',
            r'historical|history|historical',
            r'application|applied|real-world',
            r'advanced|research|frontier',
        ]
    }
    
    # 难度等级关键词
    DIFFICULTY_KEYWORDS = {
        'beginner': [
            'basic', 'introduction', 'elementary', 'fundamental',
            '基础', '入门', '初级', '基本'
        ],
        'intermediate': [
            'intermediate', 'standard', 'theorem', 'proof', 'application',
            '中级', '标准', '定理', '证明', '应用'
        ],
        'advanced': [
            'advanced', 'research', 'frontier', 'conjecture', 'specialized',
            '高级', '研究', '前沿', '猜想', '专业', '深度'
        ]
    }
    
    # 练习类型检测
    EXERCISE_PATTERNS: Dict[str, str] = {
        'proof': r'证明|proof|证',
        'calculation': r'计算|calculate|compute|求',
        'example': r'例子|example|举例',
        'application': r'应用|application|实际',
        'verification': r'验证|verify|检验',
    }
    
    # 输出配置
    OUTPUT_CONFIG = {
        'html_template_dir': 'templates',
        'default_output_format': 'json',
        'supported_formats': ['json', 'html', 'markdown', 'csv'],
        'max_issues_display': 10,
        'max_recommendations_display': 5
    }
    
    # 评估阈值
    THRESHOLDS = {
        'min_sentence_length_warning': 35,  # 句子过长警告
        'min_theorem_proof_ratio': 0.8,     # 定理证明比最低要求
        'min_example_coverage': 0.3,        # 最小示例覆盖率
        'max_formula_error_count': 3,       # 最大公式错误数
        'min_prerequisite_clarity': 0.5,    # 前置知识清晰度最低要求
    }


# 全局配置实例
config = AssessmentConfig()


def get_config() -> AssessmentConfig:
    """获取配置实例"""
    return config


def update_weights(new_weights: Dict[str, float]):
    """更新权重配置"""
    total = sum(new_weights.values())
    if abs(total - 1.0) > 0.001:
        raise ValueError(f"权重总和必须等于1.0，当前为{total}")
    
    config.WEIGHTS.update(new_weights)


def add_math_terms(terms: Set[str]):
    """添加数学术语"""
    config.MATH_TERMS.update(terms)


def set_quality_thresholds(thresholds: Dict[str, int]):
    """设置质量等级阈值"""
    config.QUALITY_THRESHOLDS.update(thresholds)


if __name__ == '__main__':
    # 打印当前配置
    print("=== FormalMath 内容质量评估系统配置 ===\n")
    
    print("评估维度权重:")
    for dim, weight in config.WEIGHTS.items():
        print(f"  - {dim}: {weight*100:.0f}%")
    
    print("\n质量等级阈值:")
    for level, threshold in sorted(config.QUALITY_THRESHOLDS.items(), key=lambda x: -x[1]):
        print(f"  - {level}: ≥{threshold}")
    
    print(f"\n数学术语数量: {len(config.MATH_TERMS)}")
    print(f"符号变体数量: {len(config.NOTATION_VARIANTS)}")
