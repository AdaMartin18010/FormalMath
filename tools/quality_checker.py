#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath项目文档质量检查脚本

功能：
1. 自动扫描docs/和concept/目录下的Markdown文档
2. 检测文档质量问题（字数、必需元素、格式规范、禁止内容等）
3. 生成详细的质量报告

使用方法：
    python tools/quality_checker.py [选项]

选项：
    --path PATH         指定要检查的目录（默认：docs/ 和 concept/）
    --output OUTPUT     输出报告路径（默认：output/quality_report.md）
    --min-size BYTES    最小文件大小（默认：2000字节）
    --strict            严格模式（启用所有检查项）
    --fix               尝试自动修复部分问题
    --help              显示帮助信息

作者: FormalMath项目
版本: 1.0.0
"""

import os
import re
import sys
import argparse
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Tuple, Optional, Set
from dataclasses import dataclass, field
from enum import Enum
import yaml


class Severity(Enum):
    """问题严重程度"""
    ERROR = "错误"      # 必须修复
    WARNING = "警告"    # 建议修复
    INFO = "信息"       # 仅供参考


@dataclass
class QualityIssue:
    """质量问题记录"""
    file_path: str
    line_number: int
    severity: Severity
    category: str
    message: str
    suggestion: str = ""


@dataclass
class DocumentScore:
    """文档评分"""
    file_path: str
    total_score: float = 100.0
    issues: List[QualityIssue] = field(default_factory=list)
    
    # 各维度得分
    content_score: float = 100.0      # 内容完整性
    format_score: float = 100.0       # 格式规范
    structure_score: float = 100.0    # 结构完整性
    quality_score: float = 100.0      # 内容质量
    
    # 统计信息
    word_count: int = 0
    char_count: int = 0
    section_count: int = 0
    has_frontmatter: bool = False


class DocumentQualityChecker:
    """文档质量检查器"""
    
    # 最小文件大小（字节）
    MIN_FILE_SIZE = 2000
    
    # 必需的前置元数据字段
    REQUIRED_FRONTMATTER_FIELDS = {
        'docs/': [],  # docs目录下可选
        'concept/': ['msc_primary']  # concept目录下必需
    }
    
    # 必需的内容章节（正则表达式）
    REQUIRED_SECTIONS = [
        (r'#{1,2}\s*.*(?:定义|Definition)', "定义部分"),
        (r'#{1,2}\s*.*(?:示例|Example|例子)', "示例部分"),
        (r'#{1,2}\s*.*(?:证明|Proof|推导|Derivation)', "证明/推导部分"),
    ]
    
    # 推荐的内容章节
    RECOMMENDED_SECTIONS = [
        (r'#{1,2}\s*.*(?:概述|Overview|简介|Introduction)', "概述部分"),
        (r'#{1,2}\s*.*(?:历史|History|背景|Background)', "历史/背景部分"),
        (r'#{1,2}\s*.*(?:应用|Application|实例)', "应用/实例部分"),
        (r'#{1,2}\s*.*(?:参考|Reference|文献)', "参考文献部分"),
    ]
    
    # 禁止内容模式
    FORBIDDEN_PATTERNS = [
        (r'TODO[:：]', "TODO占位符"),
        (r'FIXME[:：]', "FIXME标记"),
        (r'XXX[:：]', "XXX标记"),
        (r'待补充', "待补充标记"),
        (r'待完善', "待完善标记"),
        (r'待续', "待续标记"),
        (r'\[.*?\]\(.*?\)', "空链接"),
        (r'#{1,6}\s*$', "空标题"),
        (r'\n\n\n+', "过多空行"),
    ]
    
    # 重复内容检测（段落级）
    MIN_REPEAT_LENGTH = 50  # 最小重复长度
    
    def __init__(self, min_size: int = 2000, strict: bool = False):
        self.min_size = min_size
        self.strict = strict
        self.issues: List[QualityIssue] = []
        self.scores: List[DocumentScore] = []
        self.checked_files: Set[str] = set()
        
    def check_all(self, paths: List[str]) -> List[DocumentScore]:
        """检查所有指定路径的文档"""
        for path in paths:
            if os.path.isfile(path):
                if path.endswith('.md'):
                    self._check_file(path)
            elif os.path.isdir(path):
                self._check_directory(path)
        
        return self.scores
    
    def _check_directory(self, dir_path: str):
        """递归检查目录"""
        for root, _, files in os.walk(dir_path):
            # 跳过归档目录
            if '归档' in root or 'archive' in root.lower():
                continue
                
            for file in files:
                if file.endswith('.md'):
                    file_path = os.path.join(root, file)
                    self._check_file(file_path)
    
    def _check_file(self, file_path: str):
        """检查单个文件"""
        # 避免重复检查
        abs_path = os.path.abspath(file_path)
        if abs_path in self.checked_files:
            return
        self.checked_files.add(abs_path)
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            self.issues.append(QualityIssue(
                file_path=file_path,
                line_number=0,
                severity=Severity.ERROR,
                category="文件读取",
                message=f"无法读取文件: {str(e)}"
            ))
            return
        
        score = DocumentScore(file_path=file_path)
        
        # 执行各项检查
        self._check_file_size(file_path, content, score)
        self._check_frontmatter(file_path, content, score)
        self._check_structure(file_path, content, score)
        self._check_content_quality(file_path, content, score)
        self._check_forbidden_content(file_path, content, score)
        self._check_formatting(file_path, content, score)
        self._check_links(file_path, content, score)
        
        # 计算总分
        self._calculate_total_score(score)
        
        self.scores.append(score)
    
    def _check_file_size(self, file_path: str, content: str, score: DocumentScore):
        """检查文件大小"""
        size = len(content.encode('utf-8'))
        score.char_count = len(content)
        
        # 统计字数（中文字符 + 英文单词）
        chinese_chars = len(re.findall(r'[\u4e00-\u9fff]', content))
        english_words = len(re.findall(r'[a-zA-Z]+', content))
        score.word_count = chinese_chars + english_words
        
        if size < self.min_size:
            issue = QualityIssue(
                file_path=file_path,
                line_number=0,
                severity=Severity.ERROR if self.strict else Severity.WARNING,
                category="文件大小",
                message=f"文件大小为 {size} 字节，小于最小要求 {self.min_size} 字节",
                suggestion="请扩充文档内容，添加更多定义、示例、证明或背景信息"
            )
            score.issues.append(issue)
            score.content_score -= 20
    
    def _check_frontmatter(self, file_path: str, content: str, score: DocumentScore):
        """检查Frontmatter"""
        # 检测Frontmatter
        frontmatter_match = re.match(r'^---\s*\n(.*?)\n---\s*\n', content, re.DOTALL)
        
        if frontmatter_match:
            score.has_frontmatter = True
            frontmatter_content = frontmatter_match.group(1)
            
            try:
                fm = yaml.safe_load(frontmatter_content)
                if not isinstance(fm, dict):
                    raise yaml.YAMLError("Frontmatter不是有效的YAML对象")
                
                # 根据目录检查必需字段
                for dir_prefix, required_fields in self.REQUIRED_FRONTMATTER_FIELDS.items():
                    if dir_prefix in file_path.replace('\\', '/'):
                        for field in required_fields:
                            if field not in fm:
                                issue = QualityIssue(
                                    file_path=file_path,
                                    line_number=1,
                                    severity=Severity.ERROR,
                                    category="Frontmatter",
                                    message=f"缺少必需的元数据字段: {field}",
                                    suggestion=f"在Frontmatter中添加 '{field}' 字段"
                                )
                                score.issues.append(issue)
                                score.format_score -= 10
                
                # 检查MSC编码格式
                if 'msc_primary' in fm:
                    msc = str(fm['msc_primary'])
                    if not re.match(r'^\d{2}[A-Z]\d{2}$', msc):
                        issue = QualityIssue(
                            file_path=file_path,
                            line_number=1,
                            severity=Severity.WARNING,
                            category="Frontmatter",
                            message=f"MSC主编码格式可能不正确: {msc}",
                            suggestion="MSC编码应为5位格式，如: 03E99"
                        )
                        score.issues.append(issue)
                        score.format_score -= 5
                        
            except yaml.YAMLError as e:
                issue = QualityIssue(
                    file_path=file_path,
                    line_number=1,
                    severity=Severity.ERROR,
                    category="Frontmatter",
                    message=f"Frontmatter YAML格式错误: {str(e)}",
                    suggestion="检查YAML语法，确保正确的缩进和格式"
                )
                score.issues.append(issue)
                score.format_score -= 15
        else:
            # 对于concept目录下的文件，Frontmatter是必需的
            if 'concept/' in file_path.replace('\\', '/'):
                issue = QualityIssue(
                    file_path=file_path,
                    line_number=1,
                    severity=Severity.ERROR,
                    category="Frontmatter",
                    message="缺少Frontmatter",
                    suggestion="在文档开头添加Frontmatter，包含至少msc_primary字段"
                )
                score.issues.append(issue)
                score.format_score -= 20
    
    def _check_structure(self, file_path: str, content: str, score: DocumentScore):
        """检查文档结构"""
        # 统计标题层级
        headers = re.findall(r'^(#{1,6})\s+(.+)$', content, re.MULTILINE)
        score.section_count = len(headers)
        
        if score.section_count == 0:
            issue = QualityIssue(
                file_path=file_path,
                line_number=0,
                severity=Severity.ERROR,
                category="文档结构",
                message="文档没有标题结构",
                suggestion="添加适当的Markdown标题（# ## ###等）来组织内容"
            )
            score.issues.append(issue)
            score.structure_score -= 30
        
        # 检查标题层级跳跃
        prev_level = 0
        for i, (hashes, title) in enumerate(headers):
            level = len(hashes)
            line_num = content[:content.find(f"{hashes} {title}")].count('\n') + 1
            
            if level > prev_level + 1 and prev_level > 0:
                issue = QualityIssue(
                    file_path=file_path,
                    line_number=line_num,
                    severity=Severity.WARNING,
                    category="文档结构",
                    message=f"标题层级跳跃: H{prev_level} 直接到 H{level} - \"{title}\"",
                    suggestion=f"考虑添加H{prev_level + 1}级别的标题"
                )
                score.issues.append(issue)
                score.structure_score -= 5
            
            prev_level = level
        
        # 检查必需章节
        for pattern, name in self.REQUIRED_SECTIONS:
            if not re.search(pattern, content, re.IGNORECASE):
                issue = QualityIssue(
                    file_path=file_path,
                    line_number=0,
                    severity=Severity.WARNING if not self.strict else Severity.ERROR,
                    category="文档结构",
                    message=f"缺少{name}",
                    suggestion=f"添加{name}，包含定义、示例或证明"
                )
                score.issues.append(issue)
                score.structure_score -= 10
        
        # 检查推荐章节（严格模式下）
        if self.strict:
            for pattern, name in self.RECOMMENDED_SECTIONS:
                if not re.search(pattern, content, re.IGNORECASE):
                    issue = QualityIssue(
                        file_path=file_path,
                        line_number=0,
                        severity=Severity.INFO,
                        category="文档结构",
                        message=f"建议添加{name}",
                        suggestion=f"考虑添加{name}以完善文档"
                    )
                    score.issues.append(issue)
    
    def _check_content_quality(self, file_path: str, content: str, score: DocumentScore):
        """检查内容质量"""
        # 检查数学公式
        inline_math = len(re.findall(r'\$[^\$]+\$', content))
        block_math = len(re.findall(r'\$\$[\s\S]*?\$', content))
        
        if inline_math + block_math == 0:
            issue = QualityIssue(
                file_path=file_path,
                line_number=0,
                severity=Severity.WARNING,
                category="内容质量",
                message="文档中未检测到数学公式",
                suggestion="对于数学概念文档，建议添加LaTeX数学公式（$...$或$$...$$）"
            )
            score.issues.append(issue)
            score.quality_score -= 10
        
        # 检查代码块
        code_blocks = len(re.findall(r'```[\s\S]*?```', content))
        
        # 检查表格
        tables = len(re.findall(r'\|.*\|.*\|', content))
        
        # 检查列表
        lists = len(re.findall(r'^[\s]*[-*+\d+\.][\s]', content, re.MULTILINE))
        
        # 检查图片和图表
        images = len(re.findall(r'!\[.*?\]\(.*?\)', content))
        mermaid = len(re.findall(r'```mermaid[\s\S]*?```', content))
        
        # 内容多样性评分
        diversity_score = sum([
            1 if inline_math + block_math > 0 else 0,
            1 if code_blocks > 0 else 0,
            1 if tables > 0 else 0,
            1 if lists > 10 else 0,
            1 if images + mermaid > 0 else 0,
        ])
        
        if diversity_score < 2:
            issue = QualityIssue(
                file_path=file_path,
                line_number=0,
                severity=Severity.INFO,
                category="内容质量",
                message="内容格式较为单一，建议增加多样化的内容形式",
                suggestion="考虑添加代码块、表格、列表、图表或Mermaid图"
            )
            score.issues.append(issue)
        
        # 检查过长的段落
        paragraphs = content.split('\n\n')
        for para in paragraphs:
            if len(para) > 1000 and not para.startswith('```'):
                line_num = content[:content.find(para)].count('\n') + 1
                issue = QualityIssue(
                    file_path=file_path,
                    line_number=line_num,
                    severity=Severity.INFO,
                    category="内容质量",
                    message=f"发现过长段落（{len(para)}字符），可能影响可读性",
                    suggestion="将长段落拆分为多个较短的段落"
                )
                score.issues.append(issue)
                break  # 只报告一次
        
        # 重复内容检测
        self._check_duplicate_content(file_path, content, score)
    
    def _check_duplicate_content(self, file_path: str, content: str, score: DocumentScore):
        """检查重复内容"""
        # 提取段落
        paragraphs = [p.strip() for p in re.split(r'\n\n+', content) if len(p.strip()) > self.MIN_REPEAT_LENGTH]
        
        # 简单的重复检测
        seen = set()
        for para in paragraphs:
            # 规范化段落用于比较
            normalized = re.sub(r'\s+', ' ', para.lower())[:100]
            if normalized in seen:
                line_num = content[:content.find(para)].count('\n') + 1
                issue = QualityIssue(
                    file_path=file_path,
                    line_number=line_num,
                    severity=Severity.WARNING,
                    category="内容质量",
                    message="检测到可能重复的内容段落",
                    suggestion="检查并删除重复内容，或将其重构为引用"
                )
                score.issues.append(issue)
                score.quality_score -= 10
                break  # 只报告一次
            seen.add(normalized)
    
    def _check_forbidden_content(self, file_path: str, content: str, score: DocumentScore):
        """检查禁止内容"""
        for pattern, name in self.FORBIDDEN_PATTERNS:
            matches = list(re.finditer(pattern, content, re.IGNORECASE | re.MULTILINE))
            for match in matches[:3]:  # 最多报告3个
                line_num = content[:match.start()].count('\n') + 1
                issue = QualityIssue(
                    file_path=file_path,
                    line_number=line_num,
                    severity=Severity.ERROR if name != "过多空行" else Severity.INFO,
                    category="禁止内容",
                    message=f"检测到{name}: {match.group(0)[:50]}...",
                    suggestion=f"删除{name}，替换为实际内容"
                )
                score.issues.append(issue)
                if name != "过多空行":
                    score.quality_score -= 15
    
    def _check_formatting(self, file_path: str, content: str, score: DocumentScore):
        """检查格式规范"""
        # 检查中英文混排空格
        mixed_pattern = re.findall(r'[\u4e00-\u9fff][a-zA-Z]|[a-zA-Z][\u4e00-\u9fff]', content)
        if len(mixed_pattern) > 10:
            issue = QualityIssue(
                file_path=file_path,
                line_number=0,
                severity=Severity.INFO,
                category="格式规范",
                message=f"检测到{len(mixed_pattern)}处中英文之间缺少空格",
                suggestion="在中英文之间添加空格以提高可读性"
            )
            score.issues.append(issue)
        
        # 检查全角标点
        fullwidth_punct = len(re.findall(r'[，。！？；：""''（）]', content))
        halfwidth_punct = len(re.findall(r'[,.!?;:\'"()]', content))
        
        # 检查标题格式
        bad_headers = re.findall(r'^(#{1,6})[^\s#]', content, re.MULTILINE)
        for match in bad_headers:
            issue = QualityIssue(
                file_path=file_path,
                line_number=0,
                severity=Severity.WARNING,
                category="格式规范",
                message=f"标题格式不规范: {match}",
                suggestion="标题符号#后应加空格，如: ## 标题"
            )
            score.issues.append(issue)
            score.format_score -= 5
        
        # 检查文件末尾空行
        if not content.endswith('\n'):
            issue = QualityIssue(
                file_path=file_path,
                line_number=content.count('\n') + 1,
                severity=Severity.INFO,
                category="格式规范",
                message="文件末尾缺少换行符",
                suggestion="在文件末尾添加一个空行"
            )
            score.issues.append(issue)
    
    def _check_links(self, file_path: str, content: str, score: DocumentScore):
        """检查链接"""
        # 提取所有链接
        links = re.findall(r'\[([^\]]*)\]\(([^)]+)\)', content)
        
        for text, url in links:
            # 检查空链接
            if not text.strip():
                issue = QualityIssue(
                    file_path=file_path,
                    line_number=0,
                    severity=Severity.WARNING,
                    category="链接检查",
                    message=f"空链接文本: []({url})",
                    suggestion="为链接添加描述文本"
                )
                score.issues.append(issue)
            
            # 检查本地文件链接
            if not url.startswith(('http://', 'https://', '#', 'mailto:')):
                # 解析相对路径
                base_dir = os.path.dirname(file_path)
                if url.startswith('/'):
                    # 绝对路径（相对于项目根）
                    full_path = os.path.join(os.getcwd(), url.lstrip('/'))
                else:
                    # 相对路径
                    full_path = os.path.normpath(os.path.join(base_dir, url))
                
                # 移除锚点
                full_path = full_path.split('#')[0]
                
                if full_path and not os.path.exists(full_path):
                    issue = QualityIssue(
                        file_path=file_path,
                        line_number=0,
                        severity=Severity.WARNING,
                        category="链接检查",
                        message=f"链接指向的文件不存在: {url}",
                        suggestion=f"检查链接路径或创建目标文件: {full_path}"
                    )
                    score.issues.append(issue)
    
    def _calculate_total_score(self, score: DocumentScore):
        """计算文档总分"""
        # 各项权重
        weights = {
            'content': 0.3,
            'format': 0.25,
            'structure': 0.25,
            'quality': 0.2
        }
        
        score.total_score = (
            score.content_score * weights['content'] +
            score.format_score * weights['format'] +
            score.structure_score * weights['structure'] +
            score.quality_score * weights['quality']
        )
        
        # 确保分数在0-100之间
        score.total_score = max(0, min(100, score.total_score))
    
    def generate_report(self, output_path: str):
        """生成质量报告"""
        # 确保输出目录存在
        os.makedirs(os.path.dirname(output_path), exist_ok=True)
        
        # 按总分排序
        sorted_scores = sorted(self.scores, key=lambda x: x.total_score)
        
        # 统计信息
        total_files = len(self.scores)
        error_count = sum(1 for s in self.scores for i in s.issues if i.severity == Severity.ERROR)
        warning_count = sum(1 for s in self.scores for i in s.issues if i.severity == Severity.WARNING)
        info_count = sum(1 for s in self.scores for i in s.issues if i.severity == Severity.INFO)
        
        avg_score = sum(s.total_score for s in self.scores) / total_files if total_files > 0 else 0
        
        # 生成报告
        report_lines = [
            "# FormalMath项目文档质量检查报告",
            "",
            f"**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
            f"**检查文件数**: {total_files}",
            f"**平均得分**: {avg_score:.1f}/100",
            "",
            "## 📊 统计概览",
            "",
            "| 指标 | 数值 |",
            "|------|------|",
            f"| 检查文件总数 | {total_files} |",
            f"| 平均质量得分 | {avg_score:.1f} |",
            f"| 错误数量 | {error_count} |",
            f"| 警告数量 | {warning_count} |",
            f"| 信息数量 | {info_count} |",
            "",
            "## 🎯 质量评级分布",
            "",
        ]
        
        # 评级分布
        excellent = sum(1 for s in self.scores if s.total_score >= 90)
        good = sum(1 for s in self.scores if 80 <= s.total_score < 90)
        acceptable = sum(1 for s in self.scores if 60 <= s.total_score < 80)
        poor = sum(1 for s in self.scores if s.total_score < 60)
        
        report_lines.extend([
            "| 评级 | 分数范围 | 文件数 |",
            "|------|----------|--------|",
            f"| 🟢 优秀 | 90-100 | {excellent} |",
            f"| 🟡 良好 | 80-89 | {good} |",
            f"| 🟠 及格 | 60-79 | {acceptable} |",
            f"| 🔴 需改进 | 0-59 | {poor} |",
            "",
            "## ⚠️ 低质量文档列表（分数<60）",
            "",
        ])
        
        # 低质量文档
        low_quality = [s for s in sorted_scores if s.total_score < 60]
        if low_quality:
            report_lines.append("| 文件路径 | 得分 | 问题数 |")
            report_lines.append("|----------|------|--------|")
            for s in low_quality[:20]:  # 最多显示20个
                issue_count = len([i for i in s.issues if i.severity in (Severity.ERROR, Severity.WARNING)])
                report_lines.append(f"| {s.file_path} | {s.total_score:.1f} | {issue_count} |")
            
            if len(low_quality) > 20:
                report_lines.append(f"| ... 还有 {len(low_quality) - 20} 个文件 | | |")
        else:
            report_lines.append("✅ 所有文档质量均达到及格标准！")
        
        report_lines.extend([
            "",
            "## 📋 详细检查结果",
            "",
        ])
        
        # 详细结果
        for score in sorted_scores:
            grade = "🟢" if score.total_score >= 90 else "🟡" if score.total_score >= 80 else "🟠" if score.total_score >= 60 else "🔴"
            
            report_lines.extend([
                f"### {grade} {score.file_path}",
                "",
                f"**总分**: {score.total_score:.1f}/100",
                f"**内容得分**: {score.content_score:.1f} | **格式得分**: {score.format_score:.1f} | **结构得分**: {score.structure_score:.1f} | **质量得分**: {score.quality_score:.1f}",
                f"**字数**: {score.word_count} | **字符数**: {score.char_count} | **章节数**: {score.section_count}",
                "",
            ])
            
            if score.issues:
                report_lines.append("#### 发现的问题")
                report_lines.append("")
                report_lines.append("| 行号 | 严重程度 | 类别 | 问题描述 | 建议 |")
                report_lines.append("|------|----------|------|----------|------|")
                
                # 按严重程度排序
                severity_order = {Severity.ERROR: 0, Severity.WARNING: 1, Severity.INFO: 2}
                sorted_issues = sorted(score.issues, key=lambda x: severity_order.get(x.severity, 3))
                
                for issue in sorted_issues[:10]:  # 每个文件最多显示10个问题
                    severity_emoji = "🔴" if issue.severity == Severity.ERROR else "🟡" if issue.severity == Severity.WARNING else "🔵"
                    suggestion = issue.suggestion[:50] + "..." if len(issue.suggestion) > 50 else issue.suggestion
                    message = issue.message[:50] + "..." if len(issue.message) > 50 else issue.message
                    report_lines.append(f"| {issue.line_number} | {severity_emoji} {issue.severity.value} | {issue.category} | {message} | {suggestion} |")
                
                if len(score.issues) > 10:
                    report_lines.append(f"| | | | ... 还有 {len(score.issues) - 10} 个问题 | |")
                
                report_lines.append("")
        
        # 写入报告
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write('\n'.join(report_lines))
        
        print(f"质量报告已生成: {output_path}")
        print(f"共检查 {total_files} 个文件")
        print(f"平均得分: {avg_score:.1f}/100")
        print(f"问题统计: {error_count} 个错误, {warning_count} 个警告, {info_count} 个信息")


def main():
    parser = argparse.ArgumentParser(
        description="FormalMath项目文档质量检查工具",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
    python tools/quality_checker.py
    python tools/quality_checker.py --path docs/01-基础数学 --strict
    python tools/quality_checker.py --min-size 3000 --output report.md
        """
    )
    
    parser.add_argument(
        '--path', '-p',
        nargs='+',
        default=['docs/', 'concept/'],
        help='要检查的目录或文件路径（默认: docs/ concept/）'
    )
    parser.add_argument(
        '--output', '-o',
        default='output/quality_report.md',
        help='输出报告路径（默认: output/quality_report.md）'
    )
    parser.add_argument(
        '--min-size',
        type=int,
        default=2000,
        help='最小文件大小（字节，默认: 2000）'
    )
    parser.add_argument(
        '--strict',
        action='store_true',
        help='启用严格模式'
    )
    parser.add_argument(
        '--fix',
        action='store_true',
        help='尝试自动修复部分问题（开发中）'
    )
    
    args = parser.parse_args()
    
    # 创建检查器
    checker = DocumentQualityChecker(
        min_size=args.min_size,
        strict=args.strict
    )
    
    # 执行检查
    print(f"开始检查文档质量...")
    print(f"检查路径: {', '.join(args.path)}")
    print(f"最小文件大小: {args.min_size} 字节")
    print(f"严格模式: {'开启' if args.strict else '关闭'}")
    print()
    
    checker.check_all(args.path)
    checker.generate_report(args.output)
    
    # 返回非零退出码（如果有错误）
    error_count = sum(
        1 for s in checker.scores
        for i in s.issues
        if i.severity == Severity.ERROR
    )
    
    if error_count > 0:
        print(f"\n⚠️ 发现 {error_count} 个错误，请修复后重新检查")
        sys.exit(1)
    else:
        print("\n✅ 检查完成，未发现错误")
        sys.exit(0)


if __name__ == '__main__':
    main()
