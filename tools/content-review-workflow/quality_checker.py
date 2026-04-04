#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
内容质量检查器
Content Quality Checker

提供全面的文档质量检查功能，包括结构、内容、格式等方面。
"""

import re
import os
import yaml
import json
from pathlib import Path
from typing import Dict, List, Tuple, Optional, Any
from dataclasses import dataclass, asdict
from enum import Enum
import logging

# 配置日志
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)


class Severity(Enum):
    """问题严重级别"""
    ERROR = "error"
    WARNING = "warning"
    INFO = "info"


@dataclass
class Issue:
    """质量问题记录"""
    rule_name: str
    severity: Severity
    message: str
    location: Optional[str] = None
    suggestion: Optional[str] = None
    
    def to_dict(self) -> Dict:
        return {
            "rule_name": self.rule_name,
            "severity": self.severity.value,
            "message": self.message,
            "location": self.location,
            "suggestion": self.suggestion
        }


@dataclass
class QualityReport:
    """质量检查报告"""
    document_path: str
    total_checks: int
    passed_checks: int
    issues: List[Issue]
    score: float
    timestamp: str
    
    def to_dict(self) -> Dict:
        return {
            "document_path": self.document_path,
            "total_checks": self.total_checks,
            "passed_checks": self.passed_checks,
            "failed_checks": self.total_checks - self.passed_checks,
            "score": round(self.score, 2),
            "timestamp": self.timestamp,
            "issues": [issue.to_dict() for issue in self.issues],
            "summary": self._generate_summary()
        }
    
    def _generate_summary(self) -> Dict:
        error_count = sum(1 for i in self.issues if i.severity == Severity.ERROR)
        warning_count = sum(1 for i in self.issues if i.severity == Severity.WARNING)
        info_count = sum(1 for i in self.issues if i.severity == Severity.INFO)
        
        return {
            "errors": error_count,
            "warnings": warning_count,
            "infos": info_count,
            "status": "pass" if error_count == 0 else "fail"
        }


class QualityChecker:
    """内容质量检查器"""
    
    def __init__(self, rules_path: Optional[str] = None):
        """
        初始化质量检查器
        
        Args:
            rules_path: 规则配置文件路径，默认使用内置规则
        """
        self.issues: List[Issue] = []
        self.rules = self._load_rules(rules_path)
        self.standard_terms = self._load_standard_terms()
        
    def _load_rules(self, rules_path: Optional[str]) -> Dict:
        """加载审核规则"""
        if rules_path and os.path.exists(rules_path):
            with open(rules_path, 'r', encoding='utf-8') as f:
                return yaml.safe_load(f)
        
        # 默认规则路径
        default_path = Path(__file__).parent / "review_rules.yaml"
        if default_path.exists():
            with open(default_path, 'r', encoding='utf-8') as f:
                return yaml.safe_load(f)
        
        return {}
    
    def _load_standard_terms(self) -> List[str]:
        """加载标准术语表"""
        terms = []
        multilang_path = Path(__file__).parent.parent.parent / "multilang_concept_table.json"
        if multilang_path.exists():
            try:
                with open(multilang_path, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    for item in data.get("concepts", []):
                        if "chinese" in item:
                            terms.append(item["chinese"])
            except Exception as e:
                logger.warning(f"加载术语表失败: {e}")
        return terms
    
    def check_document(self, doc_path: str) -> QualityReport:
        """
        检查单个文档
        
        Args:
            doc_path: 文档路径
            
        Returns:
            QualityReport: 质量检查报告
        """
        self.issues = []
        doc_path = Path(doc_path)
        
        if not doc_path.exists():
            return self._create_error_report(str(doc_path), "文档不存在")
        
        content = doc_path.read_text(encoding='utf-8')
        
        # 执行各项检查
        checks = [
            self._check_structure,
            self._check_content_quality,
            self._check_formatting,
            self._check_links,
        ]
        
        for check in checks:
            try:
                check(content, str(doc_path))
            except Exception as e:
                logger.error(f"检查失败 {check.__name__}: {e}")
                self.issues.append(Issue(
                    rule_name=check.__name__,
                    severity=Severity.ERROR,
                    message=f"检查执行失败: {str(e)}"
                ))
        
        return self._generate_report(str(doc_path))
    
    def _check_structure(self, content: str, doc_path: str):
        """检查文档结构"""
        # 检查YAML frontmatter
        if not content.startswith('---'):
            self.issues.append(Issue(
                rule_name="yaml_frontmatter",
                severity=Severity.ERROR,
                message="文档缺少YAML前置元数据",
                suggestion="在文档开头添加 --- 包围的元数据块"
            ))
        else:
            # 解析YAML
            try:
                parts = content.split('---', 2)
                if len(parts) >= 2:
                    metadata = yaml.safe_load(parts[1])
                    if metadata:
                        # 检查必需字段
                        required = self.rules.get('quality_rules', {}).get('structure', [{}])[0].get('required', [])
                        for field in required:
                            if field not in metadata:
                                self.issues.append(Issue(
                                    rule_name="required_headers",
                                    severity=Severity.ERROR,
                                    message=f"缺少必需字段: {field}",
                                    suggestion=f"在YAML frontmatter中添加 {field} 字段"
                                ))
            except yaml.YAMLError as e:
                self.issues.append(Issue(
                    rule_name="yaml_frontmatter",
                    severity=Severity.ERROR,
                    message=f"YAML解析错误: {e}",
                    suggestion="检查YAML语法格式"
                ))
        
        # 检查章节完整性
        sections = re.findall(r'^##\s+(.+)$', content, re.MULTILINE)
        required_sections = self.rules.get('quality_rules', {}).get('structure', [{}])[1].get('required_sections', [])
        
        for section in required_sections:
            if not any(section in s for s in sections):
                self.issues.append(Issue(
                    rule_name="section_completeness",
                    severity=Severity.WARNING,
                    message=f"可能缺少章节: {section}",
                    suggestion=f"考虑添加 '{section}' 章节以完善文档结构"
                ))
    
    def _check_content_quality(self, content: str, doc_path: str):
        """检查内容质量"""
        # 获取纯文本内容（移除YAML frontmatter和代码块）
        text_content = re.sub(r'---.*?---', '', content, flags=re.DOTALL)
        text_content = re.sub(r'```.*?```', '', text_content, flags=re.DOTALL)
        text_content = re.sub(r'`[^`]+`', '', text_content)
        
        # 检查内容长度
        min_length = self.rules.get('quality_rules', {}).get('content', [{}])[0].get('min_length', 200)
        if len(text_content.strip()) < min_length:
            self.issues.append(Issue(
                rule_name="min_content_length",
                severity=Severity.WARNING,
                message=f"内容长度不足，当前 {len(text_content)} 字符，建议至少 {min_length} 字符",
                suggestion="扩充文档内容，添加更多解释和示例"
            ))
        
        # 检查术语使用
        if self.standard_terms:
            non_standard_terms = []
            # 简单的术语检查：查找可能的不规范用法
            for term in self.standard_terms[:50]:  # 限制检查数量以提高性能
                # 这里可以添加更复杂的术语匹配逻辑
                pass
    
    def _check_formatting(self, content: str, doc_path: str):
        """检查格式规范"""
        # 检查行尾空格
        lines_with_trailing = []
        for i, line in enumerate(content.split('\n'), 1):
            if line.endswith(' ') or line.endswith('\t'):
                lines_with_trailing.append(i)
        
        if lines_with_trailing:
            self.issues.append(Issue(
                rule_name="markdown_lint",
                severity=Severity.INFO,
                message=f"发现 {len(lines_with_trailing)} 行包含行尾空白字符",
                location=f"行: {lines_with_trailing[:5]}..." if len(lines_with_trailing) > 5 else f"行: {lines_with_trailing}",
                suggestion="删除行尾多余的空格或制表符"
            ))
        
        # 检查标题层级
        headings = re.findall(r'^(#{1,6})\s', content, re.MULTILINE)
        if headings:
            levels = [len(h) for h in headings]
            for i in range(1, len(levels)):
                if levels[i] > levels[i-1] + 1:
                    self.issues.append(Issue(
                        rule_name="markdown_lint",
                        severity=Severity.WARNING,
                        message="标题层级跳跃",
                        suggestion="确保标题层级连续，不要从 # 直接跳到 ###"
                    ))
                    break
        
        # 检查代码块语言标记
        code_blocks = re.findall(r'```(\w*)', content)
        empty_lang_blocks = sum(1 for lang in code_blocks if not lang)
        if empty_lang_blocks > 0:
            self.issues.append(Issue(
                rule_name="markdown_lint",
                severity=Severity.INFO,
                message=f"发现 {empty_lang_blocks} 个未指定语言的代码块",
                suggestion="为代码块添加语言标记，如 ```python"
            ))
    
    def _check_links(self, content: str, doc_path: str):
        """检查链接"""
        # 提取内部链接
        internal_links = re.findall(r'\]\(([^)]+\.md)\)', content)
        doc_dir = Path(doc_path).parent
        
        broken_links = []
        for link in internal_links:
            # 处理相对路径
            if not link.startswith('http'):
                target = doc_dir / link
                if not target.exists():
                    broken_links.append(link)
        
        if broken_links:
            self.issues.append(Issue(
                rule_name="internal_links",
                severity=Severity.WARNING,
                message=f"发现 {len(broken_links)} 个无效内部链接",
                location=str(broken_links[:5]),
                suggestion="修复或更新链接路径"
            ))
    
    def _generate_report(self, doc_path: str) -> QualityReport:
        """生成检查报告"""
        from datetime import datetime
        
        # 计算得分
        error_count = sum(1 for i in self.issues if i.severity == Severity.ERROR)
        warning_count = sum(1 for i in self.issues if i.severity == Severity.WARNING)
        info_count = sum(1 for i in self.issues if i.severity == Severity.INFO)
        
        # 简单计分：错误扣10分，警告扣3分，信息扣1分，最低0分
        base_score = 100
        score = max(0, base_score - error_count * 10 - warning_count * 3 - info_count * 1)
        
        total_checks = 10  # 假设有10个检查项
        passed_checks = max(0, total_checks - error_count - warning_count // 2)
        
        return QualityReport(
            document_path=doc_path,
            total_checks=total_checks,
            passed_checks=passed_checks,
            issues=self.issues,
            score=score,
            timestamp=datetime.now().isoformat()
        )
    
    def _create_error_report(self, doc_path: str, error_message: str) -> QualityReport:
        """创建错误报告"""
        from datetime import datetime
        
        return QualityReport(
            document_path=doc_path,
            total_checks=0,
            passed_checks=0,
            issues=[Issue(
                rule_name="system",
                severity=Severity.ERROR,
                message=error_message
            )],
            score=0,
            timestamp=datetime.now().isoformat()
        )
    
    def batch_check(self, directory: str, pattern: str = "*.md") -> List[QualityReport]:
        """
        批量检查目录中的文档
        
        Args:
            directory: 目录路径
            pattern: 文件匹配模式
            
        Returns:
            List[QualityReport]: 质量检查报告列表
        """
        reports = []
        dir_path = Path(directory)
        
        if not dir_path.exists():
            logger.error(f"目录不存在: {directory}")
            return reports
        
        for file_path in dir_path.rglob(pattern):
            logger.info(f"检查文档: {file_path}")
            report = self.check_document(str(file_path))
            reports.append(report)
        
        return reports


def main():
    """命令行入口"""
    import argparse
    
    parser = argparse.ArgumentParser(description='内容质量检查器')
    parser.add_argument('path', help='要检查的文档或目录路径')
    parser.add_argument('--rules', '-r', help='规则配置文件路径')
    parser.add_argument('--output', '-o', help='输出报告路径')
    parser.add_argument('--format', '-f', choices=['json', 'md', 'html'], default='json',
                       help='输出格式')
    parser.add_argument('--batch', '-b', action='store_true', help='批量检查模式')
    
    args = parser.parse_args()
    
    checker = QualityChecker(args.rules)
    
    if args.batch or Path(args.path).is_dir():
        reports = checker.batch_check(args.path)
        output = {
            "total_documents": len(reports),
            "passed": sum(1 for r in reports if r.score >= 60),
            "failed": sum(1 for r in reports if r.score < 60),
            "average_score": sum(r.score for r in reports) / len(reports) if reports else 0,
            "reports": [r.to_dict() for r in reports]
        }
    else:
        report = checker.check_document(args.path)
        output = report.to_dict()
    
    # 输出报告
    if args.output:
        output_path = Path(args.output)
        if args.format == 'json':
            output_path.write_text(json.dumps(output, ensure_ascii=False, indent=2), encoding='utf-8')
        elif args.format == 'md':
            # 生成Markdown格式报告
            md_content = generate_markdown_report(output)
            output_path.write_text(md_content, encoding='utf-8')
        
        logger.info(f"报告已保存: {args.output}")
    else:
        print(json.dumps(output, ensure_ascii=False, indent=2))


def generate_markdown_report(output: Dict) -> str:
    """生成Markdown格式报告"""
    if "reports" in output:
        # 批量报告
        lines = [
            "# 批量质量检查报告\n",
            f"**检查文档数**: {output['total_documents']}\n",
            f"**通过**: {output['passed']}\n",
            f"**失败**: {output['failed']}\n",
            f"**平均得分**: {output['average_score']:.2f}\n",
            "\n## 详细报告\n"
        ]
        for report in output['reports']:
            lines.append(f"\n### {report['document_path']}\n")
            lines.append(f"- **得分**: {report['score']}\n")
            lines.append(f"- **状态**: {'通过' if report['summary']['status'] == 'pass' else '失败'}\n")
            if report['issues']:
                lines.append("- **问题**:\n")
                for issue in report['issues']:
                    lines.append(f"  - [{issue['severity'].upper()}] {issue['message']}\n")
        return ''.join(lines)
    else:
        # 单个报告
        lines = [
            "# 质量检查报告\n",
            f"**文档**: {output['document_path']}\n",
            f"**得分**: {output['score']}\n",
            f"**状态**: {'通过' if output['summary']['status'] == 'pass' else '失败'}\n",
            f"**时间**: {output['timestamp']}\n",
            "\n## 问题列表\n"
        ]
        for issue in output['issues']:
            lines.append(f"\n### [{issue['severity'].upper()}] {issue['rule_name']}\n")
            lines.append(f"{issue['message']}\n")
            if issue.get('location'):
                lines.append(f"- **位置**: {issue['location']}\n")
            if issue.get('suggestion'):
                lines.append(f"- **建议**: {issue['suggestion']}\n")
        return ''.join(lines)


if __name__ == "__main__":
    main()
