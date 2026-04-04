#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath 问题清单自动提取器
Issue Extractor for FormalMath

功能：自动提取内容质量问题并生成分类问题清单
作者：FormalMath AI
版本：1.0.0
"""

import json
import re
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Any, Set, Tuple
from collections import defaultdict
from dataclasses import dataclass, field, asdict


@dataclass
class IssueItem:
    """问题项"""
    id: str
    file_path: str
    file_name: str
    issue_type: str  # completeness, accuracy, readability, internationalization, learning_effect
    severity: str  # high, medium, low
    category: str  # 问题分类
    description: str
    suggestion: str
    line_number: int = 0
    context: str = ""
    related_elements: List[str] = field(default_factory=list)
    estimated_fix_time: int = 0  # 预估修复时间（分钟）
    priority_score: float = 0.0  # 优先级分数
    
    def calculate_priority(self):
        """计算优先级分数"""
        severity_weights = {'high': 10, 'medium': 5, 'low': 2}
        type_weights = {
            'completeness': 1.0,
            'accuracy': 1.2,  # 准确性问题优先级更高
            'readability': 0.8,
            'internationalization': 0.6,
            'learning_effect': 0.7
        }
        
        severity_score = severity_weights.get(self.severity, 1)
        type_score = type_weights.get(self.issue_type, 1.0)
        
        self.priority_score = severity_score * type_score
        return self.priority_score


@dataclass
class IssueCategory:
    """问题分类"""
    name: str
    description: str
    issue_count: int = 0
    high_severity_count: int = 0
    affected_files: Set[str] = field(default_factory=set)
    
    @property
    def severity_ratio(self) -> float:
        """严重问题比例"""
        if self.issue_count == 0:
            return 0.0
        return self.high_severity_count / self.issue_count


class IssueExtractor:
    """问题提取器"""
    
    # 问题分类定义
    ISSUE_CATEGORIES = {
        'missing_content': {
            'name': '内容缺失',
            'description': '文档缺少必要的内容元素',
            'patterns': [
                r'缺少(?:概念|定义)',
                r'缺少(?:定理|证明)',
                r'缺少示例',
                r'缺少(?:参考|引用)',
                r'缺少MSC',
            ]
        },
        'formula_error': {
            'name': '公式错误',
            'description': '数学公式存在语法或格式错误',
            'patterns': [
                r'公式.*(?:错误|语法)',
                r'括号.*不匹配',
                r'(?:LaTeX|MathJax).*错误',
            ]
        },
        'citation_issue': {
            'name': '引用问题',
            'description': '引用格式不规范或链接失效',
            'patterns': [
                r'引用.*(?:错误|格式)',
                r'链接.*(?:失效|断开)',
                r'文献.*缺失',
            ]
        },
        'notation_inconsistency': {
            'name': '符号不一致',
            'description': '数学符号使用不统一',
            'patterns': [
                r'符号.*不一致',
                r'记号.*混用',
                r'(?:epsilon|phi|emptyset).*混用',
            ]
        },
        'readability_issue': {
            'name': '可读性问题',
            'description': '文档可读性需要改进',
            'patterns': [
                r'句子.*过长',
                r'段落.*过长',
                r'结构.*不清晰',
                r'层级.*混乱',
            ]
        },
        'i18n_issue': {
            'name': '国际化问题',
            'description': '多语言内容存在问题',
            'patterns': [
                r'术语.*不一致',
                r'翻译.*混用',
                r'缺少.*英文',
                r'国际化',
            ]
        },
        'learning_issue': {
            'name': '学习效果问题',
            'description': '影响学习效果的内容问题',
            'patterns': [
                r'前置.*(?:不清|缺失)',
                r'练习.*(?:不足|单一)',
                r'难度.*不匹配',
            ]
        },
    }
    
    def __init__(self):
        self.issues: List[IssueItem] = []
        self.categories: Dict[str, IssueCategory] = {}
        self._init_categories()
        
    def _init_categories(self):
        """初始化问题分类"""
        for key, config in self.ISSUE_CATEGORIES.items():
            self.categories[key] = IssueCategory(
                name=config['name'],
                description=config['description']
            )
    
    def extract_from_result(self, result: Dict[str, Any]) -> List[IssueItem]:
        """从评估结果中提取问题"""
        extracted_issues = []
        
        file_path = result.get('file_path', '')
        file_name = result.get('file_name', '')
        
        for issue_data in result.get('issues', []):
            # 确定问题分类
            category = self._categorize_issue(issue_data)
            
            # 生成唯一ID
            issue_id = self._generate_issue_id(file_name, issue_data)
            
            # 估算修复时间
            fix_time = self._estimate_fix_time(issue_data, category)
            
            issue = IssueItem(
                id=issue_id,
                file_path=file_path,
                file_name=file_name,
                issue_type=issue_data.get('type', 'unknown'),
                severity=issue_data.get('severity', 'low'),
                category=category,
                description=issue_data.get('description', ''),
                suggestion=issue_data.get('suggestion', ''),
                estimated_fix_time=fix_time
            )
            
            issue.calculate_priority()
            extracted_issues.append(issue)
            
            # 更新分类统计
            if category in self.categories:
                self.categories[category].issue_count += 1
                self.categories[category].affected_files.add(file_path)
                if issue.severity == 'high':
                    self.categories[category].high_severity_count += 1
        
        self.issues.extend(extracted_issues)
        return extracted_issues
    
    def _categorize_issue(self, issue_data: Dict[str, Any]) -> str:
        """对问题进行分类"""
        description = issue_data.get('description', '')
        issue_type = issue_data.get('type', '')
        
        # 根据描述匹配分类模式
        for category_key, config in self.ISSUE_CATEGORIES.items():
            for pattern in config['patterns']:
                if re.search(pattern, description, re.I):
                    return category_key
        
        # 根据类型映射
        type_mapping = {
            'completeness': 'missing_content',
            'accuracy': 'formula_error',
            'readability': 'readability_issue',
            'internationalization': 'i18n_issue',
            'learning_effect': 'learning_issue'
        }
        
        return type_mapping.get(issue_type, 'other')
    
    def _generate_issue_id(self, file_name: str, issue_data: Dict[str, Any]) -> str:
        """生成问题唯一ID"""
        import hashlib
        
        content = f"{file_name}:{issue_data.get('description', '')}"
        hash_obj = hashlib.md5(content.encode())
        return f"ISS-{hash_obj.hexdigest()[:8].upper()}"
    
    def _estimate_fix_time(self, issue_data: Dict[str, Any], category: str) -> int:
        """估算修复时间（分钟）"""
        severity = issue_data.get('severity', 'low')
        
        # 基础时间
        base_time = {
            'high': 60,
            'medium': 30,
            'low': 15
        }.get(severity, 15)
        
        # 分类调整
        category_multiplier = {
            'missing_content': 1.5,
            'formula_error': 1.2,
            'citation_issue': 0.8,
            'notation_inconsistency': 1.0,
            'readability_issue': 0.7,
            'i18n_issue': 1.3,
            'learning_issue': 1.0
        }.get(category, 1.0)
        
        return int(base_time * category_multiplier)
    
    def analyze_patterns(self) -> Dict[str, Any]:
        """分析问题模式"""
        patterns = {
            'common_issues': self._find_common_issues(),
            'file_patterns': self._analyze_file_patterns(),
            'severity_distribution': self._get_severity_distribution(),
            'type_distribution': self._get_type_distribution(),
        }
        return patterns
    
    def _find_common_issues(self, top_n: int = 10) -> List[Dict]:
        """查找最常见的问题"""
        issue_counts = defaultdict(lambda: {'count': 0, 'files': set(), 'severity': ''})
        
        for issue in self.issues:
            key = issue.description
            issue_counts[key]['count'] += 1
            issue_counts[key]['files'].add(issue.file_path)
            issue_counts[key]['severity'] = issue.severity
            issue_counts[key]['suggestion'] = issue.suggestion
        
        # 排序并返回前N个
        sorted_issues = sorted(
            issue_counts.items(),
            key=lambda x: x[1]['count'],
            reverse=True
        )[:top_n]
        
        return [
            {
                'description': desc,
                'count': data['count'],
                'affected_files': len(data['files']),
                'severity': data['severity'],
                'suggestion': data['suggestion']
            }
            for desc, data in sorted_issues
        ]
    
    def _analyze_file_patterns(self) -> Dict[str, Any]:
        """分析文件模式"""
        file_issues = defaultdict(list)
        
        for issue in self.issues:
            file_issues[issue.file_path].append(issue)
        
        # 问题最多的文件
        most_issues = sorted(
            file_issues.items(),
            key=lambda x: len(x[1]),
            reverse=True
        )[:10]
        
        return {
            'files_with_most_issues': [
                {
                    'file': f,
                    'issue_count': len(issues),
                    'severity_score': sum(i.priority_score for i in issues)
                }
                for f, issues in most_issues
            ],
            'total_affected_files': len(file_issues)
        }
    
    def _get_severity_distribution(self) -> Dict[str, int]:
        """获取严重程度分布"""
        distribution = defaultdict(int)
        for issue in self.issues:
            distribution[issue.severity] += 1
        return dict(distribution)
    
    def _get_type_distribution(self) -> Dict[str, int]:
        """获取类型分布"""
        distribution = defaultdict(int)
        for issue in self.issues:
            distribution[issue.issue_type] += 1
        return dict(distribution)
    
    def generate_action_plan(self) -> Dict[str, Any]:
        """生成行动计划"""
        # 按优先级排序问题
        sorted_issues = sorted(
            self.issues,
            key=lambda x: (x.priority_score, x.severity),
            reverse=True
        )
        
        # 分阶段计划
        phases = {
            'immediate': [],  # 立即处理（高优先级）
            'short_term': [],  # 短期（1周内）
            'medium_term': [],  # 中期（1个月内）
            'long_term': []   # 长期（持续改进）
        }
        
        for issue in sorted_issues:
            if issue.priority_score >= 10:
                phases['immediate'].append(issue)
            elif issue.priority_score >= 6:
                phases['short_term'].append(issue)
            elif issue.priority_score >= 3:
                phases['medium_term'].append(issue)
            else:
                phases['long_term'].append(issue)
        
        # 计算各阶段工作量
        phase_stats = {}
        for phase_name, phase_issues in phases.items():
            total_time = sum(i.estimated_fix_time for i in phase_issues)
            phase_stats[phase_name] = {
                'issue_count': len(phase_issues),
                'estimated_hours': round(total_time / 60, 1),
                'high_severity_count': sum(1 for i in phase_issues if i.severity == 'high')
            }
        
        return {
            'phases': {
                name: [asdict(i) for i in issues[:20]]  # 每阶段最多显示20个
                for name, issues in phases.items()
            },
            'phase_stats': phase_stats,
            'total_estimated_hours': sum(s['estimated_hours'] for s in phase_stats.values())
        }
    
    def generate_issue_report(self, output_path: str = None) -> str:
        """生成问题清单报告"""
        
        if output_path is None:
            output_path = self.output_dir / "issue_report.md"
        else:
            output_path = Path(output_path)
        
        # 分析问题
        patterns = self.analyze_patterns()
        action_plan = self.generate_action_plan()
        
        lines = [
            "# FormalMath 内容质量问题清单",
            "",
            f"**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
            f"**问题总数**: {len(self.issues)}",
            f"**涉及文件**: {patterns['file_patterns']['total_affected_files']}",
            "",
            "## 📊 问题概览",
            "",
            "### 严重程度分布",
            "",
        ]
        
        for severity, count in patterns['severity_distribution'].items():
            icon = {'high': '🔴', 'medium': '🟡', 'low': '🔵'}.get(severity, '⚪')
            lines.append(f"- {icon} **{severity.upper()}**: {count} 个")
        
        lines.extend(["", "### 问题类型分布", ""])
        
        for issue_type, count in sorted(patterns['type_distribution'].items(), key=lambda x: -x[1]):
            lines.append(f"- **{issue_type}**: {count} 个")
        
        lines.extend(["", "### 分类统计", ""])
        
        for key, category in sorted(self.categories.items(), key=lambda x: -x[1].issue_count):
            if category.issue_count > 0:
                lines.append(f"#### {category.name}")
                lines.append(f"- 问题数: {category.issue_count}")
                lines.append(f"- 高严重问题: {category.high_severity_count}")
                lines.append(f"- 影响文件: {len(category.affected_files)}")
                lines.append(f"- 描述: {category.description}")
                lines.append("")
        
        lines.extend(["", "## 🔥 常见问题", "" ])
        
        for i, common in enumerate(patterns['common_issues'][:10], 1):
            lines.append(f"### {i}. {common['description'][:50]}...")
            lines.append(f"- 出现次数: {common['count']}")
            lines.append(f"- 影响文件: {common['affected_files']}")
            lines.append(f"- 严重程度: {common['severity']}")
            lines.append(f"- 建议: {common['suggestion']}")
            lines.append("")
        
        lines.extend(["", "## 📋 行动计划", ""])
        
        for phase_name, stats in action_plan['phase_stats'].items():
            phase_title = {
                'immediate': '🔴 立即处理',
                'short_term': '🟡 短期计划（1周内）',
                'medium_term': '🔵 中期计划（1个月内）',
                'long_term': '⚪ 长期计划（持续改进）'
            }.get(phase_name, phase_name)
            
            lines.append(f"### {phase_title}")
            lines.append(f"- 问题数: {stats['issue_count']}")
            lines.append(f"- 预估工时: {stats['estimated_hours']} 小时")
            lines.append(f"- 高严重问题: {stats['high_severity_count']}")
            lines.append("")
            
            # 列出该阶段的问题
            phase_issues = action_plan['phases'][phase_name][:5]
            if phase_issues:
                lines.append("**主要问题**:")
                for issue in phase_issues:
                    lines.append(f"- [{issue['id']}] {issue['description'][:60]}... ({issue['file_name']})")
                lines.append("")
        
        lines.extend([
            "",
            f"**预估总工时**: {action_plan['total_estimated_hours']} 小时",
            "",
            "## 📁 详细问题列表",
            "",
        ])
        
        # 按文件分组显示问题
        file_issues = defaultdict(list)
        for issue in self.issues:
            file_issues[issue.file_path].append(issue)
        
        for file_path, issues in sorted(file_issues.items()):
            lines.append(f"### {Path(file_path).name}")
            lines.append(f"**路径**: `{file_path}`")
            lines.append("")
            
            for issue in sorted(issues, key=lambda x: -x.priority_score):
                severity_icon = {'high': '🔴', 'medium': '🟡', 'low': '🔵'}.get(issue.severity, '⚪')
                lines.append(f"#### {severity_icon} [{issue.id}] {issue.description[:60]}")
                lines.append(f"- **类型**: {issue.issue_type}")
                lines.append(f"- **分类**: {self.categories.get(issue.category, IssueCategory(name=issue.category, description='')).name}")
                lines.append(f"- **优先级**: {issue.priority_score:.1f}")
                lines.append(f"- **预估修复时间**: {issue.estimated_fix_time} 分钟")
                lines.append(f"- **建议**: {issue.suggestion}")
                lines.append("")
        
        output_path.write_text('\n'.join(lines), encoding='utf-8')
        return str(output_path)
    
    def export_issues_json(self, output_path: str = None) -> str:
        """导出JSON格式的问题清单"""
        
        if output_path is None:
            output_path = self.output_dir / "issues.json"
        else:
            output_path = Path(output_path)
        
        data = {
            'metadata': {
                'generated_at': datetime.now().isoformat(),
                'total_issues': len(self.issues),
                'categories': {k: asdict(v) for k, v in self.categories.items()}
            },
            'issues': [asdict(i) for i in self.issues],
            'analysis': self.analyze_patterns(),
            'action_plan': self.generate_action_plan()
        }
        
        output_path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding='utf-8')
        return str(output_path)
    
    def get_fix_checklist(self) -> List[Dict]:
        """生成修复检查清单"""
        checklist = []
        
        for issue in sorted(self.issues, key=lambda x: -x.priority_score):
            checklist.append({
                'id': issue.id,
                'file': issue.file_name,
                'description': issue.description,
                'severity': issue.severity,
                'estimated_time': issue.estimated_fix_time,
                'status': 'pending',
                'assigned_to': '',
                'completed_at': None
            })
        
        return checklist


class BatchIssueProcessor:
    """批量问题处理器"""
    
    def __init__(self, extractor: IssueExtractor):
        self.extractor = extractor
        
    def process_assessment_results(self, results_file: str):
        """处理评估结果文件"""
        results_path = Path(results_file)
        
        if not results_path.exists():
            raise FileNotFoundError(f"结果文件不存在: {results_file}")
        
        with open(results_path, 'r', encoding='utf-8') as f:
            data = json.load(f)
        
        results = data.get('results', [])
        
        for result in results:
            self.extractor.extract_from_result(result)
        
        print(f"已处理 {len(results)} 个评估结果，提取 {len(self.extractor.issues)} 个问题")
        
        return self.extractor


def main():
    """主函数 - 示例用法"""
    from quality_assessor import ContentQualityAssessor
    
    # 创建评估器并评估
    assessor = ContentQualityAssessor()
    results = assessor.assess_directory("../../docs/01-基础数学/集合论")
    
    # 创建提取器并提取问题
    extractor = IssueExtractor()
    
    for result in results:
        extractor.extract_from_result(result.__dict__)
    
    # 生成报告
    report_path = extractor.generate_issue_report()
    print(f"问题清单报告已生成: {report_path}")
    
    json_path = extractor.export_issues_json()
    print(f"JSON格式问题清单已导出: {json_path}")
    
    # 打印统计
    patterns = extractor.analyze_patterns()
    print(f"\n问题统计:")
    print(f"- 总问题数: {len(extractor.issues)}")
    print(f"- 影响文件数: {patterns['file_patterns']['total_affected_files']}")
    print(f"- 高优先级问题: {patterns['severity_distribution'].get('high', 0)}")


if __name__ == '__main__':
    main()
