#!/usr/bin/env python3
"""
FormalMath 质量控制系统
提供文档质量检查、评分和改进建议
"""

import os
import re
import yaml
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Set
from dataclasses import dataclass, field
from enum import Enum


class QualityLevel(Enum):
    """质量等级"""
    EXCELLENT = "优秀"      # 90-100
    GOOD = "良好"          # 80-89
    ACCEPTABLE = "可接受"   # 70-79
    NEEDS_IMPROVEMENT = "需改进"  # 60-69
    POOR = "差"            # <60


@dataclass
class QualityReport:
    """质量报告"""
    filepath: str
    title: Optional[str] = None
    overall_score: int = 0
    level: QualityLevel = QualityLevel.POOR
    checks: Dict[str, Dict] = field(default_factory=dict)
    suggestions: List[str] = field(default_factory=list)
    errors: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)
    
    def to_dict(self) -> Dict:
        return {
            'filepath': self.filepath,
            'title': self.title,
            'overall_score': self.overall_score,
            'level': self.level.value,
            'checks': self.checks,
            'suggestions': self.suggestions,
            'errors': self.errors,
            'warnings': self.warnings
        }


class QualityControl:
    """质量控制器"""
    
    # 必需元数据字段
    REQUIRED_FIELDS = ['title', 'created_date', 'version']
    
    # 推荐元数据字段
    RECOMMENDED_FIELDS = ['msc_primary', 'category', 'difficulty', 'author', 'status']
    
    # 数学术语标准写法
    STANDARD_TERMS = {
        '群': '群',
        '环': '环',
        '域': '域',
        '拓扑': '拓扑',
        '流形': '流形',
        '同态': '同态',
        '同构': '同构',
        '同伦': '同伦',
        '同调': '同调',
        '范畴': '范畴',
        '函子': '函子',
    }
    
    # 常见符号错误
    COMMON_SYMBOL_ERRORS = [
        (r'(?<![\\\w])epsilon(?![\w])', 'ε 应使用 \\epsilon'),
        (r'(?<![\\\w])delta(?![\w])', 'δ 应使用 \\delta'),
        (r'(?<![\\\w])sigma(?![\w])', 'σ 应使用 \\sigma'),
        (r'(?<![\\\w])alpha(?![\w])', 'α 应使用 \\alpha'),
        (r'(?<![\\\w])beta(?![\w])', 'β 应使用 \\beta'),
    ]
    
    def __init__(self, root_dir: str = '.'):
        self.root_dir = Path(root_dir)
        self.reports: List[QualityReport] = []
    
    def check_file(self, filepath: Path) -> QualityReport:
        """
        检查单个文件质量
        
        Args:
            filepath: 文件路径
        
        Returns:
            质量报告
        """
        report = QualityReport(filepath=str(filepath.relative_to(self.root_dir)))
        
        try:
            content = filepath.read_text(encoding='utf-8')
        except Exception as e:
            report.errors.append(f"无法读取文件: {e}")
            return report
        
        # 解析元数据
        metadata = self._extract_metadata(content)
        report.title = metadata.get('title') or self._extract_title(content)
        
        # 执行各项检查
        checks = {
            'metadata_completeness': self._check_metadata_completeness(metadata),
            'content_structure': self._check_content_structure(content),
            'notation_consistency': self._check_notation_consistency(content),
            'reference_validity': self._check_references(content),
            'format_compliance': self._check_format_compliance(content),
            'accessibility': self._check_accessibility(content),
        }
        
        report.checks = checks
        
        # 计算总分
        total_score = sum(c['score'] * c['weight'] for c in checks.values())
        report.overall_score = int(total_score / sum(c['weight'] for c in checks.values()))
        report.level = self._score_to_level(report.overall_score)
        
        # 生成建议
        report.suggestions = self._generate_suggestions(report, checks)
        
        # 收集错误和警告
        for check_name, check_result in checks.items():
            report.errors.extend(check_result.get('errors', []))
            report.warnings.extend(check_result.get('warnings', []))
        
        return report
    
    def _extract_metadata(self, content: str) -> Dict:
        """提取元数据"""
        yaml_pattern = re.compile(r'^---\s*\n(.*?)\n---\s*\n', re.DOTALL)
        match = yaml_pattern.match(content)
        
        if match:
            try:
                return yaml.safe_load(match.group(1)) or {}
            except yaml.YAMLError:
                return {}
        return {}
    
    def _extract_title(self, content: str) -> Optional[str]:
        """提取标题"""
        match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
        if match:
            return match.group(1).strip()
        return None
    
    def _check_metadata_completeness(self, metadata: Dict) -> Dict:
        """检查元数据完整性"""
        result = {
            'score': 100,
            'weight': 25,
            'errors': [],
            'warnings': [],
            'details': {}
        }
        
        # 检查必需字段
        missing_required = [f for f in self.REQUIRED_FIELDS if not metadata.get(f)]
        if missing_required:
            result['errors'].append(f"缺少必需字段: {', '.join(missing_required)}")
            result['score'] -= len(missing_required) * 20
        
        # 检查推荐字段
        missing_recommended = [f for f in self.RECOMMENDED_FIELDS if not metadata.get(f)]
        if missing_recommended:
            result['warnings'].append(f"缺少推荐字段: {', '.join(missing_recommended)}")
            result['score'] -= len(missing_recommended) * 5
        
        # 检查 MSC 格式
        if metadata.get('msc_primary'):
            if not re.match(r'^\d{2}[A-Z0-9]{0,2}$', str(metadata['msc_primary'])):
                result['warnings'].append(f"MSC主分类格式可能不正确: {metadata['msc_primary']}")
                result['score'] -= 10
        
        # 检查日期格式
        if metadata.get('created_date'):
            try:
                datetime.strptime(str(metadata['created_date']), '%Y-%m-%d')
            except ValueError:
                result['warnings'].append(f"日期格式不正确，应使用 YYYY-MM-DD: {metadata['created_date']}")
                result['score'] -= 10
        
        # 检查版本格式
        if metadata.get('version'):
            if not re.match(r'^\d+\.\d+\.\d+$', str(metadata['version'])):
                result['warnings'].append(f"版本号格式不正确，应使用 x.y.z: {metadata['version']}")
                result['score'] -= 5
        
        result['score'] = max(0, result['score'])
        return result
    
    def _check_content_structure(self, content: str) -> Dict:
        """检查内容结构"""
        result = {
            'score': 100,
            'weight': 25,
            'errors': [],
            'warnings': [],
            'details': {}
        }
        
        # 检查是否有标题
        if not re.search(r'^#\s+', content, re.MULTILINE):
            result['errors'].append("文档缺少主标题")
            result['score'] -= 30
        
        # 检查标题层级
        h2_count = len(re.findall(r'^##\s+', content, re.MULTILINE))
        h3_count = len(re.findall(r'^###\s+', content, re.MULTILINE))
        
        if h2_count == 0:
            result['warnings'].append("建议使用二级标题组织内容")
            result['score'] -= 10
        
        # 检查内容长度
        text_length = len(re.sub(r'[#*_`\[\]()]', '', content))
        result['details']['text_length'] = text_length
        
        if text_length < 500:
            result['warnings'].append("内容较短，建议补充详细信息")
            result['score'] -= 15
        elif text_length > 10000:
            result['details']['note'] = "内容较长，考虑拆分为多篇文档"
        
        # 检查是否有证明
        has_proof = bool(re.search(r'#{1,3}\s*证明|Proof', content, re.IGNORECASE))
        result['details']['has_proof'] = has_proof
        
        # 检查是否有例子
        has_example = bool(re.search(r'#{1,3}\s*例[子题]?|Example', content, re.IGNORECASE))
        result['details']['has_example'] = has_example
        
        # 检查是否有定义
        has_definition = bool(re.search(r'#{1,3}\s*定义|Definition', content, re.IGNORECASE))
        result['details']['has_definition'] = has_definition
        
        if not has_definition and not has_example:
            result['warnings'].append("建议添加定义或例子部分")
            result['score'] -= 10
        
        result['score'] = max(0, result['score'])
        return result
    
    def _check_notation_consistency(self, content: str) -> Dict:
        """检查符号一致性"""
        result = {
            'score': 100,
            'weight': 20,
            'errors': [],
            'warnings': [],
            'details': {}
        }
        
        # 检查常见符号错误
        for pattern, message in self.COMMON_SYMBOL_ERRORS:
            matches = re.findall(pattern, content)
            if matches:
                result['warnings'].append(f"{message} (发现 {len(matches)} 次)")
                result['score'] -= 5 * min(len(matches), 5)
        
        # 检查 LaTeX 公式语法
        inline_math = re.findall(r'(?<!\\)\$(.+?)(?<!\\)\$', content)
        display_math = re.findall(r'\$\$(.+?)\$\$', content, re.DOTALL)
        
        result['details']['inline_math_count'] = len(inline_math)
        result['details']['display_math_count'] = len(display_math)
        
        # 检查未闭合的公式
        odd_dollars = content.count('$') % 2 != 0
        if odd_dollars:
            result['errors'].append("检测到未闭合的 $ 符号")
            result['score'] -= 20
        
        # 检查术语一致性
        for term, standard in self.STANDARD_TERMS.items():
            # 检查是否有其他写法
            variations = self._find_term_variations(content, term)
            if variations:
                result['warnings'].append(f"术语 '{term}' 可能有其他写法: {variations}")
        
        result['score'] = max(0, result['score'])
        return result
    
    def _find_term_variations(self, content: str, term: str) -> List[str]:
        """查找术语变体"""
        # 简化的变体检测
        variations = []
        # 实际实现需要更复杂的逻辑
        return variations
    
    def _check_references(self, content: str) -> Dict:
        """检查引用有效性"""
        result = {
            'score': 100,
            'weight': 15,
            'errors': [],
            'warnings': [],
            'details': {}
        }
        
        # 检查内部链接
        internal_links = re.findall(r'\[([^\]]+)\]\(([^)]+)\)', content)
        result['details']['internal_link_count'] = len(internal_links)
        
        # 检查外部链接
        external_links = re.findall(r'\[([^\]]+)\]\((https?://[^)]+)\)', content)
        result['details']['external_link_count'] = len(external_links)
        
        # 检查链接文本
        for text, url in internal_links:
            if not text.strip():
                result['warnings'].append(f"链接缺少描述文本: {url}")
                result['score'] -= 5
        
        # 检查图片引用
        images = re.findall(r'!\[([^\]]*)\]\(([^)]+)\)', content)
        result['details']['image_count'] = len(images)
        
        for alt, src in images:
            if not alt.strip():
                result['warnings'].append(f"图片缺少替代文本: {src}")
                result['score'] -= 5
        
        result['score'] = max(0, result['score'])
        return result
    
    def _check_format_compliance(self, content: str) -> Dict:
        """检查格式合规性"""
        result = {
            'score': 100,
            'weight': 10,
            'errors': [],
            'warnings': [],
            'details': {}
        }
        
        # 检查 Markdown lint 规则
        
        # 检查标题后是否有空行
        if re.search(r'^#{1,6}\s+.+\n[^\n]', content, re.MULTILINE):
            result['warnings'].append("标题后建议添加空行")
            result['score'] -= 5
        
        # 检查列表格式
        list_items = re.findall(r'^[\s]*[-*+]\s+', content, re.MULTILINE)
        result['details']['list_item_count'] = len(list_items)
        
        # 检查代码块语言标记
        code_blocks = re.findall(r'```(\w*)', content)
        unnamed_blocks = [cb for cb in code_blocks if not cb]
        if unnamed_blocks:
            result['warnings'].append(f"{len(unnamed_blocks)} 个代码块缺少语言标记")
            result['score'] -= 5 * min(len(unnamed_blocks), 3)
        
        # 检查表格格式
        tables = re.findall(r'\|.*\|.*\n\|[-:|\s]+\|', content)
        result['details']['table_count'] = len(tables)
        
        # 检查行尾空格
        trailing_spaces = re.findall(r' +\n', content)
        if trailing_spaces:
            result['warnings'].append(f"发现 {len(trailing_spaces)} 处行尾空格")
            result['score'] -= min(len(trailing_spaces), 10)
        
        result['score'] = max(0, result['score'])
        return result
    
    def _check_accessibility(self, content: str) -> Dict:
        """检查可访问性"""
        result = {
            'score': 100,
            'weight': 5,
            'errors': [],
            'warnings': [],
            'details': {}
        }
        
        # 检查图片是否有替代文本
        images_without_alt = re.findall(r'!\[\s*\]\(([^)]+)\)', content)
        if images_without_alt:
            result['errors'].append(f"{len(images_without_alt)} 张图片缺少替代文本")
            result['score'] -= 20
        
        # 检查链接文本是否描述性
        vague_links = re.findall(r'\[\s*(点击这里|这里|此链接|link|click here)\s*\]\(([^)]+)\)', 
                                 content, re.IGNORECASE)
        if vague_links:
            result['warnings'].append("建议使用描述性链接文本")
            result['score'] -= 10
        
        # 检查是否有长段落
        long_paragraphs = re.findall(r'[^\n]{500,}\n', content)
        if long_paragraphs:
            result['warnings'].append(f"发现 {len(long_paragraphs)} 个长段落，建议适当分段")
            result['score'] -= 5 * min(len(long_paragraphs), 3)
        
        result['score'] = max(0, result['score'])
        return result
    
    def _score_to_level(self, score: int) -> QualityLevel:
        """分数转等级"""
        if score >= 90:
            return QualityLevel.EXCELLENT
        elif score >= 80:
            return QualityLevel.GOOD
        elif score >= 70:
            return QualityLevel.ACCEPTABLE
        elif score >= 60:
            return QualityLevel.NEEDS_IMPROVEMENT
        else:
            return QualityLevel.POOR
    
    def _generate_suggestions(self, report: QualityReport, checks: Dict) -> List[str]:
        """生成改进建议"""
        suggestions = []
        
        # 基于检查结果的通用建议
        if report.overall_score < 60:
            suggestions.append("文档质量较差，建议进行全面修订")
        elif report.overall_score < 80:
            suggestions.append("文档质量良好，但有改进空间")
        
        # 根据具体检查项生成建议
        metadata_check = checks.get('metadata_completeness', {})
        if metadata_check.get('score', 100) < 80:
            suggestions.append("完善文档元数据，添加缺失的必需和推荐字段")
        
        structure_check = checks.get('content_structure', {})
        details = structure_check.get('details', {})
        if not details.get('has_definition'):
            suggestions.append("添加定义部分，明确核心概念的数学定义")
        if not details.get('has_example'):
            suggestions.append("添加具体例子，帮助读者理解抽象概念")
        if not details.get('has_proof') and report.filepath.startswith('docs/'):
            suggestions.append("考虑添加重要定理的证明")
        
        notation_check = checks.get('notation_consistency', {})
        if notation_check.get('score', 100) < 90:
            suggestions.append("检查并统一数学符号的使用")
        
        return suggestions
    
    def scan_directory(self, pattern: str = '**/*.md', exclude_dirs: List[str] = None):
        """扫描目录检查质量"""
        exclude_dirs = exclude_dirs or ['.git', 'node_modules', '__pycache__', '00-归档']
        
        self.reports = []
        md_files = list(self.root_dir.glob(pattern))
        
        for filepath in md_files:
            if any(excl in str(filepath) for excl in exclude_dirs):
                continue
            
            report = self.check_file(filepath)
            self.reports.append(report)
        
        return self.reports
    
    def generate_report(self, output_path: str = None, min_score: int = 0):
        """
        生成质量报告
        
        Args:
            output_path: 输出文件路径
            min_score: 最小分数阈值，只报告低于此分数的文档
        """
        filtered_reports = [r for r in self.reports if r.overall_score <= min_score or min_score == 0]
        
        summary = {
            'generated_at': datetime.now().isoformat(),
            'total_checked': len(self.reports),
            'average_score': sum(r.overall_score for r in self.reports) / max(len(self.reports), 1),
            'by_level': {},
            'low_quality_files': [],
            'reports': [r.to_dict() for r in filtered_reports]
        }
        
        # 按等级统计
        for level in QualityLevel:
            count = len([r for r in self.reports if r.level == level])
            summary['by_level'][level.value] = count
        
        # 低质量文件
        summary['low_quality_files'] = [
            {'filepath': r.filepath, 'score': r.overall_score, 'level': r.level.value}
            for r in self.reports if r.overall_score < 70
        ]
        
        if output_path:
            with open(output_path, 'w', encoding='utf-8') as f:
                json.dump(summary, f, ensure_ascii=False, indent=2)
            print(f"质量报告已保存到: {output_path}")
        
        return summary
    
    def print_summary(self):
        """打印质量摘要"""
        if not self.reports:
            print("没有质量报告")
            return
        
        print("\n" + "="*80)
        print("FormalMath 质量检查报告")
        print("="*80)
        
        avg_score = sum(r.overall_score for r in self.reports) / len(self.reports)
        print(f"检查文档数: {len(self.reports)}")
        print(f"平均质量分: {avg_score:.1f}")
        print()
        
        # 按等级统计
        print("【质量等级分布】")
        for level in QualityLevel:
            count = len([r for r in self.reports if r.level == level])
            percentage = count / len(self.reports) * 100
            bar = '█' * int(percentage / 2)
            print(f"  {level.value:12s}: {count:4d} ({percentage:5.1f}%) {bar}")
        print()
        
        # 低质量文档
        low_quality = [r for r in self.reports if r.overall_score < 60]
        if low_quality:
            print(f"【需要关注的文档 ({len(low_quality)} 个)】")
            for r in sorted(low_quality, key=lambda x: x.overall_score)[:10]:
                print(f"  - {r.filepath}: {r.overall_score}分 ({r.level.value})")
            print()
        
        # 常见错误
        all_errors = []
        for r in self.reports:
            all_errors.extend(r.errors)
        
        if all_errors:
            from collections import Counter
            error_counts = Counter(all_errors)
            print("【常见错误】")
            for error, count in error_counts.most_common(5):
                print(f"  - {error}: {count} 次")
        
        print("="*80)


def main():
    """主函数"""
    import argparse
    
    parser = argparse.ArgumentParser(description='FormalMath 质量控制系统')
    parser.add_argument('-d', '--directory', default='.', help='项目根目录')
    parser.add_argument('-p', '--pattern', default='**/*.md', help='文件匹配模式')
    parser.add_argument('-o', '--output', help='输出报告文件')
    parser.add_argument('--min-score', type=int, default=0, help='最小分数阈值')
    parser.add_argument('--file', help='检查单个文件')
    
    args = parser.parse_args()
    
    qc = QualityControl(args.directory)
    
    if args.file:
        # 检查单个文件
        report = qc.check_file(Path(args.directory) / args.file)
        print(f"\n文件: {report.filepath}")
        print(f"标题: {report.title}")
        print(f"质量分: {report.overall_score} ({report.level.value})")
        print("\n检查项:")
        for name, result in report.checks.items():
            print(f"  {name}: {result['score']}分")
        if report.suggestions:
            print("\n改进建议:")
            for s in report.suggestions:
                print(f"  - {s}")
        if report.errors:
            print("\n错误:")
            for e in report.errors:
                print(f"  - {e}")
    else:
        # 扫描目录
        print(f"正在扫描 {args.directory} ...")
        qc.scan_directory(args.pattern)
        qc.print_summary()
        
        if args.output:
            qc.generate_report(args.output, args.min_score)


if __name__ == '__main__':
    main()
