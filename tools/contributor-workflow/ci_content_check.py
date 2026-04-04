#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
CI 内容质量检查脚本

用于 GitHub Actions 中自动化检查文档质量
"""

import argparse
import json
import re
import sys
from pathlib import Path
from typing import List, Dict, Optional
from dataclasses import dataclass, asdict
from datetime import datetime


@dataclass
class Issue:
    """检查发现问题"""
    file: str
    line: int
    severity: str  # error, warning
    code: str
    message: str


class CIContentChecker:
    """CI 内容检查器"""
    
    def __init__(self):
        self.issues: List[Issue] = []
        self.stats = {
            'files_checked': 0,
            'files_with_errors': 0,
            'errors': 0,
            'warnings': 0
        }
    
    def check_all(self, paths: List[str]) -> bool:
        """检查所有指定路径的文件"""
        for path_str in paths:
            path = Path(path_str)
            if path.is_file() and path.suffix == '.md':
                self._check_file(path)
            elif path.is_dir():
                for md_file in path.rglob('*.md'):
                    if 'node_modules' not in str(md_file):
                        self._check_file(md_file)
        
        return self.stats['errors'] == 0
    
    def _check_file(self, filepath: Path) -> None:
        """检查单个文件"""
        self.stats['files_checked'] += 1
        
        try:
            content = filepath.read_text(encoding='utf-8')
        except Exception as e:
            self._add_issue(filepath, 0, 'error', 'READ_ERROR', f'无法读取文件: {e}')
            return
        
        file_has_error = False
        
        # 检查 YAML Frontmatter
        issues = self._check_frontmatter(content, filepath)
        for issue in issues:
            self._add_issue(filepath, issue['line'], issue['severity'], 
                          issue['code'], issue['message'])
            if issue['severity'] == 'error':
                file_has_error = True
        
        # 检查内容质量
        issues = self._check_content_quality(content, filepath)
        for issue in issues:
            self._add_issue(filepath, issue['line'], issue['severity'],
                          issue['code'], issue['message'])
            if issue['severity'] == 'error':
                file_has_error = True
        
        if file_has_error:
            self.stats['files_with_errors'] += 1
    
    def _check_frontmatter(self, content: str, filepath: Path) -> List[Dict]:
        """检查 frontmatter"""
        issues = []
        
        # 检查 frontmatter 是否存在
        if not content.startswith('---'):
            issues.append({
                'line': 1,
                'severity': 'error',
                'code': 'MISSING_FRONTMATTER',
                'message': '缺少 YAML Frontmatter'
            })
            return issues
        
        # 提取 frontmatter
        match = re.match(r'^---\s*\n(.*?)\n---', content, re.DOTALL)
        if not match:
            issues.append({
                'line': 1,
                'severity': 'error',
                'code': 'INVALID_FRONTMATTER',
                'message': 'YAML Frontmatter 格式错误'
            })
            return issues
        
        try:
            import yaml
            frontmatter = yaml.safe_load(match.group(1))
            if frontmatter is None:
                frontmatter = {}
        except ImportError:
            # 如果没有 yaml 库，使用简单解析
            frontmatter = self._simple_yaml_parse(match.group(1))
        except Exception as e:
            issues.append({
                'line': 1,
                'severity': 'error',
                'code': 'YAML_ERROR',
                'message': f'YAML 解析错误: {e}'
            })
            return issues
        
        # 检查必需字段
        if 'msc_primary' not in frontmatter:
            issues.append({
                'line': 1,
                'severity': 'error',
                'code': 'MISSING_MSC',
                'message': '缺少必需字段: msc_primary'
            })
        else:
            msc = frontmatter.get('msc_primary', '')
            if not self._validate_msc(msc):
                issues.append({
                    'line': 1,
                    'severity': 'error',
                    'code': 'INVALID_MSC',
                    'message': f'无效的 MSC 编码: {msc}'
                })
        
        return issues
    
    def _simple_yaml_parse(self, content: str) -> Dict:
        """简单的 YAML 解析"""
        result = {}
        for line in content.split('\n'):
            if ':' in line and not line.strip().startswith('#'):
                key, value = line.split(':', 1)
                key = key.strip()
                value = value.strip().strip('"\'')
                if value:
                    result[key] = value
        return result
    
    def _validate_msc(self, msc: str) -> bool:
        """验证 MSC 编码格式"""
        import re
        patterns = [
            r'^\d{2}-XX$',
            r'^\d{2}[A-Z]xx$',
            r'^\d{2}[A-Z]\d{2}$',
        ]
        return any(re.match(pattern, str(msc)) for pattern in patterns)
    
    def _check_content_quality(self, content: str, filepath: Path) -> List[Dict]:
        """检查内容质量"""
        issues = []
        lines = content.split('\n')
        
        # 检查是否有标题
        has_title = False
        for i, line in enumerate(lines):
            if line.startswith('# '):
                has_title = True
                break
        
        if not has_title:
            issues.append({
                'line': 1,
                'severity': 'error',
                'code': 'MISSING_TITLE',
                'message': '文档缺少一级标题'
            })
        
        # 检查链接
        for i, line in enumerate(lines, 1):
            links = re.findall(r'\[([^\]]+)\]\(([^)]+)\)', line)
            for text, link in links:
                if link.startswith('#'):
                    # 锚点链接，检查是否存在
                    anchor = link[1:]
                    if not self._check_anchor(content, anchor):
                        issues.append({
                            'line': i,
                            'severity': 'warning',
                            'code': 'BROKEN_ANCHOR',
                            'message': f'锚点链接可能失效: {anchor}'
                        })
        
        return issues
    
    def _check_anchor(self, content: str, anchor: str) -> bool:
        """检查锚点是否存在"""
        # 将锚点转换为可能的标题形式
        anchor = anchor.lower().replace('-', '')
        
        # 查找所有标题
        for line in content.split('\n'):
            if line.startswith('#'):
                # 提取标题文本
                title = re.sub(r'^#+\s*', '', line).lower()
                title = re.sub(r'[^\w]', '', title)
                if title == anchor or anchor in title:
                    return True
        
        return False
    
    def _add_issue(self, filepath: Path, line: int, severity: str, 
                   code: str, message: str) -> None:
        """添加问题"""
        self.issues.append(Issue(
            file=str(filepath),
            line=line,
            severity=severity,
            code=code,
            message=message
        ))
        
        if severity == 'error':
            self.stats['errors'] += 1
        else:
            self.stats['warnings'] += 1
    
    def print_report(self, format: str = 'text') -> None:
        """打印检查报告"""
        if format == 'github':
            self._print_github_format()
        elif format == 'json':
            self._print_json_format()
        else:
            self._print_text_format()
    
    def _print_text_format(self) -> None:
        """文本格式输出"""
        print("=" * 70)
        print("FormalMath CI 内容质量检查报告")
        print("=" * 70)
        print()
        
        if self.issues:
            errors = [i for i in self.issues if i.severity == 'error']
            warnings = [i for i in self.issues if i.severity == 'warning']
            
            if errors:
                print("❌ 错误:")
                for issue in errors:
                    print(f"  {issue.file}:{issue.line}: [{issue.code}] {issue.message}")
                print()
            
            if warnings:
                print("⚠️  警告:")
                for issue in warnings:
                    print(f"  {issue.file}:{issue.line}: [{issue.code}] {issue.message}")
                print()
        else:
            print("✅ 所有检查通过！")
            print()
        
        print("=" * 70)
        print(f"统计: 检查 {self.stats['files_checked']} 个文件, "
              f"发现 {self.stats['errors']} 个错误, {self.stats['warnings']} 个警告")
        print("=" * 70)
    
    def _print_github_format(self) -> None:
        """GitHub Actions 格式输出"""
        for issue in self.issues:
            level = 'error' if issue.severity == 'error' else 'warning'
            print(f"::{level} file={issue.file},line={issue.line}::{issue.code}: {issue.message}")
    
    def _print_json_format(self) -> None:
        """JSON 格式输出"""
        report = {
            'timestamp': datetime.now().isoformat(),
            'stats': self.stats,
            'issues': [asdict(issue) for issue in self.issues]
        }
        print(json.dumps(report, indent=2, ensure_ascii=False))


def main():
    parser = argparse.ArgumentParser(description='CI 内容质量检查')
    parser.add_argument('--paths', nargs='+', required=True, help='要检查的路径')
    parser.add_argument('--fail-on-error', action='store_true', help='发现错误时返回非零退出码')
    parser.add_argument('--format', choices=['text', 'github', 'json'], 
                       default='text', help='输出格式')
    
    args = parser.parse_args()
    
    checker = CIContentChecker()
    success = checker.check_all(args.paths)
    checker.print_report(args.format)
    
    if args.fail_on_error and not success:
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
