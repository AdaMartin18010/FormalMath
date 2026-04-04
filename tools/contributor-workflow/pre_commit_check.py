#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath 预提交检查脚本

在提交前运行此脚本检查文档质量

用法:
    python pre_commit_check.py [options] [files...]

示例:
    # 检查所有修改的文件
    python pre_commit_check.py

    # 检查特定文件
    python pre_commit_check.py docs/example.md

    # 运行所有检查
    python pre_commit_check.py --all
"""

import argparse
import re
import sys
import subprocess
from pathlib import Path
from typing import List, Dict, Tuple
from dataclasses import dataclass, field


@dataclass
class CheckResult:
    """检查结果"""
    passed: bool
    message: str
    file: str = ""
    line: int = 0
    severity: str = "error"  # error, warning, info


class PreCommitChecker:
    """预提交检查器"""
    
    VALID_MSC_PATTERNS = [
        r'^\d{2}-XX$',  # 主分类
        r'^\d{2}[A-Z]xx$',  # 次分类一级
        r'^\d{2}[A-Z]\d{2}$',  # 次分类二级
    ]
    
    VALID_LEVELS = ['L0', 'L1', 'L2', 'L3', 'L4']
    
    def __init__(self, project_root: str = "."):
        self.project_root = Path(project_root)
        self.results: List[CheckResult] = []
        self.errors = 0
        self.warnings = 0
    
    def check_file(self, filepath: Path) -> List[CheckResult]:
        """检查单个文件"""
        results = []
        
        if not filepath.exists():
            results.append(CheckResult(
                passed=False,
                message=f"文件不存在: {filepath}",
                file=str(filepath),
                severity="error"
            ))
            return results
        
        content = filepath.read_text(encoding='utf-8')
        
        # 运行所有检查
        results.extend(self._check_yaml_frontmatter(content, filepath))
        results.extend(self._check_markdown_format(content, filepath))
        results.extend(self._check_math_formulas(content, filepath))
        results.extend(self._check_links(content, filepath))
        
        return results
    
    def _check_yaml_frontmatter(self, content: str, filepath: Path) -> List[CheckResult]:
        """检查 YAML Frontmatter"""
        results = []
        
        # 检查是否存在 frontmatter
        if not content.startswith('---'):
            results.append(CheckResult(
                passed=False,
                message="缺少 YAML Frontmatter",
                file=str(filepath),
                severity="error"
            ))
            return results
        
        # 提取 frontmatter
        match = re.match(r'^---\s*\n(.*?)\n---', content, re.DOTALL)
        if not match:
            results.append(CheckResult(
                passed=False,
                message="YAML Frontmatter 格式错误",
                file=str(filepath),
                severity="error"
            ))
            return results
        
        frontmatter = match.group(1)
        
        # 检查必需的字段
        if 'msc_primary:' not in frontmatter:
            results.append(CheckResult(
                passed=False,
                message="缺少必需字段: msc_primary",
                file=str(filepath),
                severity="error"
            ))
        else:
            # 验证 MSC 格式
            msc_match = re.search(r'msc_primary:\s*["\']?([^"\'\n]+)["\']?', frontmatter)
            if msc_match:
                msc = msc_match.group(1).strip()
                if not any(re.match(pattern, msc) for pattern in self.VALID_MSC_PATTERNS):
                    results.append(CheckResult(
                        passed=False,
                        message=f"无效的 MSC 编码格式: {msc}",
                        file=str(filepath),
                        severity="error"
                    ))
        
        # 检查 level 字段
        if 'level:' in frontmatter:
            level_match = re.search(r'level:\s*["\']?(L\d)["\']?', frontmatter)
            if level_match:
                level = level_match.group(1)
                if level not in self.VALID_LEVELS:
                    results.append(CheckResult(
                        passed=False,
                        message=f"无效的知识层次: {level}",
                        file=str(filepath),
                        severity="warning"
                    ))
        else:
            results.append(CheckResult(
                passed=False,
                message="建议添加 level 字段标注知识层次",
                file=str(filepath),
                severity="info"
            ))
        
        return results
    
    def _check_markdown_format(self, content: str, filepath: Path) -> List[CheckResult]:
        """检查 Markdown 格式"""
        results = []
        lines = content.split('\n')
        
        for i, line in enumerate(lines, 1):
            # 检查标题格式
            if line.startswith('#') and not line.startswith('# '):
                if len(line) > 1 and line[1] != ' ':
                    results.append(CheckResult(
                        passed=False,
                        message=f"标题格式错误: 缺少空格",
                        file=str(filepath),
                        line=i,
                        severity="warning"
                    ))
            
            # 检查列表格式
            if re.match(r'^\s*[-*]\S', line):
                results.append(CheckResult(
                    passed=False,
                    message=f"列表格式错误: 缺少空格",
                    file=str(filepath),
                    line=i,
                    severity="warning"
                ))
        
        # 检查文件末尾是否有空行
        if content and not content.endswith('\n'):
            results.append(CheckResult(
                passed=False,
                message="文件末尾缺少换行符",
                file=str(filepath),
                severity="warning"
            ))
        
        return results
    
    def _check_math_formulas(self, content: str, filepath: Path) -> List[CheckResult]:
        """检查数学公式"""
        results = []
        
        # 检查是否有未闭合的 LaTeX 公式
        inline_math = re.findall(r'[^\\]\$[^\$]*\$[^\$]', content)
        display_math = re.findall(r'\$\$[^\$]*\$\$', content, re.DOTALL)
        
        # 检查常见的数学符号错误
        problematic_patterns = [
            (r'\\le ', "使用 \\leq 替代 \\le 以提高可读性"),
            (r'\\ge ', "使用 \\geq 替代 \\ge 以提高可读性"),
            (r'\\neq', "使用 \\neq 替代 \\ne 以保持一致性"),
        ]
        
        for pattern, message in problematic_patterns:
            if re.search(pattern, content):
                results.append(CheckResult(
                    passed=False,
                    message=message,
                    file=str(filepath),
                    severity="info"
                ))
        
        return results
    
    def _check_links(self, content: str, filepath: Path) -> List[CheckResult]:
        """检查链接"""
        results = []
        
        # 提取所有内部链接
        internal_links = re.findall(r'\[([^\]]+)\]\(([^)]+)\)', content)
        
        for text, link in internal_links:
            # 检查是否是内部链接
            if not link.startswith(('http://', 'https://', '#', 'mailto:')):
                # 解析相对路径
                link_path = filepath.parent / link
                if not link_path.exists():
                    results.append(CheckResult(
                        passed=False,
                        message=f"内部链接失效: {link}",
                        file=str(filepath),
                        severity="error"
                    ))
        
        return results
    
    def check_lean_file(self, filepath: Path) -> List[CheckResult]:
        """检查 Lean4 文件"""
        results = []
        
        if not filepath.exists():
            results.append(CheckResult(
                passed=False,
                message=f"文件不存在: {filepath}",
                file=str(filepath),
                severity="error"
            ))
            return results
        
        content = filepath.read_text(encoding='utf-8')
        
        # 检查文件头注释
        if not content.startswith('/-'):
            results.append(CheckResult(
                passed=False,
                message="Lean 文件缺少文件头注释",
                file=str(filepath),
                severity="warning"
            ))
        
        # 检查是否包含 theorem/lemma/def
        if not re.search(r'\b(theorem|lemma|definition|def|structure|inductive)\b', content):
            results.append(CheckResult(
                passed=False,
                message="文件似乎没有包含任何定理、引理或定义",
                file=str(filepath),
                severity="warning"
            ))
        
        return results
    
    def run_checks(self, files: List[Path], check_lean: bool = True) -> bool:
        """运行所有检查"""
        print("=" * 60)
        print("FormalMath 预提交检查")
        print("=" * 60)
        print()
        
        for filepath in files:
            if filepath.suffix == '.md':
                print(f"🔍 检查: {filepath}")
                results = self.check_file(filepath)
                self.results.extend(results)
            elif check_lean and filepath.suffix == '.lean':
                print(f"🔍 检查 Lean: {filepath}")
                results = self.check_lean_file(filepath)
                self.results.extend(results)
        
        # 打印结果
        print()
        print("=" * 60)
        print("检查结果")
        print("=" * 60)
        print()
        
        errors = [r for r in self.results if r.severity == 'error']
        warnings = [r for r in self.results if r.severity == 'warning']
        infos = [r for r in self.results if r.severity == 'info']
        
        if errors:
            print(f"❌ 错误 ({len(errors)}):")
            for r in errors:
                line_info = f":{r.line}" if r.line else ""
                print(f"   {r.file}{line_info}: {r.message}")
            print()
        
        if warnings:
            print(f"⚠️  警告 ({len(warnings)}):")
            for r in warnings:
                line_info = f":{r.line}" if r.line else ""
                print(f"   {r.file}{line_info}: {r.message}")
            print()
        
        if infos:
            print(f"ℹ️  提示 ({len(infos)}):")
            for r in infos:
                line_info = f":{r.line}" if r.line else ""
                print(f"   {r.file}{line_info}: {r.message}")
            print()
        
        if not self.results:
            print("✅ 所有检查通过！")
            return True
        
        print("=" * 60)
        print(f"总计: {len(errors)} 错误, {len(warnings)} 警告, {len(infos)} 提示")
        print("=" * 60)
        
        return len(errors) == 0


def get_staged_files() -> List[Path]:
    """获取已暂存的文件"""
    try:
        result = subprocess.run(
            ['git', 'diff', '--cached', '--name-only', '--diff-filter=ACM'],
            capture_output=True,
            text=True,
            check=True
        )
        files = [Path(f) for f in result.stdout.strip().split('\n') if f]
        return [f for f in files if f.suffix in ['.md', '.lean']]
    except subprocess.CalledProcessError:
        return []


def main():
    parser = argparse.ArgumentParser(
        description='FormalMath 预提交检查',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例用法:
  # 检查所有暂存文件
  python pre_commit_check.py

  # 检查特定文件
  python pre_commit_check.py docs/example.md

  # 仅检查 Markdown
  python pre_commit_check.py --markdown-only

  # 仅检查 Lean
  python pre_commit_check.py --lean-only
        """
    )
    
    parser.add_argument('files', nargs='*', help='要检查的文件')
    parser.add_argument('--markdown-only', action='store_true', help='仅检查 Markdown')
    parser.add_argument('--lean-only', action='store_true', help='仅检查 Lean')
    parser.add_argument('--all', action='store_true', help='检查所有文件（不只是暂存）')
    parser.add_argument('--fix', action='store_true', help='尝试自动修复问题')
    
    args = parser.parse_args()
    
    checker = PreCommitChecker()
    
    if args.files:
        files = [Path(f) for f in args.files]
    elif args.all:
        # 检查所有 .md 和 .lean 文件
        files = list(Path('.').rglob('*.md')) + list(Path('.').rglob('*.lean'))
        # 排除 node_modules 等
        files = [f for f in files if 'node_modules' not in str(f)]
    else:
        files = get_staged_files()
    
    if not files:
        print("没有需要检查的文件")
        return 0
    
    check_lean = not args.markdown_only
    check_markdown = not args.lean_only
    
    if args.markdown_only:
        files = [f for f in files if f.suffix == '.md']
    elif args.lean_only:
        files = [f for f in files if f.suffix == '.lean']
    
    success = checker.run_checks(files, check_lean=check_lean)
    
    return 0 if success else 1


if __name__ == '__main__':
    sys.exit(main())
