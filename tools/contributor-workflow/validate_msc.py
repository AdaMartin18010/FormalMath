#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
MSC 编码验证脚本

验证文档的 MSC2020 编码是否正确
"""

import argparse
import re
import sys
from pathlib import Path
from typing import List, Set, Dict, Optional
from dataclasses import dataclass


# MSC2020 主分类列表
MSC_PRIMARY_CATEGORIES = {
    '00': 'General',
    '01': 'History and Biography',
    '03': 'Mathematical logic and foundations',
    '05': 'Combinatorics',
    '06': 'Order, lattices, ordered algebraic structures',
    '08': 'General algebraic systems',
    '11': 'Number theory',
    '12': 'Field theory and polynomials',
    '13': 'Commutative algebra',
    '14': 'Algebraic geometry',
    '15': 'Linear and multilinear algebra; matrix theory',
    '16': 'Associative rings and algebras',
    '17': 'Nonassociative rings and algebras',
    '18': 'Category theory; homological algebra',
    '19': 'K-theory',
    '20': 'Group theory and generalizations',
    '22': 'Topological groups, Lie groups',
    '26': 'Real functions',
    '28': 'Measure and integration',
    '30': 'Functions of a complex variable',
    '31': 'Potential theory',
    '32': 'Several complex variables and analytic spaces',
    '33': 'Special functions',
    '34': 'Ordinary differential equations',
    '35': 'Partial differential equations',
    '37': 'Dynamical systems and ergodic theory',
    '39': 'Difference and functional equations',
    '40': 'Sequences, series, summability',
    '41': 'Approximations and expansions',
    '42': 'Harmonic analysis on Euclidean spaces',
    '43': 'Abstract harmonic analysis',
    '44': 'Integral transforms, operational calculus',
    '45': 'Integral equations',
    '46': 'Functional analysis',
    '47': 'Operator theory',
    '49': 'Calculus of variations and optimal control',
    '51': 'Geometry',
    '52': 'Convex and discrete geometry',
    '53': 'Differential geometry',
    '54': 'General topology',
    '55': 'Algebraic topology',
    '57': 'Manifolds and cell complexes',
    '58': 'Global analysis, analysis on manifolds',
    '60': 'Probability theory and stochastic processes',
    '62': 'Statistics',
    '65': 'Numerical analysis',
    '68': 'Computer science',
    '70': 'Mechanics of particles and systems',
    '74': 'Mechanics of deformable solids',
    '76': 'Fluid mechanics',
    '78': 'Optics, electromagnetic theory',
    '80': 'Classical thermodynamics, heat transfer',
    '81': 'Quantum theory',
    '82': 'Statistical mechanics, structure of matter',
    '83': 'Relativity and gravitational theory',
    '85': 'Astronomy and astrophysics',
    '86': 'Geophysics',
    '90': 'Operations research, mathematical programming',
    '91': 'Game theory, economics, social and behavioral sciences',
    '92': 'Biology and other natural sciences',
    '93': 'Systems theory; control',
    '94': 'Information and communication, circuits',
    '97': 'Mathematics education',
}


@dataclass
class MSCValidationResult:
    """MSC 验证结果"""
    file: str
    msc_primary: Optional[str]
    msc_secondary: List[str]
    is_valid: bool
    errors: List[str]
    warnings: List[str]


class MSCValidator:
    """MSC 编码验证器"""
    
    def __init__(self):
        self.results: List[MSCValidationResult] = []
        self.valid_categories = set(MSC_PRIMARY_CATEGORIES.keys())
    
    def validate_file(self, filepath: Path) -> MSCValidationResult:
        """验证单个文件"""
        errors = []
        warnings = []
        msc_primary = None
        msc_secondary = []
        
        if not filepath.exists():
            errors.append(f"文件不存在: {filepath}")
            return MSCValidationResult(
                file=str(filepath),
                msc_primary=None,
                msc_secondary=[],
                is_valid=False,
                errors=errors,
                warnings=warnings
            )
        
        content = filepath.read_text(encoding='utf-8')
        
        # 检查 frontmatter
        if not content.startswith('---'):
            errors.append("缺少 YAML Frontmatter")
            is_valid = False
        else:
            # 提取 frontmatter
            match = re.match(r'^---\s*\n(.*?)\n---', content, re.DOTALL)
            if not match:
                errors.append("YAML Frontmatter 格式错误")
                is_valid = False
            else:
                frontmatter = match.group(1)
                
                # 检查 msc_primary
                msc_match = re.search(r'msc_primary:\s*["\']?([^"\'\n]+)["\']?', frontmatter)
                if msc_match:
                    msc_primary = msc_match.group(1).strip()
                    
                    # 验证格式
                    if not self._validate_msc_format(msc_primary):
                        errors.append(f"无效的 MSC 格式: {msc_primary}")
                    elif not self._validate_msc_category(msc_primary):
                        errors.append(f"未知的 MSC 分类: {msc_primary}")
                else:
                    errors.append("缺少 msc_primary 字段")
                
                # 检查 msc_secondary
                secondary_matches = re.findall(r'msc_secondary:\s*\n((?:\s*-\s*[^\n]+\n?)+)', frontmatter)
                if secondary_matches:
                    for match_text in secondary_matches:
                        codes = re.findall(r'-\s*["\']?([^"\'\n]+)["\']?', match_text)
                        for code in codes:
                            code = code.strip()
                            msc_secondary.append(code)
                            if not self._validate_msc_format(code):
                                warnings.append(f"次分类格式可能无效: {code}")
        
        is_valid = len(errors) == 0
        
        result = MSCValidationResult(
            file=str(filepath),
            msc_primary=msc_primary,
            msc_secondary=msc_secondary,
            is_valid=is_valid,
            errors=errors,
            warnings=warnings
        )
        
        self.results.append(result)
        return result
    
    def _validate_msc_format(self, msc: str) -> bool:
        """验证 MSC 格式"""
        patterns = [
            r'^\d{2}-XX$',      # 主分类格式
            r'^\d{2}[A-Z]xx$',  # 次分类一级
            r'^\d{2}[A-Z]\d{2}$',  # 次分类二级
        ]
        return any(re.match(pattern, msc) for pattern in patterns)
    
    def _validate_msc_category(self, msc: str) -> bool:
        """验证 MSC 分类是否存在"""
        # 提取前两位的分类号
        category = msc[:2]
        return category in self.valid_categories
    
    def validate_directory(self, directory: Path, pattern: str = "**/*.md") -> None:
        """验证目录下所有文件"""
        for filepath in directory.rglob(pattern):
            if 'node_modules' not in str(filepath):
                self.validate_file(filepath)
    
    def get_statistics(self) -> Dict:
        """获取验证统计"""
        total = len(self.results)
        valid = sum(1 for r in self.results if r.is_valid)
        invalid = total - valid
        
        # MSC 覆盖统计
        with_msc = sum(1 for r in self.results if r.msc_primary is not None)
        
        # 分类统计
        category_counts: Dict[str, int] = {}
        for r in self.results:
            if r.msc_primary:
                cat = r.msc_primary[:2]
                category_counts[cat] = category_counts.get(cat, 0) + 1
        
        return {
            'total_files': total,
            'valid_files': valid,
            'invalid_files': invalid,
            'msc_coverage': with_msc / total if total > 0 else 0,
            'category_distribution': category_counts
        }
    
    def print_report(self, format: str = 'text') -> None:
        """打印验证报告"""
        if format == 'github':
            self._print_github_format()
        else:
            self._print_text_format()
    
    def _print_text_format(self) -> None:
        """文本格式输出"""
        print("=" * 70)
        print("MSC 编码验证报告")
        print("=" * 70)
        print()
        
        # 统计
        stats = self.get_statistics()
        print("统计:")
        print(f"  总文件数: {stats['total_files']}")
        print(f"  有效文件: {stats['valid_files']}")
        print(f"  无效文件: {stats['invalid_files']}")
        print(f"  MSC 覆盖率: {stats['msc_coverage']:.1%}")
        print()
        
        # 分类分布
        if stats['category_distribution']:
            print("分类分布:")
            for cat, count in sorted(stats['category_distribution'].items()):
                name = MSC_PRIMARY_CATEGORIES.get(cat, 'Unknown')
                print(f"  {cat}-XX ({name}): {count} 篇")
            print()
        
        # 错误详情
        invalid_results = [r for r in self.results if not r.is_valid]
        if invalid_results:
            print("错误详情:")
            for r in invalid_results[:20]:  # 只显示前20个
                print(f"\n  {r.file}:")
                for error in r.errors:
                    print(f"    ❌ {error}")
                for warning in r.warnings:
                    print(f"    ⚠️  {warning}")
            
            if len(invalid_results) > 20:
                print(f"\n  ... 还有 {len(invalid_results) - 20} 个文件")
        else:
            print("✅ 所有文件验证通过！")
        
        print()
        print("=" * 70)
    
    def _print_github_format(self) -> None:
        """GitHub Actions 格式输出"""
        for r in self.results:
            if not r.is_valid:
                for error in r.errors:
                    print(f"::error file={r.file}::{error}")
                for warning in r.warnings:
                    print(f"::warning file={r.file}::{warning}")


def main():
    parser = argparse.ArgumentParser(description='MSC 编码验证')
    parser.add_argument('--check-all', action='store_true', 
                       help='检查所有文档')
    parser.add_argument('--path', type=str, default='.',
                       help='要检查的路径')
    parser.add_argument('--pattern', type=str, default='**/*.md',
                       help='文件匹配模式')
    parser.add_argument('--report-format', choices=['text', 'github'],
                       default='text', help='报告格式')
    
    args = parser.parse_args()
    
    validator = MSCValidator()
    
    if args.check_all:
        path = Path(args.path)
        if path.is_dir():
            validator.validate_directory(path, args.pattern)
        else:
            print(f"路径不存在: {path}")
            return 1
    
    validator.print_report(args.report_format)
    
    # 返回退出码
    invalid_count = sum(1 for r in validator.results if not r.is_valid)
    return 0 if invalid_count == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
