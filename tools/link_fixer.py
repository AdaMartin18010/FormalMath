#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath项目链接自动修复工具

功能:
- 自动修正简单的路径错误
- 建议替代链接
- 生成修复报告

用法:
    python link_fixer.py [--apply] [--quick]
    
选项:
    --apply        实际应用修复(默认只生成报告)
    --quick        仅处理高频问题(加速模式)

输出:
    - 控制台输出修复报告
    - output/link_fix_report.json - 详细修复报告
"""

import os
import re
import sys
import json
import argparse
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Tuple, Set, Optional
from dataclasses import dataclass, field, asdict
from urllib.parse import unquote
from difflib import SequenceMatcher


@dataclass
class FixSuggestion:
    """修复建议记录"""
    source_file: str
    original_target: str
    suggested_target: str
    fix_type: str
    confidence: float
    reason: str
    applied: bool = False


@dataclass
class FixStats:
    """修复统计信息"""
    total_issues: int = 0
    processed: int = 0
    fixed_issues: int = 0
    suggestions_made: int = 0
    manual_review_needed: int = 0
    file_path_fixes: int = 0
    anchor_fixes: int = 0
    removed_links: int = 0
    suggestions: List[FixSuggestion] = field(default_factory=list)


class LinkFixer:
    """Markdown链接修复器"""
    
    # 标题锚点模式
    HEADER_PATTERN = re.compile(r'^#{1,6}\s+(.+?)(?:\s+\{#[\w-]+\})?$', re.MULTILINE)
    
    def __init__(self, root_dir: str, dry_run: bool = True, quick_mode: bool = False):
        self.root_dir = Path(root_dir).resolve()
        self.dry_run = dry_run
        self.quick_mode = quick_mode
        self.stats = FixStats()
        self.all_md_files: Dict[str, Path] = {}
        self.file_anchors: Dict[str, Set[str]] = {}  # 使用字符串路径作为key
        self.modified_files: Set[Path] = set()
        
        # 高频修复映射
        self.quick_fixes = {
            # 损坏的链接 'd' -> 删除
            'd': ('', 'remove', 0.99, "损坏的链接'd'，建议删除"),
            
            # 术语词典路径修复
            'docs/FormalMath术语词典-基础数学.md': ('00-标准术语表-8语言.md', 'file_path', 0.95, "映射到标准术语表"),
            'docs/FormalMath术语词典-代数结构.md': ('00-标准术语表-8语言.md', 'file_path', 0.95, "映射到标准术语表"),
            'docs/FormalMath术语词典-分析学.md': ('00-标准术语表-8语言.md', 'file_path', 0.95, "映射到标准术语表"),
            'docs/FormalMath术语词典-几何学.md': ('00-标准术语表-8语言.md', 'file_path', 0.95, "映射到标准术语表"),
            'docs/FormalMath术语词典-拓扑学.md': ('00-标准术语表-8语言.md', 'file_path', 0.95, "映射到标准术语表"),
            'docs/FormalMath术语词典-数论.md': ('00-标准术语表-8语言.md', 'file_path', 0.95, "映射到标准术语表"),
            'docs/FormalMath术语词典-概率统计.md': ('00-标准术语表-8语言.md', 'file_path', 0.95, "映射到标准术语表"),
            'docs/FormalMath术语词典-离散数学.md': ('00-标准术语表-8语言.md', 'file_path', 0.95, "映射到标准术语表"),
            'docs/FormalMath术语词典-计算数学.md': ('00-标准术语表-8语言.md', 'file_path', 0.95, "映射到标准术语表"),
            'docs/FormalMath术语词典-应用数学.md': ('00-标准术语表-8语言.md', 'file_path', 0.95, "映射到标准术语表"),
            'docs/FormalMath术语词典-数理逻辑.md': ('00-标准术语表-8语言.md', 'file_path', 0.95, "映射到标准术语表"),
        }
        
        # 常见锚点修复映射
        self.anchor_fixes = {
            '#-目录': '#目录',
            '#-目录--table-of-contents': '#目录',
            '#目录--table-of-contents': '#目录',
            '#-目录-1': '#目录',
            '#-相关文档': '#相关文档',
            '#-文档信息': '#文档信息',
            '#-概述': '#概述',
            '#-一概述': '#一概述',
            '#-概述--overview': '#概述',
            '#术语对照表--terminology-table': '#术语对照表',
        }
        
        # 扫描文件索引
        self._build_file_index()
        
    def _build_file_index(self):
        """构建文件索引"""
        print("构建文件索引...")
        count = 0
        for pattern in ['**/*.md']:
            for f in self.root_dir.glob(pattern):
                if 'node_modules' in str(f) or '.git' in str(f):
                    continue
                self.all_md_files[f.name.lower()] = f
                count += 1
        print(f"  已索引 {count} 个Markdown文件")
                
    def get_file_anchors(self, file_path: Path) -> Set[str]:
        """获取文件的锚点，带缓存"""
        key = str(file_path)
        if key in self.file_anchors:
            return self.file_anchors[key]
        
        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
            
            anchors = set()
            for match in self.HEADER_PATTERN.finditer(content):
                header = match.group(1).strip()
                header = re.sub(r'\s*\{#[\w-]+\}\s*$', '', header)
                anchor = self._generate_anchor_id(header)
                if anchor:
                    anchors.add(anchor.lower())
            
            self.file_anchors[key] = anchors
            return anchors
        except Exception:
            self.file_anchors[key] = set()
            return set()
    
    def _generate_anchor_id(self, text: str) -> str:
        """生成GitHub风格锚点ID"""
        text = text.lower()
        text = re.sub(r'[_*~`]', '', text)
        text = re.sub(r'[^\w\s-]', '', text)
        text = re.sub(r'[\s]+', '-', text)
        return text.strip('-')
    
    def find_file_by_name(self, filename: str) -> Optional[Path]:
        """通过文件名查找文件"""
        name_lower = filename.lower()
        if name_lower in self.all_md_files:
            return self.all_md_files[name_lower]
        if not name_lower.endswith('.md'):
            return self.all_md_files.get(name_lower + '.md')
        return None
    
    def find_similar_file(self, target: str) -> Optional[Tuple[Path, float]]:
        """查找相似文件"""
        target_lower = target.lower().replace('.md', '')
        best_match = None
        best_score = 0.0
        
        for name, path in self.all_md_files.items():
            name_clean = name.lower().replace('.md', '')
            score = SequenceMatcher(None, target_lower, name_clean).ratio()
            
            if target_lower in name_clean:
                score += 0.3
            if name_clean in target_lower:
                score += 0.2
            
            if score > best_score:
                best_score = score
                best_match = (path, score)
        
        if best_match and best_match[1] > 0.6:
            return best_match
        return None
    
    def suggest_fix(self, source_file: str, link_target: str, issue_type: str) -> Optional[FixSuggestion]:
        """生成修复建议"""
        # 跳过外部链接
        if link_target.startswith(('http://', 'https://', 'ftp://', 'mailto:')):
            return None
        
        # 解析文件和锚点
        if '#' in link_target:
            file_part, anchor = link_target.split('#', 1)
        else:
            file_part, anchor = link_target, ''
        
        # 快速修复模式
        if self.quick_mode:
            # 检查快速修复映射
            if issue_type == 'broken_file' and link_target in self.quick_fixes:
                target, fix_type, conf, reason = self.quick_fixes[link_target]
                return FixSuggestion(source_file, link_target, target, fix_type, conf, reason)
            
            # 锚点快速修复
            if issue_type == 'broken_anchor' and link_target in self.anchor_fixes:
                target = self.anchor_fixes[link_target]
                return FixSuggestion(source_file, link_target, target, 'anchor', 0.9, "常见锚点映射")
            
            # 快速模式下跳过高复杂度修复
            return FixSuggestion(source_file, link_target, '', 'manual', 0.0, "需手动处理")
        
        # 完整修复逻辑
        if issue_type == 'broken_file':
            # 检查快速修复映射
            if link_target in self.quick_fixes:
                target, fix_type, conf, reason = self.quick_fixes[link_target]
                return FixSuggestion(source_file, link_target, target, fix_type, conf, reason)
            
            # 尝试查找文件
            if file_part:
                filename = Path(file_part).name
                found = self.find_file_by_name(filename)
                if found:
                    try:
                        source = self.root_dir / source_file
                        rel = found.relative_to(source.parent)
                        target = str(rel).replace('\\', '/')
                        if anchor:
                            target = f"{target}#{anchor}"
                        return FixSuggestion(source_file, link_target, target, 'file_path', 0.85, f"找到同名文件: {filename}")
                    except ValueError:
                        pass
                
                # 查找相似文件
                similar = self.find_similar_file(filename)
                if similar:
                    try:
                        source = self.root_dir / source_file
                        rel = similar[0].relative_to(source.parent)
                        target = str(rel).replace('\\', '/')
                        if anchor:
                            target = f"{target}#{anchor}"
                        return FixSuggestion(source_file, link_target, target, 'file_path', similar[1] * 0.8, 
                                           f"相似文件匹配 (相似度: {similar[1]:.2f})")
                    except ValueError:
                        pass
            
            return FixSuggestion(source_file, link_target, '', 'manual', 0.0, "无法找到匹配文件")
        
        elif issue_type == 'broken_anchor':
            # 检查锚点映射
            if link_target in self.anchor_fixes:
                target = self.anchor_fixes[link_target]
                return FixSuggestion(source_file, link_target, target, 'anchor', 0.9, "常见锚点映射")
            
            # 验证锚点是否存在
            if file_part:
                source = self.root_dir / source_file
                target_file = (source.parent / file_part).resolve()
            else:
                target_file = self.root_dir / source_file
            
            if target_file.exists():
                anchors = self.get_file_anchors(target_file)
                anchor_clean = anchor.lower()
                
                # 大小写修正
                for existing in anchors:
                    if existing == anchor_clean:
                        if existing != anchor.lower():
                            return FixSuggestion(source_file, link_target, f"#{existing}", 'anchor', 0.95, "大小写修正")
                        break
                
                # 查找相似锚点
                best_match = None
                best_score = 0.0
                for existing in anchors:
                    score = SequenceMatcher(None, anchor_clean, existing).ratio()
                    if anchor_clean in existing:
                        score += 0.3
                    if score > best_score:
                        best_score = score
                        best_match = existing
                
                if best_match and best_score > 0.7:
                    return FixSuggestion(source_file, link_target, f"#{best_match}", 'anchor', best_score,
                                       f"相似锚点匹配 (相似度: {best_score:.2f})")
            
            return FixSuggestion(source_file, link_target, '', 'manual', 0.0, "无法找到匹配锚点")
        
        return None
    
    def apply_fix_to_file(self, source_file: Path, original: str, suggested: str, fix_type: str) -> bool:
        """应用修复到文件"""
        try:
            with open(source_file, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
            
            original_content = content
            
            # 转义正则特殊字符
            escaped = re.escape(original)
            
            if fix_type == 'remove':
                # 移除链接，保留文本
                pattern = rf'\[([^\]]*)\]\({escaped}\)'
                content = re.sub(pattern, r'\1', content)
            else:
                # 替换链接目标
                pattern = rf'(\[([^\]]*)\]\(){escaped}(\))'
                content = re.sub(pattern, rf'\1{suggested}\3', content)
            
            if content != original_content:
                with open(source_file, 'w', encoding='utf-8') as f:
                    f.write(content)
                self.modified_files.add(source_file)
                return True
                
        except Exception as e:
            print(f"  错误: {source_file}: {e}")
        
        return False
    
    def process_issues(self, issues_file: str):
        """处理链接问题"""
        with open(issues_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
        
        issues = data.get('issues', [])
        self.stats.total_issues = len(issues)
        
        print(f"处理 {len(issues)} 个问题...")
        
        # 按文件分组，减少文件IO
        by_file: Dict[str, List[Dict]] = {}
        for issue in issues:
            source = issue['source_file']
            by_file.setdefault(source, []).append(issue)
        
        print(f"  分布在 {len(by_file)} 个文件中")
        
        processed_files = 0
        for source_file, file_issues in by_file.items():
            processed_files += 1
            if processed_files % 500 == 0:
                print(f"  进度: {processed_files}/{len(by_file)} 文件")
            
            source_path = self.root_dir / source_file
            if not source_path.exists():
                continue
            
            for issue in file_issues:
                self.stats.processed += 1
                
                suggestion = self.suggest_fix(
                    source_file,
                    issue['link_target'],
                    issue['issue_type']
                )
                
                if suggestion:
                    self.stats.suggestions.append(suggestion)
                    
                    if suggestion.fix_type == 'file_path':
                        self.stats.file_path_fixes += 1
                    elif suggestion.fix_type == 'anchor':
                        self.stats.anchor_fixes += 1
                    elif suggestion.fix_type == 'remove':
                        self.stats.removed_links += 1
                    elif suggestion.fix_type == 'manual':
                        self.stats.manual_review_needed += 1
                    
                    # 应用修复
                    if not self.dry_run and suggestion.fix_type in ['file_path', 'anchor', 'remove']:
                        if suggestion.confidence >= 0.8:
                            if self.apply_fix_to_file(source_path, suggestion.original_target, 
                                                     suggestion.suggested_target, suggestion.fix_type):
                                suggestion.applied = True
                                self.stats.fixed_issues += 1
        
        self.stats.suggestions_made = len(self.stats.suggestions)
        print(f"完成! 生成 {self.stats.suggestions_made} 个建议, 应用 {self.stats.fixed_issues} 个修复")
    
    def generate_report(self, output_file: str) -> str:
        """生成修复报告"""
        lines = []
        lines.append("# 链接修复报告")
        lines.append("")
        lines.append(f"**生成时间:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        lines.append(f"**项目根目录:** {self.root_dir}")
        lines.append(f"**运行模式:** {'干运行(预览)' if self.dry_run else '实际修复'}")
        lines.append(f"**处理模式:** {'快速模式' if self.quick_mode else '完整模式'}")
        lines.append("")
        
        # 统计摘要
        lines.append("## 统计摘要")
        lines.append("")
        lines.append(f"| 指标 | 数量 |")
        lines.append(f"|------|------|")
        lines.append(f"| 总问题数 | {self.stats.total_issues:,} |")
        lines.append(f"| 已处理 | {self.stats.processed:,} |")
        lines.append(f"| 生成建议数 | {self.stats.suggestions_made:,} |")
        lines.append(f"| 文件路径修复 | {self.stats.file_path_fixes:,} |")
        lines.append(f"| 锚点修复 | {self.stats.anchor_fixes:,} |")
        lines.append(f"| 建议删除 | {self.stats.removed_links:,} |")
        lines.append(f"| 需手动处理 | {self.stats.manual_review_needed:,} |")
        if not self.dry_run:
            lines.append(f"| 实际修复数 | {self.stats.fixed_issues:,} |")
            lines.append(f"| 修改文件数 | {len(self.modified_files):,} |")
        lines.append("")
        
        # 高置信度修复
        high_conf = [s for s in self.stats.suggestions if s.confidence >= 0.8 and s.fix_type != 'manual']
        if high_conf:
            lines.append(f"## 高置信度自动修复 ({len(high_conf)} 个)")
            lines.append("")
            lines.append("以下修复具有高置信度，已自动应用(或建议应用):")
            lines.append("")
            
            # 按类型分组
            by_type: Dict[str, List[FixSuggestion]] = {}
            for s in high_conf:
                by_type.setdefault(s.fix_type, []).append(s)
            
            for fix_type, suggestions in by_type.items():
                lines.append(f"### {fix_type} ({len(suggestions)} 个)")
                lines.append("")
                for s in suggestions[:20]:
                    status = "✅" if s.applied else "⏳"
                    lines.append(f"- {status} `{s.source_file}`")
                    lines.append(f"  - 原始: `{s.original_target}`")
                    lines.append(f"  - 修复: `{s.suggested_target}`")
                    lines.append(f"  - 置信度: {s.confidence:.0%}")
                if len(suggestions) > 20:
                    lines.append(f"- ... 还有 {len(suggestions) - 20} 个")
                lines.append("")
        
        # 需手动处理的问题
        manual = [s for s in self.stats.suggestions if s.fix_type == 'manual']
        if manual:
            lines.append(f"## 需手动处理的问题 ({len(manual)} 个)")
            lines.append("")
            
            # 按文件分组
            by_file: Dict[str, List[FixSuggestion]] = {}
            for s in manual:
                by_file.setdefault(s.source_file, []).append(s)
            
            lines.append(f"涉及 {len(by_file)} 个文件:")
            lines.append("")
            
            for file, suggestions in list(by_file.items())[:30]:
                lines.append(f"### {file}")
                for s in suggestions[:5]:
                    lines.append(f"- `{s.original_target}` - {s.reason}")
                if len(suggestions) > 5:
                    lines.append(f"- ... 还有 {len(suggestions) - 5} 个问题")
                lines.append("")
            
            if len(by_file) > 30:
                lines.append(f"**... 还有 {len(by_file) - 30} 个文件**")
            lines.append("")
        
        # 修复详情表
        lines.append("## 修复详情")
        lines.append("")
        lines.append("| 源文件 | 原始链接 | 修复建议 | 类型 | 置信度 | 状态 |")
        lines.append("|--------|----------|----------|------|--------|------|")
        
        for s in self.stats.suggestions[:200]:
            status = "✅ 已应用" if s.applied else ("⏳ 待应用" if s.fix_type != 'manual' else "❌ 需手动")
            orig = s.original_target[:40] + "..." if len(s.original_target) > 40 else s.original_target
            sugg = s.suggested_target[:40] + "..." if len(s.suggested_target) > 40 else s.suggested_target
            lines.append(f"| {s.source_file[:30]} | `{orig}` | `{sugg}` | {s.fix_type} | {s.confidence:.0%} | {status} |")
        
        if len(self.stats.suggestions) > 200:
            lines.append(f"| ... | ... | ... | ... | ... | **还有 {len(self.stats.suggestions) - 200} 条** |")
        
        lines.append("")
        lines.append("---")
        lines.append(f"*报告生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}*")
        
        report = '\n'.join(lines)
        
        # 写入文件
        output_path = Path(output_file)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(report)
        
        return report
    
    def generate_json_report(self, output_file: str):
        """生成JSON报告"""
        report_data = {
            'fix_time': datetime.now().isoformat(),
            'root_directory': str(self.root_dir),
            'dry_run': self.dry_run,
            'quick_mode': self.quick_mode,
            'statistics': {
                'total_issues': self.stats.total_issues,
                'processed': self.stats.processed,
                'suggestions_made': self.stats.suggestions_made,
                'file_path_fixes': self.stats.file_path_fixes,
                'anchor_fixes': self.stats.anchor_fixes,
                'removed_links': self.stats.removed_links,
                'manual_review_needed': self.stats.manual_review_needed,
                'fixed_issues': self.stats.fixed_issues,
                'modified_files': len(self.modified_files)
            },
            'suggestions': [
                {
                    'source_file': s.source_file,
                    'original_target': s.original_target,
                    'suggested_target': s.suggested_target,
                    'fix_type': s.fix_type,
                    'confidence': s.confidence,
                    'reason': s.reason,
                    'applied': s.applied
                }
                for s in self.stats.suggestions
            ]
        }
        
        output_path = Path(output_file)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(report_data, ensure_ascii=False, indent=2, fp=output_path.open('w', encoding='utf-8'))


def main():
    parser = argparse.ArgumentParser(description='FormalMath项目链接自动修复工具')
    parser.add_argument('--apply', action='store_true', help='实际应用修复')
    parser.add_argument('--quick', action='store_true', help='快速模式(仅处理高频问题)')
    parser.add_argument('--root', default='.', help='项目根目录')
    parser.add_argument('--issues', default='output/link_check_report.json', help='问题报告文件')
    args = parser.parse_args()
    
    root_dir = Path(args.root).resolve()
    issues_file = root_dir / args.issues
    
    if not issues_file.exists():
        print(f"错误: 报告文件不存在: {issues_file}")
        sys.exit(1)
    
    dry_run = not args.apply
    
    print("=" * 60)
    print("FormalMath项目链接自动修复工具")
    print("=" * 60)
    print(f"项目根目录: {root_dir}")
    print(f"模式: {'干运行(预览)' if dry_run else '实际修复'}")
    print(f"处理: {'快速模式' if args.quick else '完整模式'}")
    print("=" * 60)
    print()
    
    # 创建修复器
    fixer = LinkFixer(root_dir, dry_run=dry_run, quick_mode=args.quick)
    
    # 处理问题
    fixer.process_issues(str(issues_file))
    
    # 生成报告
    print("\n生成报告...")
    report_file = root_dir / 'output' / 'link_fix_report.md'
    fixer.generate_report(str(report_file))
    
    json_file = root_dir / 'output' / 'link_fix_report.json'
    with open(json_file, 'w', encoding='utf-8') as f:
        json.dump({
            'fix_time': datetime.now().isoformat(),
            'statistics': {
                'total_issues': fixer.stats.total_issues,
                'processed': fixer.stats.processed,
                'suggestions_made': fixer.stats.suggestions_made,
                'file_path_fixes': fixer.stats.file_path_fixes,
                'anchor_fixes': fixer.stats.anchor_fixes,
                'removed_links': fixer.stats.removed_links,
                'manual_review_needed': fixer.stats.manual_review_needed,
                'fixed_issues': fixer.stats.fixed_issues,
                'modified_files': len(fixer.modified_files)
            }
        }, f, ensure_ascii=False, indent=2)
    
    # 输出摘要
    print("\n" + "=" * 60)
    print("修复摘要")
    print("=" * 60)
    print(f"  总问题数:     {fixer.stats.total_issues:,}")
    print(f"  已处理:       {fixer.stats.processed:,}")
    print(f"  生成建议:     {fixer.stats.suggestions_made:,}")
    print(f"  文件路径修复: {fixer.stats.file_path_fixes:,}")
    print(f"  锚点修复:     {fixer.stats.anchor_fixes:,}")
    print(f"  建议删除:     {fixer.stats.removed_links:,}")
    print(f"  需手动处理:   {fixer.stats.manual_review_needed:,}")
    if not dry_run:
        print(f"  实际修复数:   {fixer.stats.fixed_issues:,}")
        print(f"  修改文件数:   {len(fixer.modified_files):,}")
    print("=" * 60)
    
    if dry_run:
        print("\n这是干运行模式，未实际修改文件。")
        print("使用 --apply 参数应用修复。")
    
    print(f"\n报告已保存:")
    print(f"  - {report_file}")
    print(f"  - {json_file}")


if __name__ == '__main__':
    main()
