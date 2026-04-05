#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath项目链接自动修复工具

功能:
- 自动修正简单的路径错误
- 建议替代链接
- 生成修复报告

用法:
    python link_fixer.py [--dry-run] [--fix-type TYPE]
    
选项:
    --dry-run      仅显示修复建议，不实际修改文件
    --fix-type     指定修复类型: file, anchor, all (默认: all)

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


@dataclass
class FixSuggestion:
    """修复建议记录"""
    source_file: str
    link_text: str
    original_target: str
    suggested_target: str
    fix_type: str  # 'file_path', 'anchor', 'remove', 'manual'
    confidence: float  # 0.0-1.0
    reason: str
    line_number: int = 0
    applied: bool = False


@dataclass
class FixStats:
    """修复统计信息"""
    total_issues: int = 0
    fixed_issues: int = 0
    suggestions_made: int = 0
    manual_review_needed: int = 0
    file_path_fixes: int = 0
    anchor_fixes: int = 0
    removed_links: int = 0
    suggestions: List[FixSuggestion] = field(default_factory=list)


class LinkFixer:
    """Markdown链接修复器"""
    
    # Markdown链接正则表达式模式
    LINK_PATTERN = re.compile(
        r'(!?)\[([^\]]*)\]\(([^)]+)\)',
        re.MULTILINE | re.DOTALL
    )
    
    # 标题锚点模式
    HEADER_PATTERN = re.compile(
        r'^#{1,6}\s+(.+?)(?:\s+\{#[\w-]+\})?$',
        re.MULTILINE
    )
    
    # 自定义锚点模式
    CUSTOM_ANCHOR_PATTERN = re.compile(
        r'<a[^>]*\s+name=["\']([^"\']+)["\'][^>]*>',
        re.IGNORECASE
    )
    
    def __init__(self, root_dir: str, dry_run: bool = True):
        self.root_dir = Path(root_dir).resolve()
        self.dry_run = dry_run
        self.stats = FixStats()
        self.all_md_files: Dict[str, Path] = {}  # 文件名 -> 路径映射
        self.file_anchors: Dict[Path, Set[str]] = {}
        self.file_content_cache: Dict[Path, str] = {}
        
        # 常见修复模式
        self.path_fixes = {
            # 术语词典路径修复
            'docs/FormalMath术语词典-基础数学.md': '00-标准术语表-8语言.md',
            'docs/FormalMath术语词典-代数结构.md': '00-标准术语表-8语言.md',
            'docs/FormalMath术语词典-分析学.md': '00-标准术语表-8语言.md',
            'docs/FormalMath术语词典-几何学.md': '00-标准术语表-8语言.md',
            'docs/FormalMath术语词典-拓扑学.md': '00-标准术语表-8语言.md',
            'docs/FormalMath术语词典-数论.md': '00-标准术语表-8语言.md',
        }
        
        # 扫描所有Markdown文件
        self._scan_all_files()
        
    def _scan_all_files(self):
        """扫描所有Markdown文件并建立索引"""
        for pattern in ['**/*.md', '**/*.markdown']:
            for f in self.root_dir.glob(pattern):
                if 'node_modules' in str(f) or '.git' in str(f):
                    continue
                self.all_md_files[f.name.lower()] = f
                
    def find_file_by_name(self, filename: str) -> Optional[Path]:
        """通过文件名查找文件"""
        # 直接匹配
        if filename.lower() in self.all_md_files:
            return self.all_md_files[filename.lower()]
        
        # 尝试添加.md扩展名
        if not filename.endswith('.md') and not filename.endswith('.markdown'):
            return self.all_md_files.get((filename + '.md').lower())
        
        return None
    
    def find_similar_files(self, target: str, max_results: int = 3) -> List[Tuple[Path, float]]:
        """查找相似的文件"""
        from difflib import SequenceMatcher
        
        target_lower = target.lower()
        matches = []
        
        for name, path in self.all_md_files.items():
            # 计算相似度
            similarity = SequenceMatcher(None, target_lower, name).ratio()
            
            # 如果目标包含在文件名中，提高相似度
            if target_lower.replace('.md', '') in name.replace('.md', ''):
                similarity += 0.2
            
            # 如果文件名包含目标，提高相似度
            if name.replace('.md', '') in target_lower.replace('.md', ''):
                similarity += 0.1
                
            matches.append((path, similarity))
        
        # 按相似度排序
        matches.sort(key=lambda x: x[1], reverse=True)
        return matches[:max_results]
    
    def extract_anchors(self, content: str) -> Set[str]:
        """从Markdown内容中提取所有锚点"""
        anchors = set()
        
        # 匹配标题
        for match in self.HEADER_PATTERN.finditer(content):
            header_text = match.group(1).strip()
            # 移除自定义锚点标记
            header_text = re.sub(r'\s*\{#[\w-]+\}\s*$', '', header_text)
            # 生成锚点ID
            anchor = self._generate_anchor_id(header_text)
            if anchor:
                anchors.add(anchor.lower())
        
        # 匹配自定义锚点
        for match in self.CUSTOM_ANCHOR_PATTERN.finditer(content):
            anchors.add(match.group(1).lower())
            
        return anchors
    
    def _generate_anchor_id(self, header_text: str) -> str:
        """根据标题文本生成GitHub风格的锚点ID"""
        # 移除 {#anchor} 部分
        header_text = re.sub(r'\s*\{#[\w-]+\}\s*$', '', header_text)
        
        # 转换为小写
        anchor = header_text.lower()
        
        # 移除Markdown格式标记
        anchor = re.sub(r'[_*~`]', '', anchor)
        
        # 替换空格和特殊字符为连字符
        anchor = re.sub(r'[^\w\s-]', '', anchor)
        anchor = re.sub(r'[\s]+', '-', anchor)
        
        # 移除首尾的连字符
        anchor = anchor.strip('-')
        
        return anchor
    
    def find_similar_anchors(self, file_path: Path, target_anchor: str, max_results: int = 3) -> List[Tuple[str, float]]:
        """查找相似的锚点"""
        from difflib import SequenceMatcher
        
        if file_path not in self.file_anchors:
            try:
                with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                    content = f.read()
                self.file_anchors[file_path] = self.extract_anchors(content)
            except Exception:
                return []
        
        anchors = self.file_anchors[file_path]
        target_lower = target_anchor.lower().lstrip('#')
        
        matches = []
        for anchor in anchors:
            similarity = SequenceMatcher(None, target_lower, anchor).ratio()
            
            # 如果目标包含在锚点中，提高相似度
            if target_lower in anchor:
                similarity += 0.3
            
            matches.append((anchor, similarity))
        
        matches.sort(key=lambda x: x[1], reverse=True)
        return matches[:max_results]
    
    def suggest_file_fix(self, source_file: Path, link_target: str) -> Optional[FixSuggestion]:
        """建议文件路径修复"""
        # 跳过外部链接
        if link_target.startswith(('http://', 'https://', 'ftp://', 'mailto:', 'tel:')):
            return None
        
        # 跳过纯锚点链接
        if link_target.startswith('#'):
            return None
        
        # 移除URL解码
        link_target = unquote(link_target)
        
        # 解析文件路径和锚点
        if '#' in link_target:
            file_part, anchor = link_target.split('#', 1)
        else:
            file_part, anchor = link_target, ''
        
        # 处理特殊情况
        if file_part == 'd' or not file_part:
            # 这可能是损坏的链接，建议删除或设为手动修复
            return FixSuggestion(
                source_file=str(source_file.relative_to(self.root_dir)),
                link_text='',
                original_target=link_target,
                suggested_target='',
                fix_type='remove',
                confidence=0.9,
                reason=f"无效链接目标 '{file_part}'，建议删除或手动检查"
            )
        
        # 尝试直接修复已知模式
        if file_part in self.path_fixes:
            fixed_path = self.path_fixes[file_part]
            if anchor:
                fixed_path = f"{fixed_path}#{anchor}"
            return FixSuggestion(
                source_file=str(source_file.relative_to(self.root_dir)),
                link_text='',
                original_target=link_target,
                suggested_target=fixed_path,
                fix_type='file_path',
                confidence=0.95,
                reason=f"已知路径映射: {file_part} -> {self.path_fixes[file_part]}"
            )
        
        # 尝试查找文件
        filename = Path(file_part).name
        found_file = self.find_file_by_name(filename)
        
        if found_file:
            # 计算相对路径
            try:
                rel_path = found_file.relative_to(source_file.parent)
                suggested = str(rel_path).replace('\\', '/')
                if anchor:
                    suggested = f"{suggested}#{anchor}"
                
                return FixSuggestion(
                    source_file=str(source_file.relative_to(self.root_dir)),
                    link_text='',
                    original_target=link_target,
                    suggested_target=suggested,
                    fix_type='file_path',
                    confidence=0.85,
                    reason=f"找到同名文件: {filename}"
                )
            except ValueError:
                pass
        
        # 查找相似文件
        similar_files = self.find_similar_files(filename)
        if similar_files and similar_files[0][1] > 0.6:
            best_match = similar_files[0]
            try:
                rel_path = best_match[0].relative_to(source_file.parent)
                suggested = str(rel_path).replace('\\', '/')
                if anchor:
                    suggested = f"{suggested}#{anchor}"
                
                return FixSuggestion(
                    source_file=str(source_file.relative_to(self.root_dir)),
                    link_text='',
                    original_target=link_target,
                    suggested_target=suggested,
                    fix_type='file_path',
                    confidence=best_match[1] * 0.8,
                    reason=f"相似文件匹配 (相似度: {best_match[1]:.2f})"
                )
            except ValueError:
                pass
        
        # 无法自动修复，建议手动处理
        return FixSuggestion(
            source_file=str(source_file.relative_to(self.root_dir)),
            link_text='',
            original_target=link_target,
            suggested_target='',
            fix_type='manual',
            confidence=0.0,
            reason=f"无法找到匹配文件，建议手动检查"
        )
    
    def suggest_anchor_fix(self, source_file: Path, target_file: Path, anchor: str) -> Optional[FixSuggestion]:
        """建议锚点修复"""
        if not anchor:
            return None
        
        anchor = anchor.lstrip('#')
        
        # 加载目标文件的锚点
        if target_file not in self.file_anchors:
            try:
                with open(target_file, 'r', encoding='utf-8', errors='ignore') as f:
                    content = f.read()
                self.file_anchors[target_file] = self.extract_anchors(content)
            except Exception:
                return None
        
        anchors = self.file_anchors[target_file]
        
        # 检查锚点是否已存在（可能是大小写问题）
        for existing_anchor in anchors:
            if existing_anchor.lower() == anchor.lower():
                if existing_anchor != anchor:
                    return FixSuggestion(
                        source_file=str(source_file.relative_to(self.root_dir)),
                        link_text='',
                        original_target=f"#{anchor}",
                        suggested_target=f"#{existing_anchor}",
                        fix_type='anchor',
                        confidence=0.95,
                        reason=f"大小写修正"
                    )
                return None  # 锚点已存在，没有问题
        
        # 查找相似锚点
        similar_anchors = self.find_similar_anchors(target_file, anchor)
        if similar_anchors and similar_anchors[0][1] > 0.7:
            best_match = similar_anchors[0]
            return FixSuggestion(
                source_file=str(source_file.relative_to(self.root_dir)),
                link_text='',
                original_target=f"#{anchor}",
                suggested_target=f"#{best_match[0]}",
                fix_type='anchor',
                confidence=best_match[1],
                reason=f"相似锚点匹配 (相似度: {best_match[1]:.2f})"
            )
        
        # 常见目录锚点修复
        common_toc_fixes = {
            '#-目录': '#目录',
            '#-目录--table-of-contents': '#目录',
            '#目录--table-of-contents': '#目录',
            '#-相关文档': '#相关文档',
            '#-文档信息': '#文档信息',
            '#-概述': '#概述',
            '#-一概述': '#一、概述',
        }
        
        anchor_key = f"#{anchor}"
        if anchor_key in common_toc_fixes:
            return FixSuggestion(
                source_file=str(source_file.relative_to(self.root_dir)),
                link_text='',
                original_target=f"#{anchor}",
                suggested_target=common_toc_fixes[anchor_key],
                fix_type='anchor',
                confidence=0.8,
                reason=f"常见锚点修正"
            )
        
        # 无法自动修复
        return FixSuggestion(
            source_file=str(source_file.relative_to(self.root_dir)),
            link_text='',
            original_target=f"#{anchor}",
            suggested_target='',
            fix_type='manual',
            confidence=0.0,
            reason=f"无法找到匹配锚点，建议手动检查或添加目标锚点"
        )
    
    def apply_fix(self, source_file: Path, suggestion: FixSuggestion) -> bool:
        """应用修复到文件"""
        if self.dry_run:
            return False
        
        try:
            with open(source_file, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
            
            original_content = content
            
            if suggestion.fix_type == 'remove':
                # 移除无效链接，保留链接文本
                pattern = rf'\[([^\]]*)\]\({re.escape(suggestion.original_target)}\)'
                content = re.sub(pattern, r'\1', content)
            else:
                # 替换链接目标
                pattern = rf'(\[([^\]]*)\]\(){re.escape(suggestion.original_target)}(\))'
                content = re.sub(pattern, rf'\1{suggestion.suggested_target}\3', content)
            
            if content != original_content:
                with open(source_file, 'w', encoding='utf-8') as f:
                    f.write(content)
                suggestion.applied = True
                return True
            
        except Exception as e:
            print(f"  错误: 无法修复 {source_file}: {e}")
        
        return False
    
    def process_issues(self, issues_file: str):
        """处理链接检查报告中的问题"""
        with open(issues_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
        
        issues = data.get('issues', [])
        self.stats.total_issues = len(issues)
        
        print(f"处理 {len(issues)} 个问题...")
        
        for i, issue in enumerate(issues, 1):
            if i % 1000 == 0:
                print(f"  进度: {i}/{len(issues)}")
            
            source_file = self.root_dir / issue['source_file']
            link_target = issue['link_target']
            issue_type = issue['issue_type']
            
            if issue_type == 'broken_file':
                suggestion = self.suggest_file_fix(source_file, link_target)
                if suggestion:
                    self.stats.suggestions.append(suggestion)
                    if suggestion.fix_type == 'file_path':
                        self.stats.file_path_fixes += 1
                    elif suggestion.fix_type == 'remove':
                        self.stats.removed_links += 1
                    elif suggestion.fix_type == 'manual':
                        self.stats.manual_review_needed += 1
                    
                    if not self.dry_run and suggestion.fix_type in ['file_path', 'remove']:
                        if self.apply_fix(source_file, suggestion):
                            self.stats.fixed_issues += 1
            
            elif issue_type == 'broken_anchor':
                # 解析文件路径和锚点
                if '#' in link_target:
                    file_part, anchor = link_target.split('#', 1)
                else:
                    file_part, anchor = '', link_target.lstrip('#')
                
                if file_part:
                    target_file = (source_file.parent / file_part).resolve()
                else:
                    target_file = source_file
                
                suggestion = self.suggest_anchor_fix(source_file, target_file, anchor)
                if suggestion:
                    self.stats.suggestions.append(suggestion)
                    if suggestion.fix_type == 'anchor':
                        self.stats.anchor_fixes += 1
                    elif suggestion.fix_type == 'manual':
                        self.stats.manual_review_needed += 1
                    
                    if not self.dry_run and suggestion.fix_type == 'anchor':
                        if self.apply_fix(source_file, suggestion):
                            self.stats.fixed_issues += 1
        
        self.stats.suggestions_made = len(self.stats.suggestions)
        print(f"处理完成，生成 {self.stats.suggestions_made} 个修复建议")
    
    def generate_report(self, output_file: str = None) -> str:
        """生成修复报告"""
        lines = []
        lines.append("链接修复报告")
        lines.append("=" * 60)
        lines.append(f"检查时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        lines.append(f"项目根目录: {self.root_dir}")
        lines.append(f"模式: {'干运行(预览)' if self.dry_run else '实际修复'}")
        lines.append("")
        
        # 统计信息
        lines.append("统计摘要:")
        lines.append(f"- 总问题数: {self.stats.total_issues}")
        lines.append(f"- 生成建议数: {self.stats.suggestions_made}")
        lines.append(f"- 文件路径修复: {self.stats.file_path_fixes}")
        lines.append(f"- 锚点修复: {self.stats.anchor_fixes}")
        lines.append(f"- 建议删除: {self.stats.removed_links}")
        lines.append(f"- 需手动处理: {self.stats.manual_review_needed}")
        if not self.dry_run:
            lines.append(f"- 实际修复数: {self.stats.fixed_issues}")
        lines.append("")
        
        # 高置信度修复建议
        high_confidence = [s for s in self.stats.suggestions if s.confidence >= 0.8]
        if high_confidence:
            lines.append(f"高置信度修复建议 ({len(high_confidence)} 个):")
            for s in high_confidence[:50]:  # 限制显示数量
                lines.append(f"\n[{s.fix_type}] {s.source_file}")
                lines.append(f"  原始: {s.original_target}")
                lines.append(f"  建议: {s.suggested_target}")
                lines.append(f"  置信度: {s.confidence:.2f}")
                lines.append(f"  原因: {s.reason}")
                if s.applied:
                    lines.append(f"  状态: ✓ 已应用")
            if len(high_confidence) > 50:
                lines.append(f"\n... 还有 {len(high_confidence) - 50} 个高置信度建议")
            lines.append("")
        
        # 中等置信度修复建议
        medium_confidence = [s for s in self.stats.suggestions if 0.5 <= s.confidence < 0.8]
        if medium_confidence:
            lines.append(f"中等置信度修复建议 ({len(medium_confidence)} 个, 建议检查):")
            for s in medium_confidence[:30]:
                lines.append(f"\n[{s.fix_type}] {s.source_file}")
                lines.append(f"  原始: {s.original_target}")
                lines.append(f"  建议: {s.suggested_target}")
                lines.append(f"  置信度: {s.confidence:.2f}")
                lines.append(f"  原因: {s.reason}")
            if len(medium_confidence) > 30:
                lines.append(f"\n... 还有 {len(medium_confidence) - 30} 个中等置信度建议")
            lines.append("")
        
        # 需手动处理的问题
        manual_fixes = [s for s in self.stats.suggestions if s.fix_type == 'manual']
        if manual_fixes:
            lines.append(f"需手动处理的问题 ({len(manual_fixes)} 个):")
            # 按源文件分组
            by_file: Dict[str, List[FixSuggestion]] = {}
            for s in manual_fixes:
                by_file.setdefault(s.source_file, []).append(s)
            
            for file, suggestions in list(by_file.items())[:20]:
                lines.append(f"\n  {file}:")
                for s in suggestions[:5]:
                    lines.append(f"    - {s.original_target}")
                    lines.append(f"      原因: {s.reason}")
                if len(suggestions) > 5:
                    lines.append(f"    ... 还有 {len(suggestions) - 5} 个问题")
            if len(by_file) > 20:
                lines.append(f"\n  ... 还有 {len(by_file) - 20} 个文件")
        
        report = '\n'.join(lines)
        
        if output_file:
            output_path = Path(output_file)
            output_path.parent.mkdir(parents=True, exist_ok=True)
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(report)
            print(f"\n报告已保存到: {output_path}")
        
        return report
    
    def generate_json_report(self, output_file: str = None) -> str:
        """生成JSON格式的详细报告"""
        report_data = {
            'fix_time': datetime.now().isoformat(),
            'root_directory': str(self.root_dir),
            'dry_run': self.dry_run,
            'statistics': {
                'total_issues': self.stats.total_issues,
                'suggestions_made': self.stats.suggestions_made,
                'file_path_fixes': self.stats.file_path_fixes,
                'anchor_fixes': self.stats.anchor_fixes,
                'removed_links': self.stats.removed_links,
                'manual_review_needed': self.stats.manual_review_needed,
                'fixed_issues': self.stats.fixed_issues
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
        
        json_str = json.dumps(report_data, ensure_ascii=False, indent=2)
        
        if output_file:
            output_path = Path(output_file)
            output_path.parent.mkdir(parents=True, exist_ok=True)
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(json_str)
            print(f"JSON报告已保存到: {output_path}")
        
        return json_str


def main():
    parser = argparse.ArgumentParser(
        description='FormalMath项目链接自动修复工具'
    )
    parser.add_argument(
        '--dry-run',
        action='store_true',
        help='仅显示修复建议，不实际修改文件'
    )
    parser.add_argument(
        '--root',
        default='.',
        help='项目根目录路径'
    )
    parser.add_argument(
        '--issues',
        default='output/link_check_report.json',
        help='链接检查报告JSON文件路径'
    )
    parser.add_argument(
        '--apply',
        action='store_true',
        help='实际应用修复(不使用--dry-run)'
    )
    
    args = parser.parse_args()
    
    root_dir = Path(args.root).resolve()
    issues_file = root_dir / args.issues
    
    if not issues_file.exists():
        print(f"错误: 链接检查报告不存在: {issues_file}")
        print("请先运行 link_checker.py 生成报告")
        sys.exit(1)
    
    dry_run = not args.apply
    
    print("=" * 60)
    print("FormalMath项目链接自动修复工具")
    print("=" * 60)
    print(f"项目根目录: {root_dir}")
    print(f"模式: {'干运行(预览)' if dry_run else '实际修复'}")
    print()
    
    # 创建修复器并处理
    fixer = LinkFixer(root_dir, dry_run=dry_run)
    fixer.process_issues(str(issues_file))
    
    # 生成报告
    print("\n生成报告...")
    report_output = root_dir / 'output' / 'link_fix_report.txt'
    fixer.generate_report(str(report_output))
    
    json_output = root_dir / 'output' / 'link_fix_report.json'
    fixer.generate_json_report(str(json_output))
    
    # 控制台输出摘要
    print("\n" + "=" * 60)
    print("修复摘要:")
    print(f"  - 总问题数: {fixer.stats.total_issues}")
    print(f"  - 生成建议数: {fixer.stats.suggestions_made}")
    print(f"  - 文件路径修复: {fixer.stats.file_path_fixes}")
    print(f"  - 锚点修复: {fixer.stats.anchor_fixes}")
    print(f"  - 建议删除: {fixer.stats.removed_links}")
    print(f"  - 需手动处理: {fixer.stats.manual_review_needed}")
    if not dry_run:
        print(f"  - 实际修复数: {fixer.stats.fixed_issues}")
    print("=" * 60)
    
    if dry_run:
        print("\n这是干运行模式，未实际修改文件。")
        print("使用 --apply 参数应用修复。")
    
    print(f"\n详细报告已保存到:")
    print(f"  - {report_output}")
    print(f"  - {json_output}")


if __name__ == '__main__':
    main()
