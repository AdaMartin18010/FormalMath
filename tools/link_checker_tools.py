#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath项目链接检查工具

功能:
- 检查内部链接有效性(Markdown文件之间的链接)
- 检查锚点引用正确性
- 生成链接检查报告

用法:
    python link_checker.py [项目根目录路径]
    
    如果不指定路径，默认使用当前工作目录

输出:
    - 控制台输出链接检查报告
    - 可选输出JSON格式的详细报告
"""

import os
import re
import sys
import json
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Tuple, Set
from dataclasses import dataclass, field, asdict
from urllib.parse import urlparse, unquote


@dataclass
class LinkIssue:
    """链接问题记录"""
    source_file: str
    link_text: str
    link_target: str
    issue_type: str  # 'broken_file', 'broken_anchor', 'empty_link'
    line_number: int = 0
    
    def __str__(self):
        rel_source = self.source_file
        if self.issue_type == 'broken_file':
            return f"{rel_source}: [broken file] {self.link_target}"
        elif self.issue_type == 'broken_anchor':
            return f"{rel_source}: [broken anchor] {self.link_target}"
        elif self.issue_type == 'empty_link':
            return f"{rel_source}: [empty link] '{self.link_text}'"
        else:
            return f"{rel_source}: [{self.issue_type}] {self.link_target}"


@dataclass
class LinkStats:
    """链接统计信息"""
    total_files: int = 0
    total_links: int = 0
    valid_links: int = 0
    invalid_links: int = 0
    internal_links: int = 0
    anchor_links: int = 0
    external_links: int = 0
    issues: List[LinkIssue] = field(default_factory=list)
    
    @property
    def valid_rate(self) -> float:
        if self.total_links == 0:
            return 100.0
        return (self.valid_links / self.total_links) * 100
    
    @property
    def invalid_rate(self) -> float:
        if self.total_links == 0:
            return 0.0
        return (self.invalid_links / self.total_links) * 100


class LinkChecker:
    """Markdown链接检查器"""
    
    # Markdown链接正则表达式模式
    LINK_PATTERN = re.compile(
        r'!?\[([^\]]*)\]\(([^)]+)\)',
        re.MULTILINE | re.DOTALL
    )
    
    # 锚点定义模式 (## Header {#anchor} 或 ## Header)
    ANCHOR_PATTERN = re.compile(
        r'^#{1,6}\s+(.+?)(?:\s+\{#[\w-]+\})?$',
        re.MULTILINE
    )
    
    # HTML锚点模式 <a name="anchor">
    HTML_ANCHOR_PATTERN = re.compile(
        r'<a[^>]*\s+name=["\']([^"\']+)["\'][^>]*>',
        re.IGNORECASE
    )
    
    # 自动生成的锚点ID模式
    AUTO_ANCHOR_PATTERN = re.compile(
        r'^#{1,6}\s+(.+?)$',
        re.MULTILINE
    )
    
    def __init__(self, root_dir: str):
        self.root_dir = Path(root_dir).resolve()
        self.stats = LinkStats()
        self.all_md_files: Set[Path] = set()
        self.file_anchors: Dict[Path, Set[str]] = {}
        
    def scan_markdown_files(self) -> List[Path]:
        """递归扫描所有Markdown文件"""
        md_files = []
        for pattern in ['**/*.md', '**/*.markdown']:
            md_files.extend(self.root_dir.glob(pattern))
        
        # 过滤掉node_modules等目录
        md_files = [
            f for f in md_files 
            if 'node_modules' not in str(f) and '.git' not in str(f)
        ]
        
        self.all_md_files = set(md_files)
        self.stats.total_files = len(md_files)
        return md_files
    
    def extract_anchors(self, content: str) -> Set[str]:
        """从Markdown内容中提取所有锚点"""
        anchors = set()
        
        # 匹配标题中的锚点 {#anchor}
        for match in self.ANCHOR_PATTERN.finditer(content):
            header_text = match.group(1).strip()
            # 提取显式锚点
            anchor_match = re.search(r'\{#([\w-]+)\}$', header_text)
            if anchor_match:
                anchors.add(anchor_match.group(1).lower())
            
            # 自动生成锚点ID
            auto_anchor = self._generate_anchor_id(header_text)
            if auto_anchor:
                anchors.add(auto_anchor.lower())
        
        # 匹配HTML锚点 <a name="anchor">
        for match in self.HTML_ANCHOR_PATTERN.finditer(content):
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
    
    def parse_link(self, link_target: str) -> Tuple[str, str]:
        """解析链接目标，返回(文件路径, 锚点)"""
        if '#' in link_target:
            parts = link_target.split('#', 1)
            return parts[0], parts[1]
        return link_target, ''
    
    def is_external_link(self, link_target: str) -> bool:
        """检查是否为外部链接"""
        if not link_target:
            return False
        return (
            link_target.startswith('http://') or
            link_target.startswith('https://') or
            link_target.startswith('ftp://') or
            link_target.startswith('mailto:') or
            link_target.startswith('tel:')
        )
    
    def is_anchor_only_link(self, link_target: str) -> bool:
        """检查是否仅为锚点链接（同一文件内）"""
        return link_target.startswith('#')
    
    def check_file_exists(self, file_path: Path) -> bool:
        """检查文件是否存在"""
        return file_path.exists() and file_path.is_file()
    
    def check_anchor_exists(self, file_path: Path, anchor: str) -> bool:
        """检查锚点是否存在于文件中"""
        if file_path not in self.file_anchors:
            return False
        return anchor.lower() in self.file_anchors[file_path]
    
    def process_file(self, md_file: Path) -> List[LinkIssue]:
        """处理单个Markdown文件，返回问题列表"""
        issues = []
        
        try:
            with open(md_file, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
        except Exception as e:
            print(f"警告: 无法读取文件 {md_file}: {e}")
            return issues
        
        # 提取该文件的所有锚点
        self.file_anchors[md_file] = self.extract_anchors(content)
        
        # 查找所有链接
        for match in self.LINK_PATTERN.finditer(content):
            link_text = match.group(1).strip()
            link_target = match.group(2).strip()
            
            # 跳过图片链接（如果检查的是图片链接）
            if match.group(0).startswith('!'):
                continue
            
            # 跳过空链接
            if not link_target:
                issues.append(LinkIssue(
                    source_file=str(md_file.relative_to(self.root_dir)),
                    link_text=link_text,
                    link_target='',
                    issue_type='empty_link',
                    line_number=content[:match.start()].count('\n') + 1
                ))
                self.stats.total_links += 1
                self.stats.invalid_links += 1
                continue
            
            self.stats.total_links += 1
            
            # 跳过外部链接
            if self.is_external_link(link_target):
                self.stats.external_links += 1
                self.stats.valid_links += 1
                continue
            
            # 解码URL编码
            link_target = unquote(link_target)
            
            # 处理仅为锚点的链接
            if self.is_anchor_only_link(link_target):
                self.stats.anchor_links += 1
                anchor = link_target[1:]  # 移除开头的#
                if not self.check_anchor_exists(md_file, anchor):
                    issues.append(LinkIssue(
                        source_file=str(md_file.relative_to(self.root_dir)),
                        link_text=link_text,
                        link_target=link_target,
                        issue_type='broken_anchor',
                        line_number=content[:match.start()].count('\n') + 1
                    ))
                    self.stats.invalid_links += 1
                else:
                    self.stats.valid_links += 1
                continue
            
            # 处理文件链接
            file_part, anchor = self.parse_link(link_target)
            
            # 解析文件路径
            if file_part:
                # 相对路径解析
                target_file = (md_file.parent / file_part).resolve()
                
                # 检查是否在项目根目录下
                try:
                    target_file.relative_to(self.root_dir)
                except ValueError:
                    # 路径在项目根目录外，跳过检查
                    self.stats.valid_links += 1
                    continue
            else:
                # 只有锚点，指向当前文件
                target_file = md_file
            
            self.stats.internal_links += 1
            
            # 检查文件是否存在
            if not self.check_file_exists(target_file):
                # 尝试添加.md扩展名
                if not file_part.endswith('.md') and not file_part.endswith('.markdown'):
                    target_file_with_ext = Path(str(target_file) + '.md')
                    if self.check_file_exists(target_file_with_ext):
                        target_file = target_file_with_ext
                    else:
                        target_file_with_ext = Path(str(target_file) + '.markdown')
                        if self.check_file_exists(target_file_with_ext):
                            target_file = target_file_with_ext
                
                if not self.check_file_exists(target_file):
                    issues.append(LinkIssue(
                        source_file=str(md_file.relative_to(self.root_dir)),
                        link_text=link_text,
                        link_target=link_target,
                        issue_type='broken_file',
                        line_number=content[:match.start()].count('\n') + 1
                    ))
                    self.stats.invalid_links += 1
                    continue
            
            # 检查锚点
            if anchor:
                self.stats.anchor_links += 1
                # 确保目标文件的锚点已加载
                if target_file not in self.file_anchors:
                    try:
                        with open(target_file, 'r', encoding='utf-8', errors='ignore') as f:
                            target_content = f.read()
                        self.file_anchors[target_file] = self.extract_anchors(target_content)
                    except Exception:
                        self.file_anchors[target_file] = set()
                
                if not self.check_anchor_exists(target_file, anchor):
                    issues.append(LinkIssue(
                        source_file=str(md_file.relative_to(self.root_dir)),
                        link_text=link_text,
                        link_target=link_target,
                        issue_type='broken_anchor',
                        line_number=content[:match.start()].count('\n') + 1
                    ))
                    self.stats.invalid_links += 1
                    continue
            
            self.stats.valid_links += 1
        
        return issues
    
    def run(self) -> LinkStats:
        """运行链接检查"""
        print("开始扫描Markdown文件...")
        md_files = self.scan_markdown_files()
        print(f"发现 {len(md_files)} 个Markdown文件\n")
        
        print("开始检查链接...")
        for i, md_file in enumerate(md_files, 1):
            if i % 500 == 0 or i == len(md_files):
                print(f"  进度: {i}/{len(md_files)} 文件已处理...")
            
            issues = self.process_file(md_file)
            self.stats.issues.extend(issues)
        
        return self.stats
    
    def generate_report(self, output_file: str = None) -> str:
        """生成检查报告"""
        lines = []
        lines.append("链接检查报告")
        lines.append("=" * 50)
        lines.append(f"检查时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        lines.append(f"检查目录: {self.root_dir}")
        lines.append(f"检查文件数: {self.stats.total_files}")
        lines.append("")
        
        # 无效链接
        if self.stats.issues:
            lines.append(f"无效链接 ({len(self.stats.issues)} 个):")
            for issue in self.stats.issues:
                lines.append(f"- {issue}")
            lines.append("")
        else:
            lines.append("无效链接: 无\n")
        
        # 统计信息
        lines.append("统计:")
        lines.append(f"- 总链接数: {self.stats.total_links}")
        lines.append(f"- 内部文件链接: {self.stats.internal_links}")
        lines.append(f"- 锚点链接: {self.stats.anchor_links}")
        lines.append(f"- 外部链接: {self.stats.external_links}")
        lines.append(f"- 有效链接: {self.stats.valid_links} ({self.stats.valid_rate:.1f}%)")
        lines.append(f"- 无效链接: {self.stats.invalid_links} ({self.stats.invalid_rate:.1f}%)")
        
        report = '\n'.join(lines)
        
        # 输出到文件
        if output_file:
            output_path = Path(output_file)
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(report)
            print(f"\n报告已保存到: {output_path}")
        
        return report
    
    def generate_json_report(self, output_file: str = None) -> str:
        """生成JSON格式的详细报告"""
        report_data = {
            'check_time': datetime.now().isoformat(),
            'root_directory': str(self.root_dir),
            'statistics': {
                'total_files': self.stats.total_files,
                'total_links': self.stats.total_links,
                'valid_links': self.stats.valid_links,
                'invalid_links': self.stats.invalid_links,
                'internal_links': self.stats.internal_links,
                'anchor_links': self.stats.anchor_links,
                'external_links': self.stats.external_links,
                'valid_rate_percent': round(self.stats.valid_rate, 2),
                'invalid_rate_percent': round(self.stats.invalid_rate, 2)
            },
            'issues': [
                {
                    'source_file': issue.source_file,
                    'link_text': issue.link_text,
                    'link_target': issue.link_target,
                    'issue_type': issue.issue_type,
                    'line_number': issue.line_number
                }
                for issue in self.stats.issues
            ]
        }
        
        json_str = json.dumps(report_data, ensure_ascii=False, indent=2)
        
        if output_file:
            output_path = Path(output_file)
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(json_str)
            print(f"JSON报告已保存到: {output_path}")
        
        return json_str


def main():
    """主函数"""
    # 解析命令行参数
    if len(sys.argv) > 1:
        root_dir = sys.argv[1]
    else:
        root_dir = os.getcwd()
    
    # 检查目录是否存在
    if not os.path.isdir(root_dir):
        print(f"错误: 目录不存在: {root_dir}")
        sys.exit(1)
    
    print(f"FormalMath项目链接检查工具")
    print(f"{'='*50}\n")
    print(f"项目根目录: {root_dir}\n")
    
    # 创建链接检查器并运行
    checker = LinkChecker(root_dir)
    stats = checker.run()
    
    # 生成报告
    print("\n" + "="*50)
    report = checker.generate_report()
    print("\n" + report)
    
    # 同时生成JSON报告
    json_output = Path(root_dir) / 'output' / 'link_check_report.json'
    json_output.parent.mkdir(parents=True, exist_ok=True)
    checker.generate_json_report(str(json_output))
    
    # 生成文本报告
    text_output = Path(root_dir) / 'output' / 'link_check_report.txt'
    checker.generate_report(str(text_output))
    
    # 返回退出码
    if stats.invalid_links > 0:
        print(f"\n发现 {stats.invalid_links} 个无效链接，请修复。")
        sys.exit(1)
    else:
        print("\n所有链接检查通过！")
        sys.exit(0)


if __name__ == '__main__':
    main()
