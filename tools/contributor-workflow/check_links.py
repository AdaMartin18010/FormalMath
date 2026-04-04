#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
链接检查脚本

检查 Markdown 文档中的内部链接是否有效
"""

import argparse
import re
import sys
from pathlib import Path
from typing import List, Set, Dict, Tuple
from dataclasses import dataclass
from urllib.parse import urlparse


@dataclass
class LinkCheckResult:
    """链接检查结果"""
    source_file: str
    target: str
    line: int
    link_type: str  # internal, anchor, external
    is_valid: bool
    message: str


class LinkChecker:
    """链接检查器"""
    
    def __init__(self, project_root: str = "."):
        self.project_root = Path(project_root)
        self.results: List[LinkCheckResult] = []
        self.all_files: Set[Path] = set()
        self.all_anchors: Dict[str, Set[str]] = {}
    
    def scan_files(self, paths: List[str]) -> None:
        """扫描所有文件"""
        for path_str in paths:
            path = self.project_root / path_str
            if path.is_file() and path.suffix == '.md':
                self.all_files.add(path.resolve())
                self._extract_anchors(path)
            elif path.is_dir():
                for md_file in path.rglob('*.md'):
                    if 'node_modules' not in str(md_file):
                        self.all_files.add(md_file.resolve())
                        self._extract_anchors(md_file)
    
    def _extract_anchors(self, filepath: Path) -> None:
        """提取文件中的所有锚点"""
        try:
            content = filepath.read_text(encoding='utf-8')
        except Exception:
            return
        
        anchors = set()
        
        # 提取标题锚点
        for line in content.split('\n'):
            if line.startswith('#'):
                # 生成锚点 ID
                title = re.sub(r'^#+\s*', '', line)
                anchor = self._generate_anchor_id(title)
                if anchor:
                    anchors.add(anchor)
        
        # 也提取显式锚点 <a name="...">
        for match in re.finditer(r'<a[^>]+name=["\']([^"\']+)["\']', content):
            anchors.add(match.group(1))
        
        self.all_anchors[str(filepath.resolve())] = anchors
    
    def _generate_anchor_id(self, title: str) -> str:
        """生成锚点 ID（GitHub 风格）"""
        # 移除 Markdown 格式
        title = re.sub(r'\[([^\]]+)\]\([^\)]+\)', r'\1', title)
        title = re.sub(r'[*_`]', '', title)
        
        # 转换为小写，替换空格为连字符
        anchor = title.lower().strip()
        anchor = re.sub(r'[^\w\s-]', '', anchor)
        anchor = re.sub(r'\s+', '-', anchor)
        anchor = anchor.strip('-')
        
        return anchor
    
    def check_links(self, check_internal: bool = True, 
                   check_external: bool = False) -> None:
        """检查所有链接"""
        for filepath in self.all_files:
            self._check_file_links(filepath, check_internal, check_external)
    
    def _check_file_links(self, filepath: Path, check_internal: bool,
                         check_external: bool) -> None:
        """检查单个文件的链接"""
        try:
            content = filepath.read_text(encoding='utf-8')
        except Exception as e:
            self.results.append(LinkCheckResult(
                source_file=str(filepath),
                target='',
                line=0,
                link_type='error',
                is_valid=False,
                message=f"无法读取文件: {e}"
            ))
            return
        
        lines = content.split('\n')
        
        for line_num, line in enumerate(lines, 1):
            # 查找 Markdown 链接
            for match in re.finditer(r'\[([^\]]+)\]\(([^)]+)\)', line):
                link_text = match.group(1)
                link_target = match.group(2)
                
                # 跳过图片
                if match.start() > 0 and line[match.start() - 1] == '!':
                    continue
                
                # 分类链接
                if link_target.startswith('#'):
                    # 锚点链接
                    if check_internal:
                        self._check_anchor_link(filepath, link_target, line_num)
                elif link_target.startswith(('http://', 'https://')):
                    # 外部链接
                    if check_external:
                        self._check_external_link(filepath, link_target, line_num)
                elif not link_target.startswith(('mailto:', 'tel:')):
                    # 内部文件链接
                    if check_internal:
                        self._check_internal_link(filepath, link_target, line_num)
    
    def _check_anchor_link(self, filepath: Path, target: str, line: int) -> None:
        """检查锚点链接"""
        anchor = target[1:]  # 移除 #
        
        file_key = str(filepath.resolve())
        anchors = self.all_anchors.get(file_key, set())
        
        # 生成可能的锚点 ID 变体
        possible_anchors = {
            anchor,
            anchor.lower(),
            self._generate_anchor_id(anchor),
        }
        
        is_valid = bool(anchors & possible_anchors)
        
        self.results.append(LinkCheckResult(
            source_file=str(filepath),
            target=target,
            line=line,
            link_type='anchor',
            is_valid=is_valid,
            message="" if is_valid else f"锚点不存在: {anchor}"
        ))
    
    def _check_internal_link(self, filepath: Path, target: str, line: int) -> None:
        """检查内部文件链接"""
        # 移除锚点部分
        target_path = target.split('#')[0]
        
        if not target_path:
            return
        
        # 解析相对路径
        if target_path.startswith('/'):
            # 绝对路径（相对于项目根）
            full_path = self.project_root / target_path[1:]
        else:
            # 相对路径
            full_path = filepath.parent / target_path
        
        full_path = full_path.resolve()
        
        # 检查文件是否存在
        is_valid = full_path.exists() or full_path in self.all_files
        
        self.results.append(LinkCheckResult(
            source_file=str(filepath),
            target=target,
            line=line,
            link_type='internal',
            is_valid=is_valid,
            message="" if is_valid else f"文件不存在: {target_path}"
        ))
    
    def _check_external_link(self, filepath: Path, target: str, line: int) -> None:
        """检查外部链接（简化版，不实际访问）"""
        # 仅检查格式
        parsed = urlparse(target)
        is_valid = bool(parsed.scheme and parsed.netloc)
        
        self.results.append(LinkCheckResult(
            source_file=str(filepath),
            target=target,
            line=line,
            link_type='external',
            is_valid=is_valid,
            message="" if is_valid else "URL 格式无效"
        ))
    
    def print_report(self) -> None:
        """打印检查报告"""
        print("=" * 70)
        print("链接检查报告")
        print("=" * 70)
        print()
        
        broken = [r for r in self.results if not r.is_valid]
        valid = [r for r in self.results if r.is_valid]
        
        print(f"总链接数: {len(self.results)}")
        print(f"有效链接: {len(valid)}")
        print(f"失效链接: {len(broken)}")
        print()
        
        if broken:
            print("失效链接详情:")
            print()
            
            # 按文件分组
            by_file: Dict[str, List[LinkCheckResult]] = {}
            for r in broken:
                by_file.setdefault(r.source_file, []).append(r)
            
            for filepath, results in sorted(by_file.items()):
                print(f"  📄 {filepath}")
                for r in results:
                    print(f"     第 {r.line} 行: [{r.link_type}] {r.target}")
                    print(f"       → {r.message}")
                print()
        else:
            print("✅ 所有链接有效！")
        
        print("=" * 70)


def main():
    parser = argparse.ArgumentParser(description='链接检查')
    parser.add_argument('--paths', nargs='+', required=True,
                       help='要检查的路径')
    parser.add_argument('--check-internal', action='store_true',
                       help='检查内部链接')
    parser.add_argument('--check-external', action='store_true',
                       help='检查外部链接（仅格式）')
    parser.add_argument('--fail-on-broken', action='store_true',
                       help='发现失效链接时返回非零退出码')
    
    args = parser.parse_args()
    
    checker = LinkChecker()
    checker.scan_files(args.paths)
    checker.check_links(
        check_internal=args.check_internal,
        check_external=args.check_external
    )
    checker.print_report()
    
    if args.fail_on_broken:
        broken_count = sum(1 for r in checker.results if not r.is_valid)
        return 0 if broken_count == 0 else 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
