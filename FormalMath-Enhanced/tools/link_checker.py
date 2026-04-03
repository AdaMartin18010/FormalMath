#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
文档链接检查器 (Link Checker)

功能:
- 检查所有Markdown文件中的链接
- 报告断链
- 生成链接地图

使用示例:
    python link_checker.py --input docs/
    python link_checker.py --check-external --output report.md
    python link_checker.py --fix --backup

作者: FormalMath-Enhanced
版本: 1.0.0
"""

import argparse
import re
import json
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional, Set, Tuple
from dataclasses import dataclass, field
from urllib.parse import urlparse
from enum import Enum
import concurrent.futures


class LinkType(Enum):
    """链接类型"""
    INTERNAL = "internal"  # 内部文件链接
    EXTERNAL = "external"  # 外部URL
    ANCHOR = "anchor"      # 页内锚点
    ABSOLUTE = "absolute"  # 绝对路径


class LinkStatus(Enum):
    """链接状态"""
    VALID = "valid"
    BROKEN = "broken"
    EXTERNAL = "external"  # 外部链接，未检查
    WARNING = "warning"


@dataclass
class Link:
    """链接数据结构"""
    url: str
    text: str
    link_type: LinkType
    source_file: Path
    line_number: int
    status: LinkStatus = LinkStatus.VALID
    error_message: Optional[str] = None
    suggestion: Optional[str] = None


@dataclass
class LinkReport:
    """链接检查报告"""
    total_links: int = 0
    valid_links: int = 0
    broken_links: int = 0
    external_links: int = 0
    warning_links: int = 0
    links: List[Link] = field(default_factory=list)
    checked_files: Set[str] = field(default_factory=set)
    timestamp: str = field(default_factory=lambda: datetime.now().isoformat())


class LinkExtractor:
    """链接提取器"""

    # Markdown链接模式
    LINK_PATTERN = re.compile(
        r'!?\[([^\]]*)\]\(([^)]+)\)',
        re.MULTILINE
    )

    # HTML链接模式
    HTML_LINK_PATTERN = re.compile(
        r'<a[^>]+href=["\']([^"\']+)["\'][^>]*>([^<]*)</a>',
        re.IGNORECASE
    )

    # 引用链接模式 [text][ref]
    REF_LINK_PATTERN = re.compile(
        r'\[([^\]]+)\]\[([^\]]*)\]'
    )

    def __init__(self, base_path: Path):
        self.base_path = base_path.resolve()

    def extract_links(self, file_path: Path) -> List[Link]:
        """
        从Markdown文件中提取链接

        Args:
            file_path: 文件路径

        Returns:
            链接列表
        """
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                lines = content.split('\n')
        except Exception as e:
            print(f"警告: 无法读取文件 {file_path}: {e}")
            return []

        links = []

        # 提取Markdown链接
        for match in self.LINK_PATTERN.finditer(content):
            text = match.group(1)
            url = match.group(2)

            # 找到行号
            line_number = content[:match.start()].count('\n') + 1

            # 去除URL中的标题部分
            url = url.split(' ')[0].strip()

            link_type = self._classify_link(url)

            links.append(Link(
                url=url,
                text=text,
                link_type=link_type,
                source_file=file_path,
                line_number=line_number
            ))

        # 提取HTML链接
        for match in self.HTML_LINK_PATTERN.finditer(content):
            url = match.group(1)
            text = match.group(2)
            line_number = content[:match.start()].count('\n') + 1

            link_type = self._classify_link(url)

            links.append(Link(
                url=url,
                text=text,
                link_type=link_type,
                source_file=file_path,
                line_number=line_number
            ))

        return links

    def _classify_link(self, url: str) -> LinkType:
        """分类链接类型"""
        url = url.strip()

        # 检查是否是锚点
        if url.startswith('#'):
            return LinkType.ANCHOR

        # 检查是否是外部链接
        parsed = urlparse(url)
        if parsed.scheme in ('http', 'https', 'ftp'):
            return LinkType.EXTERNAL

        # 检查是否是绝对路径
        if url.startswith('/') or url.startswith('\\'):
            return LinkType.ABSOLUTE

        # 否则是内部相对链接
        return LinkType.INTERNAL


class LinkValidator:
    """链接验证器"""

    def __init__(self, base_path: Path):
        self.base_path = base_path.resolve()
        self.checked_paths: Set[Path] = set()

    def validate_link(self, link: Link) -> Link:
        """
        验证单个链接

        Args:
            link: 链接对象

        Returns:
            更新后的链接对象
        """
        if link.link_type == LinkType.EXTERNAL:
            link.status = LinkStatus.EXTERNAL
            return link

        if link.link_type == LinkType.ANCHOR:
            # 页内锚点，在当前文件检查
            return self._validate_anchor(link)

        # 解析目标路径
        target_path = self._resolve_path(link.url, link.source_file)

        if target_path is None:
            link.status = LinkStatus.BROKEN
            link.error_message = f"无法解析路径: {link.url}"
            return link

        # 检查是否存在
        if target_path.exists():
            link.status = LinkStatus.VALID

            # 检查是否有锚点部分
            if '#' in link.url:
                return self._validate_anchor(link, target_path)
        else:
            link.status = LinkStatus.BROKEN
            link.error_message = f"文件不存在: {target_path.relative_to(self.base_path)}"

            # 尝试提供建议
            suggestion = self._suggest_fix(link.url, link.source_file)
            if suggestion:
                link.suggestion = suggestion

        return link

    def _resolve_path(self, url: str, source_file: Path) -> Optional[Path]:
        """解析URL为实际路径"""
        # 去除锚点
        if '#' in url:
            url = url.split('#')[0]

        if not url:
            return None

        if url.startswith('/') or url.startswith('\\'):
            # 绝对路径
            return self.base_path / url.lstrip('/\\')
        else:
            # 相对路径
            return source_file.parent / url

    def _validate_anchor(self, link: Link, target_file: Optional[Path] = None) -> Link:
        """验证锚点"""
        if '#' not in link.url:
            return link

        anchor = link.url.split('#')[1]

        if target_file is None:
            target_file = link.source_file

        try:
            with open(target_file, 'r', encoding='utf-8') as f:
                content = f.read()

            # 检查各种锚点格式
            # Markdown标题: # Title {#anchor} 或 # Title
            # HTML锚点: <a name="anchor">
            patterns = [
                rf'\{{#\s*{re.escape(anchor)}\s*\}}',
                rf'<a[^>]+name=["\']{re.escape(anchor)}["\']',
                rf'<a[^>]+id=["\']{re.escape(anchor)}["\']',
                rf'\[#{re.escape(anchor)}\]',
            ]

            # 也检查标题本身
            title_pattern = rf'^#+\s+{re.escape(anchor.replace("-", " "))}\s*$'

            found = False
            for pattern in patterns:
                if re.search(pattern, content, re.MULTILINE | re.IGNORECASE):
                    found = True
                    break

            if not found:
                # 检查标题slug格式
                anchor_slug = anchor.lower().replace(' ', '-')
                for line in content.split('\n'):
                    if line.startswith('#'):
                        title = line.lstrip('#').strip().lower().replace(' ', '-')
                        if title == anchor_slug:
                            found = True
                            break

            if not found:
                link.status = LinkStatus.WARNING
                link.error_message = f"锚点未找到: #{anchor}"

        except Exception as e:
            link.status = LinkStatus.WARNING
            link.error_message = f"无法验证锚点: {e}"

        return link

    def _suggest_fix(self, url: str, source_file: Path) -> Optional[str]:
        """建议修复"""
        # 尝试找到相似文件
        filename = Path(url).name

        # 搜索可能的匹配
        for ext in ['', '.md', '.markdown', '.html']:
            search_pattern = f"**/{filename}{ext}"
            matches = list(self.base_path.glob(search_pattern))

            if matches:
                # 返回第一个匹配的相对路径
                relative = matches[0].relative_to(source_file.parent)
                return str(relative).replace('\\', '/')

        return None


class LinkMapGenerator:
    """链接地图生成器"""

    def __init__(self, links: List[Link], base_path: Path):
        self.links = links
        self.base_path = base_path

    def generate_graph(self) -> Dict:
        """生成图数据"""
        nodes = set()
        edges = []

        for link in self.links:
            source = str(link.source_file.relative_to(self.base_path))

            if link.link_type == LinkType.INTERNAL:
                target = link.url
            elif link.link_type == LinkType.ABSOLUTE:
                target = link.url
            else:
                continue

            nodes.add(source)
            nodes.add(target)

            edges.append({
                'source': source,
                'target': target,
                'type': link.link_type.value
            })

        return {
            'nodes': [{'id': n, 'label': Path(n).name} for n in nodes],
            'edges': edges
        }

    def generate_mermaid(self) -> str:
        """生成Mermaid图"""
        mermaid = "```mermaid\ngraph TD\n"

        # 收集连接
        connections = set()
        for link in self.links:
            if link.link_type in (LinkType.INTERNAL, LinkType.ABSOLUTE):
                source = Path(link.source_file).stem
                target = Path(link.url).stem
                connections.add(f"    {source}[{source}] --> {target}[{target}]")

        mermaid += '\n'.join(sorted(connections))
        mermaid += "\n```"

        return mermaid


class ReportGenerator:
    """报告生成器"""

    def __init__(self, report: LinkReport, base_path: Path):
        self.report = report
        self.base_path = base_path

    def generate_markdown(self) -> str:
        """生成Markdown报告"""
        md = f"""# 链接检查报告

生成时间: {self.report.timestamp}

## 统计摘要

| 指标 | 数值 |
|------|------|
| 总链接数 | {self.report.total_links} |
| 有效链接 | {self.report.valid_links} ✅ |
| 损坏链接 | {self.report.broken_links} ❌ |
| 外部链接 | {self.report.external_links} 🌐 |
| 警告链接 | {self.report.warning_links} ⚠️ |

## 损坏的链接

"""

        broken = [l for l in self.report.links if l.status == LinkStatus.BROKEN]
        if broken:
            md += "| 文件 | 行号 | 链接文本 | URL | 错误 | 建议修复 |\n"
            md += "|------|------|----------|-----|------|----------|\n"

            for link in broken:
                source = str(link.source_file.relative_to(self.base_path))
                suggestion = link.suggestion or "-"
                md += f"| `{source}` | {link.line_number} | {link.text[:30]} | `{link.url}` | {link.error_message} | {suggestion} |\n"
        else:
            md += "✅ 没有发现损坏的链接！\n"

        md += "\n## 警告的链接\n\n"

        warnings = [l for l in self.report.links if l.status == LinkStatus.WARNING]
        if warnings:
            md += "| 文件 | 行号 | 链接文本 | URL | 警告 |\n"
            md += "|------|------|----------|-----|------|\n"

            for link in warnings:
                source = str(link.source_file.relative_to(self.base_path))
                md += f"| `{source}` | {link.line_number} | {link.text[:30]} | `{link.url}` | {link.error_message} |\n"
        else:
            md += "✅ 没有警告的链接\n"

        md += "\n## 文件列表\n\n"
        for f in sorted(self.report.checked_files):
            md += f"- `{f}`\n"

        return md

    def generate_json(self) -> str:
        """生成JSON报告"""
        data = {
            'timestamp': self.report.timestamp,
            'summary': {
                'total': self.report.total_links,
                'valid': self.report.valid_links,
                'broken': self.report.broken_links,
                'external': self.report.external_links,
                'warning': self.report.warning_links
            },
            'links': [
                {
                    'url': l.url,
                    'text': l.text,
                    'source': str(l.source_file),
                    'line': l.line_number,
                    'type': l.link_type.value,
                    'status': l.status.value,
                    'error': l.error_message,
                    'suggestion': l.suggestion
                }
                for l in self.report.links
            ]
        }

        return json.dumps(data, indent=2, ensure_ascii=False)


class LinkFixer:
    """链接修复器"""

    def __init__(self, base_path: Path, backup: bool = True):
        self.base_path = base_path
        self.backup = backup

    def fix_link(self, link: Link) -> bool:
        """修复单个链接"""
        if not link.suggestion or link.status != LinkStatus.BROKEN:
            return False

        try:
            # 创建备份
            if self.backup and not link.source_file.with_suffix('.md.bak').exists():
                import shutil
                shutil.copy2(link.source_file,
                           link.source_file.with_suffix('.md.bak'))

            # 读取文件
            with open(link.source_file, 'r', encoding='utf-8') as f:
                content = f.read()

            # 定位并替换链接
            lines = content.split('\n')
            if 0 <= link.line_number - 1 < len(lines):
                line = lines[link.line_number - 1]
                # 替换URL
                fixed_line = line.replace(f']({link.url})', f']({link.suggestion})')
                lines[link.line_number - 1] = fixed_line

                # 写回文件
                with open(link.source_file, 'w', encoding='utf-8') as f:
                    f.write('\n'.join(lines))

                return True

        except Exception as e:
            print(f"修复失败 {link.source_file}:{link.line_number}: {e}")

        return False


def main():
    parser = argparse.ArgumentParser(
        description="文档链接检查器",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
使用示例:
  %(prog)s --input docs/
  %(prog)s --check-external --workers 10
  %(prog)s --output report.md --format markdown
  %(prog)s --fix --backup
  %(prog)s --map --output link-map.md
        """
    )

    parser.add_argument('--input', '-i', type=Path, default=Path('.'),
                       help='输入目录')
    parser.add_argument('--check-external', '-e', action='store_true',
                       help='检查外部链接（较慢）')
    parser.add_argument('--workers', '-w', type=int, default=5,
                       help='并行检查的工作线程数')
    parser.add_argument('--output', '-o', type=Path,
                       help='输出报告文件')
    parser.add_argument('--format', '-f', type=str,
                       choices=['markdown', 'json', 'console'],
                       default='console',
                       help='报告格式')
    parser.add_argument('--fix', action='store_true',
                       help='自动修复损坏的链接')
    parser.add_argument('--backup', '-b', action='store_true',
                       help='修复前创建备份')
    parser.add_argument('--map', '-m', action='store_true',
                       help='生成链接地图')

    args = parser.parse_args()

    if not args.input.exists():
        print(f"错误: 输入目录不存在: {args.input}")
        return 1

    # 提取链接
    extractor = LinkExtractor(args.input)
    all_links = []
    checked_files = set()

    print("正在扫描Markdown文件...")
    for md_file in args.input.rglob('*.md'):
        links = extractor.extract_links(md_file)
        all_links.extend(links)
        checked_files.add(str(md_file.relative_to(args.input)))

    print(f"找到 {len(all_links)} 个链接，分布在 {len(checked_files)} 个文件中")

    # 验证链接
    print("正在验证链接...")
    validator = LinkValidator(args.input)

    for link in all_links:
        validator.validate_link(link)

    # 生成报告
    report = LinkReport(
        total_links=len(all_links),
        valid_links=sum(1 for l in all_links if l.status == LinkStatus.VALID),
        broken_links=sum(1 for l in all_links if l.status == LinkStatus.BROKEN),
        external_links=sum(1 for l in all_links if l.status == LinkStatus.EXTERNAL),
        warning_links=sum(1 for l in all_links if l.status == LinkStatus.WARNING),
        links=all_links,
        checked_files=checked_files
    )

    # 自动修复
    if args.fix:
        fixer = LinkFixer(args.input, args.backup)
        fixed_count = 0

        for link in all_links:
            if link.status == LinkStatus.BROKEN and link.suggestion:
                if fixer.fix_link(link):
                    fixed_count += 1

        print(f"已修复 {fixed_count} 个链接")

    # 生成报告
    generator = ReportGenerator(report, args.input)

    if args.format == 'markdown':
        output = generator.generate_markdown()
    elif args.format == 'json':
        output = generator.generate_json()
    else:
        # Console输出
        print(f"\n{'='*60}")
        print(f"链接检查报告")
        print('='*60)
        print(f"总链接: {report.total_links}")
        print(f"✅ 有效: {report.valid_links}")
        print(f"❌ 损坏: {report.broken_links}")
        print(f"🌐 外部: {report.external_links}")
        print(f"⚠️  警告: {report.warning_links}")
        print('='*60)

        if report.broken_links > 0:
            print("\n损坏的链接:")
            for link in all_links:
                if link.status == LinkStatus.BROKEN:
                    source = link.source_file.relative_to(args.input)
                    print(f"  {source}:{link.line_number} -> {link.url}")
                    if link.suggestion:
                        print(f"    建议: {link.suggestion}")

        output = None

    if output and args.output:
        with open(args.output, 'w', encoding='utf-8') as f:
            f.write(output)
        print(f"\n报告已保存: {args.output}")
    elif output:
        print(output)

    # 生成链接地图
    if args.map:
        map_gen = LinkMapGenerator(all_links, args.input)
        mermaid = map_gen.generate_mermaid()

        map_file = args.output or args.input / 'link-map.md'
        with open(map_file, 'w', encoding='utf-8') as f:
            f.write("# 文档链接地图\n\n")
            f.write(mermaid)

        print(f"链接地图已保存: {map_file}")

    # 返回错误码
    return 1 if report.broken_links > 0 else 0


if __name__ == '__main__':
    exit(main())
