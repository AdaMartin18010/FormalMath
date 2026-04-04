#!/usr/bin/env python3
"""
FormalMath 元数据管理 CLI 工具
整合提取、查询、版本控制和质量检查功能
"""

import os
import sys
import json
import argparse
from pathlib import Path
from typing import Optional

# 添加当前目录到路径
sys.path.insert(0, str(Path(__file__).parent))

from metadata_extractor import MetadataExtractor
from metadata_query import MetadataQuery
from version_control import VersionControl, MetadataVersionManager
from quality_control import QualityControl


class MetadataManager:
    """元数据管理器"""
    
    def __init__(self, root_dir: str = '.'):
        self.root_dir = Path(root_dir)
        self.data_file = self.root_dir / '.metadata_cache.json'
        
        # 初始化各组件
        self.extractor = MetadataExtractor(root_dir)
        self.query: Optional[MetadataQuery] = None
        self.version_control = VersionControl(root_dir)
        self.quality_control = QualityControl(root_dir)
        
        # 加载缓存数据
        self._load_cache()
    
    def _load_cache(self):
        """加载缓存的元数据"""
        if self.data_file.exists():
            try:
                self.query = MetadataQuery(str(self.data_file))
                print(f"已加载缓存: {self.data_file}")
            except Exception as e:
                print(f"加载缓存失败: {e}")
                self.query = None
    
    def _save_cache(self):
        """保存元数据到缓存"""
        if self.extractor.records:
            self.extractor.export_to_json(str(self.data_file))
            self.query = MetadataQuery(str(self.data_file))
    
    def scan(self, pattern: str = '**/*.md', exclude: list = None, stats: bool = True):
        """扫描文档并提取元数据"""
        print(f"\n{'='*60}")
        print("扫描文档并提取元数据")
        print('='*60)
        
        exclude = exclude or ['.git', 'node_modules', '__pycache__', '00-归档']
        
        print(f"扫描目录: {self.root_dir}")
        print(f"匹配模式: {pattern}")
        print(f"排除目录: {', '.join(exclude)}")
        print()
        
        records = self.extractor.scan_directory(pattern, exclude)
        print(f"找到 {len(records)} 个文档")
        
        # 保存缓存
        self._save_cache()
        
        # 显示统计
        if stats:
            self.extractor.print_statistics()
        
        # 显示错误
        if self.extractor.errors:
            print(f"\n警告: 处理过程中有 {len(self.extractor.errors)} 个错误")
            for err in self.extractor.errors[:5]:
                print(f"  - {err['file']}: {err['error']}")
            if len(self.extractor.errors) > 5:
                print(f"  ... 还有 {len(self.extractor.errors) - 5} 个错误")
    
    def query_docs(self, **kwargs):
        """查询文档"""
        if not self.query:
            print("错误: 请先执行 scan 命令构建元数据索引")
            return
        
        print(f"\n{'='*60}")
        print("查询文档")
        print('='*60)
        
        result = self.query.query(**kwargs)
        self.query.print_query_results(result)
    
    def search(self, keyword: str):
        """全文搜索"""
        if not self.query:
            print("错误: 请先执行 scan 命令构建元数据索引")
            return
        
        print(f"\n搜索关键词: '{keyword}'")
        print('='*60)
        
        results = self.query.search(keyword)
        print(f"找到 {len(results)} 个结果\n")
        
        for i, r in enumerate(results[:20], 1):
            print(f"{i}. {r.get('title', '无标题')}")
            print(f"   路径: {r.get('filepath', 'N/A')}")
            print(f"   分类: {r.get('category', 'N/A')} | MSC: {r.get('msc_primary', 'N/A')}")
            print()
    
    def check_quality(self, pattern: str = '**/*.md', output: str = None):
        """质量检查"""
        print(f"\n{'='*60}")
        print("质量检查")
        print('='*60)
        
        self.quality_control.scan_directory(pattern)
        self.quality_control.print_summary()
        
        if output:
            self.quality_control.generate_report(output)
    
    def check_file(self, filepath: str):
        """检查单个文件"""
        full_path = self.root_dir / filepath
        if not full_path.exists():
            print(f"错误: 文件不存在 {filepath}")
            return
        
        report = self.quality_control.check_file(full_path)
        
        print(f"\n{'='*60}")
        print(f"文件质量报告: {filepath}")
        print('='*60)
        print(f"标题: {report.title}")
        print(f"质量分: {report.overall_score}/100 ({report.level.value})")
        print()
        
        print("【检查项得分】")
        for name, result in report.checks.items():
            status = "✓" if result['score'] >= 80 else "⚠" if result['score'] >= 60 else "✗"
            print(f"  {status} {name:25s}: {result['score']:3d}/100")
        print()
        
        if report.suggestions:
            print("【改进建议】")
            for i, s in enumerate(report.suggestions, 1):
                print(f"  {i}. {s}")
            print()
        
        if report.errors:
            print("【错误】")
            for e in report.errors:
                print(f"  ✗ {e}")
            print()
        
        if report.warnings:
            print("【警告】")
            for w in report.warnings[:5]:
                print(f"  ⚠ {w}")
            if len(report.warnings) > 5:
                print(f"  ... 还有 {len(report.warnings) - 5} 个警告")
    
    def update_version(self, filepath: str, changes: str, level: str = 'patch'):
        """更新文档版本"""
        manager = MetadataVersionManager(self.root_dir)
        
        try:
            new_version = manager.update_document_version(filepath, changes, level)
            print(f"\n✓ 版本更新成功")
            print(f"  文件: {filepath}")
            print(f"  新版本: {new_version}")
        except Exception as e:
            print(f"\n✗ 版本更新失败: {e}")
    
    def version_history(self, filepath: str = None):
        """查看版本历史"""
        self.version_control.print_version_history(filepath)
    
    def export(self, format: str = 'json', output: str = None):
        """导出元数据"""
        if not self.extractor.records:
            print("错误: 没有可导出的数据，请先执行 scan 命令")
            return
        
        if format == 'json':
            output = output or 'metadata_export.json'
            self.extractor.export_to_json(output)
        elif format == 'csv':
            output = output or 'metadata_export.csv'
            self.extractor.export_to_csv(output)
        else:
            print(f"错误: 不支持的格式 {format}")
    
    def stats(self):
        """显示统计信息"""
        if not self.query:
            print("错误: 请先执行 scan 命令构建元数据索引")
            return
        
        stats = self.query.get_statistics()
        
        print(f"\n{'='*60}")
        print("FormalMath 文档统计")
        print('='*60)
        print(f"总文档数: {stats['total']}")
        print()
        
        if stats['by_category']:
            print("【按分类】")
            for cat, count in sorted(stats['by_category'].items(), key=lambda x: -x[1]):
                print(f"  {cat}: {count}")
            print()
        
        if stats['by_difficulty']:
            print("【按难度】")
            for diff in ['L0', 'L1', 'L2', 'L3', 'L4']:
                if diff in stats['by_difficulty']:
                    print(f"  {diff}: {stats['by_difficulty'][diff]}")
            print()
        
        if stats['by_status']:
            print("【按状态】")
            for status, count in sorted(stats['by_status'].items(), key=lambda x: -x[1]):
                print(f"  {status}: {count}")
            print()
        
        if stats['by_depth_level']:
            print("【按深度等级】")
            for level, count in sorted(stats['by_depth_level'].items(), key=lambda x: -x[1]):
                print(f"  {level}: {count}")
        
        print('='*60)


def main():
    """主函数"""
    parser = argparse.ArgumentParser(
        description='FormalMath 元数据管理 CLI',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  # 扫描所有文档
  %(prog)s scan

  # 查询代数结构类别的文档
  %(prog)s query --category "代数结构"

  # 搜索关键词
  %(prog)s search "群论"

  # 检查质量
  %(prog)s quality-check

  # 检查单个文件
  %(prog)s check-file docs/02-代数结构/群论.md

  # 更新版本
  %(prog)s version-update docs/02-代数结构/群论.md "添加新定理证明" --level minor
        """
    )
    
    parser.add_argument('-d', '--directory', default='.', help='项目根目录')
    
    subparsers = parser.add_subparsers(dest='command', help='可用命令')
    
    # scan 命令
    scan_parser = subparsers.add_parser('scan', help='扫描文档提取元数据')
    scan_parser.add_argument('-p', '--pattern', default='**/*.md', help='文件匹配模式')
    scan_parser.add_argument('--no-stats', action='store_true', help='不显示统计')
    
    # query 命令
    query_parser = subparsers.add_parser('query', help='查询文档')
    query_parser.add_argument('--category', help='内容分类')
    query_parser.add_argument('--difficulty', help='难度等级 (L0-L4)')
    query_parser.add_argument('--status', help='文档状态')
    query_parser.add_argument('--msc', help='MSC主分类')
    query_parser.add_argument('--has-proofs', type=bool, help='是否含证明')
    query_parser.add_argument('--has-examples', type=bool, help='是否含例子')
    query_parser.add_argument('--has-lean4', type=bool, help='是否含Lean4')
    query_parser.add_argument('--min-score', type=int, help='最低质量分')
    
    # search 命令
    search_parser = subparsers.add_parser('search', help='全文搜索')
    search_parser.add_argument('keyword', help='搜索关键词')
    
    # quality-check 命令
    quality_parser = subparsers.add_parser('quality-check', help='质量检查')
    quality_parser.add_argument('-p', '--pattern', default='**/*.md', help='文件匹配模式')
    quality_parser.add_argument('-o', '--output', help='输出报告文件')
    
    # check-file 命令
    check_file_parser = subparsers.add_parser('check-file', help='检查单个文件')
    check_file_parser.add_argument('filepath', help='文件路径')
    
    # version-update 命令
    version_parser = subparsers.add_parser('version-update', help='更新文档版本')
    version_parser.add_argument('filepath', help='文件路径')
    version_parser.add_argument('changes', help='变更描述')
    version_parser.add_argument('--level', default='patch', 
                                choices=['major', 'minor', 'patch'],
                                help='版本递增级别')
    
    # version-history 命令
    history_parser = subparsers.add_parser('version-history', help='查看版本历史')
    history_parser.add_argument('--file', help='指定文件路径')
    
    # export 命令
    export_parser = subparsers.add_parser('export', help='导出元数据')
    export_parser.add_argument('--format', default='json', choices=['json', 'csv'],
                               help='导出格式')
    export_parser.add_argument('-o', '--output', help='输出文件路径')
    
    # stats 命令
    subparsers.add_parser('stats', help='显示统计信息')
    
    args = parser.parse_args()
    
    if not args.command:
        parser.print_help()
        return
    
    # 创建管理器
    manager = MetadataManager(args.directory)
    
    # 执行命令
    if args.command == 'scan':
        manager.scan(args.pattern, stats=not args.no_stats)
    
    elif args.command == 'query':
        kwargs = {}
        if args.category:
            kwargs['category'] = args.category
        if args.difficulty:
            kwargs['difficulty'] = args.difficulty
        if args.status:
            kwargs['status'] = args.status
        if args.msc:
            kwargs['msc_primary'] = args.msc
        if args.has_proofs is not None:
            kwargs['has_proofs'] = args.has_proofs
        if args.has_examples is not None:
            kwargs['has_examples'] = args.has_examples
        if args.has_lean4 is not None:
            kwargs['has_lean4'] = args.has_lean4
        if args.min_score:
            kwargs['min_quality_score'] = args.min_score
        
        manager.query_docs(**kwargs)
    
    elif args.command == 'search':
        manager.search(args.keyword)
    
    elif args.command == 'quality-check':
        manager.check_quality(args.pattern, args.output)
    
    elif args.command == 'check-file':
        manager.check_file(args.filepath)
    
    elif args.command == 'version-update':
        manager.update_version(args.filepath, args.changes, args.level)
    
    elif args.command == 'version-history':
        manager.version_history(args.file)
    
    elif args.command == 'export':
        manager.export(args.format, args.output)
    
    elif args.command == 'stats':
        manager.stats()


if __name__ == '__main__':
    main()
