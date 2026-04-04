#!/usr/bin/env python3
"""
FormalMath 元数据提取工具
用于从 Markdown 文档中提取和管理元数据
"""

import os
import re
import json
import yaml
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, asdict
from collections import defaultdict


@dataclass
class MetadataRecord:
    """元数据记录类"""
    filepath: str
    filename: str
    title: Optional[str] = None
    created_date: Optional[str] = None
    version: Optional[str] = None
    msc_primary: Optional[str] = None
    msc_secondary: Optional[List[str]] = None
    category: Optional[str] = None
    difficulty: Optional[str] = None
    depth_level: Optional[str] = None
    author: Optional[str] = None
    status: Optional[str] = None
    quality_score: Optional[int] = None
    completeness: Optional[str] = None
    word_count: Optional[int] = None
    has_proofs: Optional[bool] = None
    has_examples: Optional[bool] = None
    has_exercises: Optional[bool] = None
    has_lean4: Optional[bool] = None
    last_modified: Optional[str] = None
    related_concepts: Optional[List[str]] = None
    prerequisites: Optional[List[str]] = None
    raw_metadata: Optional[Dict] = None
    validation_errors: List[str] = None
    
    def __post_init__(self):
        if self.validation_errors is None:
            self.validation_errors = []


class MetadataExtractor:
    """元数据提取器"""
    
    # YAML Front Matter 正则表达式
    YAML_PATTERN = re.compile(r'^---\s*\n(.*?)\n---\s*\n', re.DOTALL)
    
    # 深度等级后缀映射
    DEPTH_SUFFIXES = {
        '-基础版.md': '基础版',
        '-增强版.md': '增强版',
        '-深度扩展版.md': '深度扩展版',
        '-国际标准版.md': '国际标准版',
    }
    
    def __init__(self, root_dir: str = '.'):
        self.root_dir = Path(root_dir)
        self.records: List[MetadataRecord] = []
        self.errors: List[Dict] = []
    
    def extract_from_file(self, filepath: Path) -> Optional[MetadataRecord]:
        """从单个文件提取元数据"""
        try:
            content = filepath.read_text(encoding='utf-8')
            
            # 提取 YAML Front Matter
            yaml_match = self.YAML_PATTERN.match(content)
            metadata = {}
            
            if yaml_match:
                try:
                    metadata = yaml.safe_load(yaml_match.group(1)) or {}
                except yaml.YAMLError as e:
                    self.errors.append({
                        'file': str(filepath),
                        'error': f'YAML解析错误: {e}'
                    })
                    metadata = {}
            
            # 创建记录
            record = MetadataRecord(
                filepath=str(filepath.relative_to(self.root_dir)),
                filename=filepath.name,
                raw_metadata=metadata
            )
            
            # 填充标准字段
            self._fill_standard_fields(record, metadata, content)
            
            # 自动检测字段
            self._auto_detect_fields(record, content)
            
            # 验证记录
            self._validate_record(record)
            
            return record
            
        except Exception as e:
            self.errors.append({
                'file': str(filepath),
                'error': f'文件读取错误: {e}'
            })
            return None
    
    def _fill_standard_fields(self, record: MetadataRecord, metadata: Dict, content: str):
        """填充标准字段"""
        record.title = metadata.get('title') or self._extract_title(content)
        record.created_date = metadata.get('created_date')
        record.version = metadata.get('version')
        record.msc_primary = metadata.get('msc_primary')
        record.msc_secondary = metadata.get('msc_secondary', [])
        record.category = metadata.get('category')
        record.difficulty = metadata.get('difficulty')
        record.depth_level = metadata.get('depth_level') or self._detect_depth_level(filepath=record.filepath)
        record.author = metadata.get('author')
        record.status = metadata.get('status', 'draft')
        record.quality_score = metadata.get('quality_score')
        record.completeness = metadata.get('completeness')
        record.last_modified = metadata.get('last_modified')
        record.related_concepts = metadata.get('related_concepts', [])
        record.prerequisites = metadata.get('prerequisites', [])
        
        # 布尔字段
        record.has_proofs = metadata.get('has_proofs')
        record.has_examples = metadata.get('has_examples')
        record.has_exercises = metadata.get('has_exercises')
        record.has_lean4 = metadata.get('has_lean4')
    
    def _extract_title(self, content: str) -> Optional[str]:
        """从内容中提取标题"""
        # 查找第一个 # 标题
        title_match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
        if title_match:
            return title_match.group(1).strip()
        return None
    
    def _detect_depth_level(self, filepath: str) -> Optional[str]:
        """根据文件名检测深度等级"""
        for suffix, level in self.DEPTH_SUFFIXES.items():
            if suffix in filepath:
                return level
        return None
    
    def _auto_detect_fields(self, record: MetadataRecord, content: str):
        """自动检测字段"""
        # 字数统计 (去除 Markdown 标记)
        clean_content = re.sub(r'```[\s\S]*?```', '', content)  # 移除代码块
        clean_content = re.sub(r'!\[.*?\]\(.*?\)', '', clean_content)  # 移除图片
        clean_content = re.sub(r'\[.*?\]\(.*?\)', '', clean_content)  # 移除链接
        clean_content = re.sub(r'[#*_`]', '', clean_content)  # 移除格式标记
        word_count = len(clean_content.replace('\n', '').replace(' ', ''))
        record.word_count = word_count
        
        # 自动检测证明
        if record.has_proofs is None:
            proof_patterns = [
                r'#{1,3}\s*证明',
                r'\*\*证明\*\*',
                r'#{1,3}\s*Proof',
                r'Proof\.\s*',
            ]
            record.has_proofs = any(re.search(p, content, re.IGNORECASE) for p in proof_patterns)
        
        # 自动检测例子
        if record.has_examples is None:
            example_patterns = [
                r'#{1,3}\s*例[子题]?',
                r'#{1,3}\s*Example',
                r'\*\*例[子题]?\*\*',
            ]
            record.has_examples = any(re.search(p, content, re.IGNORECASE) for p in example_patterns)
        
        # 自动检测习题
        if record.has_exercises is None:
            exercise_patterns = [
                r'#{1,3}\s*习题',
                r'#{1,3}\s*Exercise',
                r'#{1,3}\s*Problem',
            ]
            record.has_exercises = any(re.search(p, content, re.IGNORECASE) for p in exercise_patterns)
        
        # 自动检测 Lean4
        if record.has_lean4 is None:
            lean_patterns = [
                r'```lean4?',
                r'theorem\s+\w+',
                r'lemma\s+\w+',
                r'import\s+Mathlib',
            ]
            record.has_lean4 = any(re.search(p, content) for p in lean_patterns)
    
    def _validate_record(self, record: MetadataRecord):
        """验证记录"""
        errors = []
        
        # 必需字段
        if not record.title:
            errors.append('缺少标题 (title)')
        if not record.created_date:
            errors.append('缺少创建日期 (created_date)')
        if not record.version:
            errors.append('缺少版本号 (version)')
        
        # 日期格式验证
        if record.created_date:
            try:
                datetime.strptime(record.created_date, '%Y-%m-%d')
            except ValueError:
                errors.append(f'创建日期格式错误: {record.created_date}')
        
        # 版本号格式验证
        if record.version:
            if not re.match(r'^\d+\.\d+\.\d+$', record.version):
                errors.append(f'版本号格式错误: {record.version}')
        
        # 难度等级验证
        if record.difficulty and record.difficulty not in ['L0', 'L1', 'L2', 'L3', 'L4']:
            errors.append(f'难度等级错误: {record.difficulty}')
        
        # 状态验证
        if record.status and record.status not in ['draft', 'review', 'published', 'deprecated', 'archived']:
            errors.append(f'状态值错误: {record.status}')
        
        record.validation_errors = errors
    
    def scan_directory(self, pattern: str = '**/*.md', exclude_dirs: List[str] = None) -> List[MetadataRecord]:
        """扫描目录提取元数据"""
        exclude_dirs = exclude_dirs or ['.git', 'node_modules', '__pycache__', '00-归档']
        
        self.records = []
        md_files = list(self.root_dir.glob(pattern))
        
        for filepath in md_files:
            # 检查是否在排除目录中
            if any(excl in str(filepath) for excl in exclude_dirs):
                continue
            
            record = self.extract_from_file(filepath)
            if record:
                self.records.append(record)
        
        return self.records
    
    def export_to_json(self, output_path: str):
        """导出到 JSON"""
        data = {
            'exported_at': datetime.now().isoformat(),
            'total_records': len(self.records),
            'total_errors': len(self.errors),
            'records': [asdict(r) for r in self.records],
            'errors': self.errors
        }
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        
        print(f"已导出 {len(self.records)} 条记录到 {output_path}")
    
    def export_to_csv(self, output_path: str):
        """导出到 CSV"""
        import csv
        
        if not self.records:
            print("没有记录可导出")
            return
        
        # 定义CSV字段
        fields = [
            'filepath', 'filename', 'title', 'created_date', 'version',
            'msc_primary', 'category', 'difficulty', 'depth_level',
            'status', 'quality_score', 'word_count', 'has_proofs',
            'has_examples', 'has_exercises', 'has_lean4'
        ]
        
        with open(output_path, 'w', newline='', encoding='utf-8-sig') as f:
            writer = csv.DictWriter(f, fieldnames=fields)
            writer.writeheader()
            
            for record in self.records:
                row = {field: getattr(record, field, '') for field in fields}
                writer.writerow(row)
        
        print(f"已导出 {len(self.records)} 条记录到 {output_path}")
    
    def get_statistics(self) -> Dict:
        """获取统计信息"""
        stats = {
            'total_documents': len(self.records),
            'by_category': defaultdict(int),
            'by_difficulty': defaultdict(int),
            'by_depth_level': defaultdict(int),
            'by_status': defaultdict(int),
            'by_msc': defaultdict(int),
            'with_proofs': 0,
            'with_examples': 0,
            'with_exercises': 0,
            'with_lean4': 0,
            'total_word_count': 0,
            'validation_errors': len([r for r in self.records if r.validation_errors]),
        }
        
        for record in self.records:
            if record.category:
                stats['by_category'][record.category] += 1
            if record.difficulty:
                stats['by_difficulty'][record.difficulty] += 1
            if record.depth_level:
                stats['by_depth_level'][record.depth_level] += 1
            if record.status:
                stats['by_status'][record.status] += 1
            if record.msc_primary:
                stats['by_msc'][record.msc_primary] += 1
            
            if record.has_proofs:
                stats['with_proofs'] += 1
            if record.has_examples:
                stats['with_examples'] += 1
            if record.has_exercises:
                stats['with_exercises'] += 1
            if record.has_lean4:
                stats['with_lean4'] += 1
            
            if record.word_count:
                stats['total_word_count'] += record.word_count
        
        # 转换为普通dict
        stats['by_category'] = dict(stats['by_category'])
        stats['by_difficulty'] = dict(stats['by_difficulty'])
        stats['by_depth_level'] = dict(stats['by_depth_level'])
        stats['by_status'] = dict(stats['by_status'])
        stats['by_msc'] = dict(stats['by_msc'])
        
        return stats
    
    def print_statistics(self):
        """打印统计信息"""
        stats = self.get_statistics()
        
        print("\n" + "="*60)
        print("FormalMath 元数据统计报告")
        print("="*60)
        print(f"总文档数: {stats['total_documents']}")
        print(f"总字数: {stats['total_word_count']:,}")
        print(f"验证错误: {stats['validation_errors']}")
        print()
        
        print("【内容特征】")
        print(f"  含证明: {stats['with_proofs']} ({stats['with_proofs']/max(stats['total_documents'],1)*100:.1f}%)")
        print(f"  含例子: {stats['with_examples']} ({stats['with_examples']/max(stats['total_documents'],1)*100:.1f}%)")
        print(f"  含习题: {stats['with_exercises']} ({stats['with_exercises']/max(stats['total_documents'],1)*100:.1f}%)")
        print(f"  含Lean4: {stats['with_lean4']} ({stats['with_lean4']/max(stats['total_documents'],1)*100:.1f}%)")
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
        
        print("="*60)


def main():
    """主函数"""
    import argparse
    
    parser = argparse.ArgumentParser(description='FormalMath 元数据提取工具')
    parser.add_argument('-d', '--directory', default='.', help='扫描目录')
    parser.add_argument('-p', '--pattern', default='**/*.md', help='文件匹配模式')
    parser.add_argument('-o', '--output', help='输出JSON文件路径')
    parser.add_argument('-c', '--csv', help='输出CSV文件路径')
    parser.add_argument('-s', '--stats', action='store_true', help='显示统计信息')
    parser.add_argument('--exclude', nargs='+', default=['.git', 'node_modules', '__pycache__', '00-归档'],
                        help='排除的目录')
    
    args = parser.parse_args()
    
    # 创建提取器
    extractor = MetadataExtractor(args.directory)
    
    # 扫描目录
    print(f"正在扫描 {args.directory} ...")
    records = extractor.scan_directory(args.pattern, args.exclude)
    print(f"找到 {len(records)} 个文档")
    
    # 显示统计
    if args.stats:
        extractor.print_statistics()
    
    # 导出JSON
    if args.output:
        extractor.export_to_json(args.output)
    
    # 导出CSV
    if args.csv:
        extractor.export_to_csv(args.csv)
    
    # 显示错误
    if extractor.errors:
        print(f"\n警告: 处理过程中有 {len(extractor.errors)} 个错误")


if __name__ == '__main__':
    main()
