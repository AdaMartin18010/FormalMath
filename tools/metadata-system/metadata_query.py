#!/usr/bin/env python3
"""
FormalMath 元数据查询系统
提供强大的文档查询和检索功能
"""

import os
import json
import re
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Any, Callable
from dataclasses import dataclass
from functools import lru_cache


@dataclass
class QueryResult:
    """查询结果"""
    records: List[Dict]
    total: int
    page: int
    per_page: int
    query_time: float


class MetadataQuery:
    """元数据查询系统"""
    
    def __init__(self, data_source: str = None):
        """
        初始化查询系统
        
        Args:
            data_source: JSON文件路径或包含记录的字典
        """
        self.records: List[Dict] = []
        self.indexes: Dict[str, Dict] = {}
        
        if isinstance(data_source, str) and os.path.exists(data_source):
            self.load_from_json(data_source)
        elif isinstance(data_source, dict):
            self.records = data_source.get('records', [])
        elif isinstance(data_source, list):
            self.records = data_source
    
    def load_from_json(self, filepath: str):
        """从JSON文件加载数据"""
        with open(filepath, 'r', encoding='utf-8') as f:
            data = json.load(f)
            self.records = data.get('records', [])
        print(f"已加载 {len(self.records)} 条记录")
        self._build_indexes()
    
    def _build_indexes(self):
        """构建索引以加速查询"""
        # 分类索引
        self.indexes['category'] = {}
        self.indexes['difficulty'] = {}
        self.indexes['status'] = {}
        self.indexes['msc_primary'] = {}
        self.indexes['depth_level'] = {}
        self.indexes['has_proofs'] = {True: [], False: []}
        self.indexes['has_examples'] = {True: [], False: []}
        self.indexes['has_lean4'] = {True: [], False: []}
        
        for idx, record in enumerate(self.records):
            # 分类索引
            cat = record.get('category')
            if cat:
                self.indexes['category'].setdefault(cat, []).append(idx)
            
            # 难度索引
            diff = record.get('difficulty')
            if diff:
                self.indexes['difficulty'].setdefault(diff, []).append(idx)
            
            # 状态索引
            status = record.get('status')
            if status:
                self.indexes['status'].setdefault(status, []).append(idx)
            
            # MSC索引
            msc = record.get('msc_primary')
            if msc:
                self.indexes['msc_primary'].setdefault(msc, []).append(idx)
            
            # 深度等级索引
            depth = record.get('depth_level')
            if depth:
                self.indexes['depth_level'].setdefault(depth, []).append(idx)
            
            # 布尔字段索引
            self.indexes['has_proofs'][record.get('has_proofs', False)].append(idx)
            self.indexes['has_examples'][record.get('has_examples', False)].append(idx)
            self.indexes['has_lean4'][record.get('has_lean4', False)].append(idx)
        
        print("索引构建完成")
    
    def query(self, 
              category: str = None,
              difficulty: str = None,
              status: str = None,
              msc_primary: str = None,
              depth_level: str = None,
              has_proofs: bool = None,
              has_examples: bool = None,
              has_exercises: bool = None,
              has_lean4: bool = None,
              title_contains: str = None,
              filepath_pattern: str = None,
              min_quality_score: int = None,
              min_word_count: int = None,
              related_concepts: List[str] = None,
              custom_filter: Callable = None,
              sort_by: str = None,
              sort_desc: bool = True,
              page: int = 1,
              per_page: int = 50) -> QueryResult:
        """
        多条件组合查询
        
        Args:
            category: 内容分类
            difficulty: 难度等级 (L0-L4)
            status: 文档状态
            msc_primary: MSC主分类
            depth_level: 深度等级
            has_proofs: 是否包含证明
            has_examples: 是否包含例子
            has_exercises: 是否包含习题
            has_lean4: 是否含Lean4
            title_contains: 标题包含关键词
            filepath_pattern: 文件路径匹配模式
            min_quality_score: 最低质量分
            min_word_count: 最低字数
            related_concepts: 相关概念列表
            custom_filter: 自定义过滤函数
            sort_by: 排序字段
            sort_desc: 是否降序
            page: 页码
            per_page: 每页数量
        
        Returns:
            QueryResult: 查询结果
        """
        import time
        start_time = time.time()
        
        # 获取候选记录索引
        candidate_indices = set(range(len(self.records)))
        
        # 使用索引加速过滤
        if category and category in self.indexes['category']:
            candidate_indices &= set(self.indexes['category'][category])
        
        if difficulty and difficulty in self.indexes['difficulty']:
            candidate_indices &= set(self.indexes['difficulty'][difficulty])
        
        if status and status in self.indexes['status']:
            candidate_indices &= set(self.indexes['status'][status])
        
        if msc_primary and msc_primary in self.indexes['msc_primary']:
            candidate_indices &= set(self.indexes['msc_primary'][msc_primary])
        
        if depth_level and depth_level in self.indexes['depth_level']:
            candidate_indices &= set(self.indexes['depth_level'][depth_level])
        
        if has_proofs is not None:
            candidate_indices &= set(self.indexes['has_proofs'][has_proofs])
        
        if has_examples is not None:
            candidate_indices &= set(self.indexes['has_examples'][has_examples])
        
        if has_lean4 is not None:
            candidate_indices &= set(self.indexes['has_lean4'][has_lean4])
        
        # 应用其他过滤条件
        results = []
        for idx in candidate_indices:
            record = self.records[idx]
            
            # 标题过滤
            if title_contains:
                title = record.get('title', '') or ''
                if title_contains.lower() not in title.lower():
                    continue
            
            # 文件路径过滤
            if filepath_pattern:
                filepath = record.get('filepath', '')
                if not re.search(filepath_pattern, filepath, re.IGNORECASE):
                    continue
            
            # 质量分过滤
            if min_quality_score is not None:
                score = record.get('quality_score') or 0
                if score < min_quality_score:
                    continue
            
            # 字数过滤
            if min_word_count is not None:
                count = record.get('word_count') or 0
                if count < min_word_count:
                    continue
            
            # 习题过滤
            if has_exercises is not None:
                if record.get('has_exercises') != has_exercises:
                    continue
            
            # 相关概念过滤
            if related_concepts:
                record_concepts = record.get('related_concepts', []) or []
                if not any(c in record_concepts for c in related_concepts):
                    continue
            
            # 自定义过滤
            if custom_filter and not custom_filter(record):
                continue
            
            results.append(record)
        
        # 排序
        if sort_by:
            results.sort(key=lambda x: (x.get(sort_by) is None, x.get(sort_by, '')), 
                        reverse=sort_desc)
        
        # 分页
        total = len(results)
        start = (page - 1) * per_page
        end = start + per_page
        paged_results = results[start:end]
        
        query_time = time.time() - start_time
        
        return QueryResult(
            records=paged_results,
            total=total,
            page=page,
            per_page=per_page,
            query_time=query_time
        )
    
    def search(self, keyword: str, fields: List[str] = None) -> List[Dict]:
        """
        全文搜索
        
        Args:
            keyword: 搜索关键词
            fields: 搜索字段列表，默认搜索所有文本字段
        
        Returns:
            匹配的记录列表
        """
        if not fields:
            fields = ['title', 'filepath', 'category', 'related_concepts', 'prerequisites']
        
        keyword_lower = keyword.lower()
        results = []
        
        for record in self.records:
            score = 0
            for field in fields:
                value = record.get(field)
                if not value:
                    continue
                
                if isinstance(value, str):
                    if keyword_lower in value.lower():
                        score += 1
                elif isinstance(value, list):
                    if any(keyword_lower in str(v).lower() for v in value):
                        score += 1
            
            if score > 0:
                results.append((score, record))
        
        # 按相关度排序
        results.sort(key=lambda x: -x[0])
        return [r[1] for r in results]
    
    def find_by_concept(self, concept: str) -> List[Dict]:
        """根据概念查找相关文档"""
        results = []
        for record in self.records:
            concepts = record.get('related_concepts', []) or []
            if concept in concepts:
                results.append(record)
        return results
    
    def find_by_mathematician(self, mathematician: str) -> List[Dict]:
        """根据数学家查找相关文档"""
        results = []
        for record in self.records:
            mathematicians = record.get('related_mathematicians', []) or []
            if mathematician in mathematicians:
                results.append(record)
        return results
    
    def find_by_course(self, course: str) -> List[Dict]:
        """根据课程查找相关文档"""
        results = []
        for record in self.records:
            courses = record.get('courses_mapped', []) or []
            if any(course.lower() in c.lower() for c in courses):
                results.append(record)
        return results
    
    def get_learning_path(self, start_concept: str, end_concept: str) -> List[Dict]:
        """
        获取学习路径
        
        基于前置知识和后续主题构建学习路径
        """
        # 找到起始概念和结束概念的文档
        start_docs = self.find_by_concept(start_concept)
        end_docs = self.find_by_concept(end_concept)
        
        if not start_docs or not end_docs:
            return []
        
        # 简化的路径查找（基于难度递进）
        path = []
        current_difficulty = start_docs[0].get('difficulty', 'L1')
        target_difficulty = end_docs[0].get('difficulty', 'L4')
        
        difficulty_order = ['L0', 'L1', 'L2', 'L3', 'L4']
        
        start_idx = difficulty_order.index(current_difficulty) if current_difficulty in difficulty_order else 1
        end_idx = difficulty_order.index(target_difficulty) if target_difficulty in difficulty_order else 4
        
        for diff in difficulty_order[start_idx:end_idx+1]:
            docs = self.query(difficulty=diff, has_proofs=True, sort_by='quality_score', per_page=3).records
            path.extend(docs)
        
        return path
    
    def get_statistics(self) -> Dict:
        """获取统计信息"""
        stats = {
            'total': len(self.records),
            'by_category': {},
            'by_difficulty': {},
            'by_status': {},
            'by_msc_primary': {},
            'by_depth_level': {},
        }
        
        for record in self.records:
            for key in ['category', 'difficulty', 'status', 'msc_primary', 'depth_level']:
                value = record.get(key)
                if value:
                    stats[f'by_{key}'][value] = stats[f'by_{key}'].get(value, 0) + 1
        
        return stats
    
    def print_query_results(self, result: QueryResult, max_display: int = 10):
        """打印查询结果"""
        print(f"\n查询结果: {result.total} 条记录 (第 {result.page} 页, 耗时 {result.query_time:.3f}s)")
        print("-" * 80)
        
        for i, record in enumerate(result.records[:max_display], 1):
            print(f"{i}. {record.get('title', '无标题')}")
            print(f"   路径: {record.get('filepath', 'N/A')}")
            print(f"   分类: {record.get('category', 'N/A')} | 难度: {record.get('difficulty', 'N/A')} | MSC: {record.get('msc_primary', 'N/A')}")
            if record.get('word_count'):
                print(f"   字数: {record['word_count']:,}")
            print()
        
        if result.total > max_display:
            print(f"... 还有 {result.total - max_display} 条记录 ...")
        
        print("-" * 80)


def interactive_query():
    """交互式查询界面"""
    import argparse
    
    parser = argparse.ArgumentParser(description='FormalMath 元数据查询系统')
    parser.add_argument('-d', '--data', required=True, help='元数据JSON文件路径')
    parser.add_argument('--interactive', action='store_true', help='进入交互模式')
    
    args = parser.parse_args()
    
    # 初始化查询系统
    query_system = MetadataQuery(args.data)
    
    if not args.interactive:
        # 显示统计信息
        stats = query_system.get_statistics()
        print("\n" + "="*60)
        print("FormalMath 文档统计")
        print("="*60)
        print(f"总文档数: {stats['total']}")
        
        if stats['by_category']:
            print("\n【按分类】")
            for cat, count in sorted(stats['by_category'].items(), key=lambda x: -x[1])[:10]:
                print(f"  {cat}: {count}")
        
        if stats['by_difficulty']:
            print("\n【按难度】")
            for diff in ['L0', 'L1', 'L2', 'L3', 'L4']:
                if diff in stats['by_difficulty']:
                    print(f"  {diff}: {stats['by_difficulty'][diff]}")
        
        print("="*60)
        return
    
    # 交互模式
    print("\n" + "="*60)
    print("FormalMath 元数据查询系统 - 交互模式")
    print("="*60)
    print("命令:")
    print("  search <关键词>    - 全文搜索")
    print("  category <分类>    - 按分类查询")
    print("  difficulty <等级>  - 按难度查询 (L0-L4)")
    print("  concept <概念>     - 查找相关概念文档")
    print("  course <课程>      - 查找课程相关文档")
    print("  stats              - 显示统计信息")
    print("  help               - 显示帮助")
    print("  quit               - 退出")
    print("="*60)
    
    while True:
        try:
            cmd = input("\n> ").strip()
            if not cmd:
                continue
            
            parts = cmd.split(maxsplit=1)
            action = parts[0].lower()
            arg = parts[1] if len(parts) > 1 else ""
            
            if action == 'quit' or action == 'exit':
                break
            
            elif action == 'help':
                print("可用命令: search, category, difficulty, concept, course, stats, help, quit")
            
            elif action == 'stats':
                stats = query_system.get_statistics()
                print(f"\n总文档数: {stats['total']}")
            
            elif action == 'search' and arg:
                results = query_system.search(arg)
                print(f"\n找到 {len(results)} 个结果 (显示前10个):")
                for i, r in enumerate(results[:10], 1):
                    print(f"{i}. {r.get('title', '无标题')} - {r.get('filepath', 'N/A')}")
            
            elif action == 'category' and arg:
                result = query_system.query(category=arg, per_page=10)
                query_system.print_query_results(result)
            
            elif action == 'difficulty' and arg:
                result = query_system.query(difficulty=arg.upper(), per_page=10)
                query_system.print_query_results(result)
            
            elif action == 'concept' and arg:
                results = query_system.find_by_concept(arg)
                print(f"\n找到 {len(results)} 个相关文档:")
                for i, r in enumerate(results[:10], 1):
                    print(f"{i}. {r.get('title', '无标题')} - {r.get('filepath', 'N/A')}")
            
            elif action == 'course' and arg:
                results = query_system.find_by_course(arg)
                print(f"\n找到 {len(results)} 个相关文档:")
                for i, r in enumerate(results[:10], 1):
                    print(f"{i}. {r.get('title', '无标题')} - {r.get('filepath', 'N/A')}")
            
            else:
                print(f"未知命令: {action}")
        
        except KeyboardInterrupt:
            break
        except Exception as e:
            print(f"错误: {e}")
    
    print("\n再见!")


if __name__ == '__main__':
    interactive_query()
