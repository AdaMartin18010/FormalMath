#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
定理搜索工具 (Theorem Search)

功能:
- 搜索Mathlib4注释
- 支持关键词、领域、难度筛选
- 输出搜索结果表格

使用示例:
    python theorem_search.py --keyword "prime number" --domain number_theory
    python theorem_search.py --difficulty hard --format json --output results.json
    python theorem_search.py --author "Paul Erdős" --domain combinatorics

作者: FormalMath-Enhanced
版本: 1.0.0
"""

import argparse
import re
import json
import csv
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass, asdict
from enum import Enum


class DifficultyLevel(Enum):
    """难度等级"""
    BEGINNER = "beginner"
    INTERMEDIATE = "intermediate"
    ADVANCED = "advanced"
    HARD = "hard"
    EXPERT = "expert"


@dataclass
class Theorem:
    """定理数据结构"""
    name: str
    statement: str
    proof: Optional[str]
    file_path: str
    line_number: int
    domain: str
    difficulty: str
    author: Optional[str]
    references: List[str]
    tags: List[str]
    lean_code: Optional[str]


class MathlibParser:
    """Mathlib注释解析器"""
    
    # 注释标签模式
    DOC_PATTERN = re.compile(
        r'/-\s*\n'
        r'(.*?)'
        r'-\s*/',
        re.DOTALL
    )
    
    THEOREM_PATTERN = re.compile(
        r'(?:theorem|lemma|def|structure|class)\s+'
        r'([a-zA-Z_][a-zA-Z0-9_]*)'
        r'\s*[^;]*?:=',
        re.DOTALL
    )
    
    # 元数据标签
    TAG_PATTERNS = {
        'author': re.compile(r'@author\s+(.+?)(?:\n|$)', re.IGNORECASE),
        'domain': re.compile(r'@domain\s+(.+?)(?:\n|$)', re.IGNORECASE),
        'difficulty': re.compile(r'@difficulty\s+(\w+)(?:\n|$)', re.IGNORECASE),
        'reference': re.compile(r'@see\s+(.+?)(?:\n|$)', re.IGNORECASE),
        'tag': re.compile(r'#(\w+)', re.IGNORECASE),
    }
    
    def __init__(self, mathlib_path: Optional[Path] = None):
        self.mathlib_path = mathlib_path or Path(".")
        self.theorems: List[Theorem] = []
    
    def parse_file(self, file_path: Path) -> List[Theorem]:
        """
        解析单个Lean文件
        
        Args:
            file_path: Lean文件路径
            
        Returns:
            定理列表
        """
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                lines = content.split('\n')
        except Exception as e:
            print(f"警告: 无法读取文件 {file_path}: {e}")
            return []
        
        theorems = []
        
        # 查找所有文档注释
        for match in self.DOC_PATTERN.finditer(content):
            doc_start = match.start()
            doc_content = match.group(1)
            line_number = content[:doc_start].count('\n') + 1
            
            # 查找注释后的定理定义
            after_doc = content[doc_start + len(match.group(0)):]
            theorem_match = self.THEOREM_PATTERN.search(after_doc)
            
            if theorem_match:
                theorem_name = theorem_match.group(1)
                
                # 提取定理声明
                stmt_match = re.search(
                    rf'{theorem_name}\s*[:\{].*?(?::=|\n\n)',
                    after_doc,
                    re.DOTALL
                )
                statement = stmt_match.group(0) if stmt_match else ""
                
                # 提取证明
                proof_start = after_doc.find(theorem_match.group(0)) + len(theorem_match.group(0))
                proof_match = re.search(r'by\s+(.+?)(?:\n\n|$)', after_doc[proof_start:], re.DOTALL)
                proof = proof_match.group(1) if proof_match else None
                
                # 提取元数据
                author = self._extract_tag(doc_content, 'author')
                domain = self._extract_tag(doc_content, 'domain') or self._infer_domain(file_path)
                difficulty = self._extract_tag(doc_content, 'difficulty') or "unknown"
                
                references = []
                for ref_match in self.TAG_PATTERNS['reference'].finditer(doc_content):
                    references.append(ref_match.group(1).strip())
                
                tags = []
                for tag_match in self.TAG_PATTERNS['tag'].finditer(doc_content):
                    tags.append(tag_match.group(1))
                
                # 提取Lean代码
                lean_code = None
                if theorem_match:
                    code_start = doc_start + len(match.group(0))
                    code_end = proof_start + len(proof) if proof else code_start + 500
                    lean_code = after_doc[:min(code_end - proof_start, 1000)]
                
                theorem = Theorem(
                    name=theorem_name,
                    statement=statement.strip()[:500],
                    proof=proof.strip()[:1000] if proof else None,
                    file_path=str(file_path.relative_to(self.mathlib_path)),
                    line_number=line_number,
                    domain=domain,
                    difficulty=difficulty.lower(),
                    author=author,
                    references=references,
                    tags=tags,
                    lean_code=lean_code
                )
                
                theorems.append(theorem)
        
        return theorems
    
    def _extract_tag(self, content: str, tag: str) -> Optional[str]:
        """提取标签值"""
        pattern = self.TAG_PATTERNS.get(tag)
        if pattern:
            match = pattern.search(content)
            return match.group(1).strip() if match else None
        return None
    
    def _infer_domain(self, file_path: Path) -> str:
        """从文件路径推断数学领域"""
        path_str = str(file_path).lower()
        
        domain_mapping = {
            'algebra': 'algebra',
            'analysis': 'analysis',
            'number_theory': 'number_theory',
            'topology': 'topology',
            'geometry': 'geometry',
            'combinatorics': 'combinatorics',
            'probability': 'probability',
            'logic': 'logic',
            'set': 'set_theory',
            'category': 'category_theory',
            'group': 'group_theory',
            'ring': 'ring_theory',
            'field': 'field_theory',
            'linear': 'linear_algebra',
            'matrix': 'linear_algebra',
            'calculus': 'calculus',
            'measure': 'measure_theory',
            'complex': 'complex_analysis',
        }
        
        for key, domain in domain_mapping.items():
            if key in path_str:
                return domain
        
        return "unknown"
    
    def build_index(self, directories: List[Path]) -> None:
        """
        构建定理索引
        
        Args:
            directories: 要扫描的目录列表
        """
        for directory in directories:
            if not directory.exists():
                continue
            
            for lean_file in directory.rglob('*.lean'):
                theorems = self.parse_file(lean_file)
                self.theorems.extend(theorems)
        
        print(f"已索引 {len(self.theorems)} 个定理")
    
    def search(self, 
               keyword: Optional[str] = None,
               domain: Optional[str] = None,
               difficulty: Optional[str] = None,
               author: Optional[str] = None,
               tags: Optional[List[str]] = None,
               limit: int = 50) -> List[Theorem]:
        """
        搜索定理
        
        Args:
            keyword: 关键词
            domain: 领域
            difficulty: 难度
            author: 作者
            tags: 标签列表
            limit: 结果限制
            
        Returns:
            匹配的定理列表
        """
        results = []
        
        for theorem in self.theorems:
            score = 0
            
            # 关键词匹配
            if keyword:
                keyword_lower = keyword.lower()
                if keyword_lower in theorem.name.lower():
                    score += 10
                if keyword_lower in theorem.statement.lower():
                    score += 5
                if theorem.proof and keyword_lower in theorem.proof.lower():
                    score += 3
                for tag in theorem.tags:
                    if keyword_lower in tag.lower():
                        score += 8
            else:
                score = 1
            
            # 领域筛选
            if domain and theorem.domain != domain.lower():
                continue
            
            # 难度筛选
            if difficulty and theorem.difficulty != difficulty.lower():
                continue
            
            # 作者筛选
            if author and (not theorem.author or author.lower() not in theorem.author.lower()):
                continue
            
            # 标签筛选
            if tags:
                theorem_tags_lower = [t.lower() for t in theorem.tags]
                if not any(tag.lower() in theorem_tags_lower for tag in tags):
                    continue
            
            if score > 0:
                results.append((score, theorem))
        
        # 按分数排序并限制结果
        results.sort(key=lambda x: x[0], reverse=True)
        return [t for _, t in results[:limit]]


class OutputFormatter:
    """输出格式化器"""
    
    @staticmethod
    def format_markdown(theorems: List[Theorem]) -> str:
        """格式化为Markdown表格"""
        output = "# 定理搜索结果\n\n"
        output += f"找到 {len(theorems)} 个定理\n\n"
        output += "| 名称 | 领域 | 难度 | 作者 | 文件 |\n"
        output += "|------|------|------|------|------|\n"
        
        for t in theorems:
            author = t.author or "N/A"
            output += f"| `{t.name}` | {t.domain} | {t.difficulty} | {author} | `{t.file_path}:{t.line_number}` |\n"
        
        return output
    
    @staticmethod
    def format_json(theorems: List[Theorem]) -> str:
        """格式化为JSON"""
        return json.dumps([asdict(t) for t in theorems], indent=2, ensure_ascii=False)
    
    @staticmethod
    def format_csv(theorems: List[Theorem]) -> str:
        """格式化为CSV"""
        import io
        output = io.StringIO()
        writer = csv.writer(output)
        
        writer.writerow(['Name', 'Domain', 'Difficulty', 'Author', 'File', 'Line', 'Statement', 'Tags'])
        
        for t in theorems:
            writer.writerow([
                t.name,
                t.domain,
                t.difficulty,
                t.author or '',
                t.file_path,
                t.line_number,
                t.statement[:200],
                ', '.join(t.tags)
            ])
        
        return output.getvalue()
    
    @staticmethod
    def format_console(theorems: List[Theorem]) -> str:
        """格式化为控制台输出"""
        lines = []
        lines.append(f"\n{'='*80}")
        lines.append(f"搜索结果: {len(theorems)} 个定理")
        lines.append('='*80)
        
        for i, t in enumerate(theorems, 1):
            lines.append(f"\n[{i}] {t.name}")
            lines.append(f"    领域: {t.domain}")
            lines.append(f"    难度: {t.difficulty}")
            if t.author:
                lines.append(f"    作者: {t.author}")
            lines.append(f"    位置: {t.file_path}:{t.line_number}")
            if t.tags:
                lines.append(f"    标签: {', '.join(t.tags)}")
            if t.statement:
                stmt = t.statement.replace('\n', ' ')[:100]
                lines.append(f"    声明: {stmt}...")
            lines.append('-'*80)
        
        return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="定理搜索工具 - 搜索Mathlib4中的定理",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
使用示例:
  %(prog)s --keyword "prime" --domain number_theory
  %(prog)s --difficulty hard --format json -o results.json
  %(prog)s --author "Erdos" --tags algebra topology
  %(prog)s --mathlib ~/mathlib4/Mathlib --keyword "compact"
        """
    )
    
    parser.add_argument('--mathlib', '-m', type=Path,
                       help='Mathlib4目录路径')
    parser.add_argument('--keyword', '-k', type=str,
                       help='搜索关键词')
    parser.add_argument('--domain', '-d', type=str,
                       help='数学领域筛选')
    parser.add_argument('--difficulty', '-D', type=str,
                       choices=['beginner', 'intermediate', 'advanced', 'hard', 'expert'],
                       help='难度等级筛选')
    parser.add_argument('--author', '-a', type=str,
                       help='作者筛选')
    parser.add_argument('--tags', '-t', nargs='+',
                       help='标签筛选（多个标签）')
    parser.add_argument('--limit', '-l', type=int, default=50,
                       help='结果数量限制（默认: 50）')
    parser.add_argument('--format', '-f', type=str,
                       choices=['console', 'markdown', 'json', 'csv'],
                       default='console',
                       help='输出格式')
    parser.add_argument('--output', '-o', type=Path,
                       help='输出文件路径')
    parser.add_argument('--reindex', '-r', action='store_true',
                       help='重新构建索引')
    
    args = parser.parse_args()
    
    # 如果没有搜索条件，显示帮助
    if not any([args.keyword, args.domain, args.difficulty, args.author, args.tags]):
        parser.print_help()
        return 0
    
    # 初始化解析器
    mathlib_path = args.mathlib or Path('.')
    parser_obj = MathlibParser(mathlib_path)
    
    # 构建索引
    index_file = Path('.theorem_index.json')
    
    if args.reindex or not index_file.exists():
        print("正在构建定理索引...")
        directories = [
            mathlib_path / 'Mathlib',
            mathlib_path / 'src',
        ]
        parser_obj.build_index([d for d in directories if d.exists()])
        
        # 保存索引
        with open(index_file, 'w', encoding='utf-8') as f:
            json.dump([asdict(t) for t in parser_obj.theorems], f, ensure_ascii=False)
    else:
        print("正在加载索引...")
        with open(index_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
            parser_obj.theorems = [Theorem(**t) for t in data]
        print(f"已加载 {len(parser_obj.theorems)} 个定理")
    
    # 执行搜索
    print(f"\n搜索: keyword={args.keyword}, domain={args.domain}, difficulty={args.difficulty}")
    results = parser_obj.search(
        keyword=args.keyword,
        domain=args.domain,
        difficulty=args.difficulty,
        author=args.author,
        tags=args.tags,
        limit=args.limit
    )
    
    # 格式化输出
    formatter = OutputFormatter()
    
    if args.format == 'markdown':
        output = formatter.format_markdown(results)
    elif args.format == 'json':
        output = formatter.format_json(results)
    elif args.format == 'csv':
        output = formatter.format_csv(results)
    else:
        output = formatter.format_console(results)
    
    # 输出结果
    if args.output:
        with open(args.output, 'w', encoding='utf-8') as f:
            f.write(output)
        print(f"\n结果已保存到: {args.output}")
    else:
        print(output)
    
    return 0


if __name__ == '__main__':
    exit(main())
