#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
IMO题目生成器 (IMO Practice Generator)

功能:
- 按领域/难度/年份筛选题目
- 生成练习试卷
- 输出PDF/Markdown格式

使用示例:
    python imo_practice_generator.py --domain algebra --difficulty hard --count 5
    python imo_practice_generator.py --year 2020-2023 --output practice.md
    python imo_practice_generator.py --mixed --count 6 --format pdf

作者: FormalMath-Enhanced
版本: 1.0.0
"""

import argparse
import json
import random
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass, asdict
from enum import Enum


class ProblemDomain(Enum):
    """IMO题目领域"""
    ALGEBRA = "algebra"
    GEOMETRY = "geometry"
    NUMBER_THEORY = "number_theory"
    COMBINATORICS = "combinatorics"
    MIXED = "mixed"


class DifficultyLevel(Enum):
    """难度等级"""
    EASY = (1, 2)
    MEDIUM = (3, 4)
    HARD = (5, 6)
    MIXED = (1, 6)


@dataclass
class IMOProblem:
    """IMO题目数据结构"""
    year: int
    number: int  # 1-6
    domain: str
    difficulty: int  # 1-6
    statement: str
    solution: Optional[str]
    hints: List[str]
    source: str
    tags: List[str]
    solve_rate: Optional[float]  # 当年解决率
    average_score: Optional[float]  # 平均分


class IMOProblemDatabase:
    """IMO题目数据库"""
    
    def __init__(self, data_path: Optional[Path] = None):
        self.data_path = data_path or Path(__file__).parent / "imo_database.json"
        self.problems: List[IMOProblem] = []
        self._load_database()
    
    def _load_database(self) -> None:
        """加载题目数据库"""
        if self.data_path.exists():
            try:
                with open(self.data_path, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    self.problems = [IMOProblem(**p) for p in data.get('problems', [])]
            except Exception as e:
                print(f"警告: 无法加载数据库: {e}")
                self._init_sample_database()
        else:
            self._init_sample_database()
    
    def _init_sample_database(self) -> None:
        """初始化示例数据库"""
        sample_problems = [
            # 代数题目
            IMOProblem(
                year=2023,
                number=1,
                domain="algebra",
                difficulty=2,
                statement="""确定所有满足以下条件的合数正整数 $n$：
如果 $d_1, d_2, \ldots, d_k$ 是 $n$ 的所有正除数，且满足 $1 = d_1 < d_2 < \cdots < d_k = n$，
则对于每个 $i = 1, 2, \ldots, k-2$，都有 $d_i$ 整除 $d_{i+1} + d_{i+2}$。""",
                solution=None,
                hints=["考虑小合数的例子", "分析除数的结构", "利用归纳思想"],
                source="IMO 2023 Problem 1",
                tags=["divisors", "number theory", "sequences"],
                solve_rate=0.65,
                average_score=4.2
            ),
            IMOProblem(
                year=2023,
                number=4,
                domain="algebra",
                difficulty=5,
                statement="""设 $x_1, x_2, \ldots, x_{2023}$ 是两两不同的正实数，满足
$$a_k = \sqrt{(x_1 + x_2 + \cdots + x_k)\left(\frac{1}{x_1} + \frac{1}{x_2} + \cdots + \frac{1}{x_k}\right)}$$
是整数，其中 $k = 1, 2, \ldots, 2023$。
证明：$a_{2023} \geq 3034$。""",
                solution=None,
                hints=["使用柯西不等式", "分析递推关系", "寻找下界估计"],
                source="IMO 2023 Problem 4",
                tags=["inequality", "cauchy-schwarz", "sequences"],
                solve_rate=0.15,
                average_score=1.2
            ),
            # 几何题目
            IMOProblem(
                year=2022,
                number=2,
                domain="geometry",
                difficulty=4,
                statement="""设 $\mathbb{R}^+$ 表示正实数集合。求所有函数 $f: \mathbb{R}^+ \to \mathbb{R}^+$，
使得对于所有 $x, y \in \mathbb{R}^+$，等式
$$f(x) + f(y) = f(f(x) + y)$$
成立。""",
                solution=None,
                hints=["尝试线性函数", "分析函数的单射性", "建立递推关系"],
                source="IMO 2022 Problem 2",
                tags=["functional equation", "real numbers"],
                solve_rate=0.35,
                average_score=2.8
            ),
            IMOProblem(
                year=2022,
                number=6,
                domain="geometry",
                difficulty=6,
                statement="""设 $ABCD$ 是一个凸四边形，满足 $\angle BAC = 90°$ 和 $\angle BDC = 90°$。
设 $E$ 是直线 $AC$ 和 $BD$ 的交点。设 $F$ 是点 $A$ 关于直线 $BD$ 的对称点。
证明：直线 $FC$ 经过 $\triangle BCD$ 的外心。""",
                solution=None,
                hints=["利用对称性", "分析外心的性质", "考虑共圆条件"],
                source="IMO 2022 Problem 6",
                tags=["cyclic quadrilateral", "circumcenter", "symmetry"],
                solve_rate=0.05,
                average_score=0.4
            ),
            # 数论题目
            IMOProblem(
                year=2021,
                number=1,
                domain="number_theory",
                difficulty=2,
                statement="""设 $n \geq 100$ 是一个整数。Ivan 将 $n, n+1, \ldots, 2n$ 这 $n+1$ 个数写在黑板上。
每次操作，他选择两个数 $a, b$ 擦去，然后写上 $|a - b|$。证明：经过 $n$ 次操作后，
黑板上剩下的数小于 $n/2$。""",
                solution=None,
                hints=["分析不变量", "考虑模2的性质", "寻找上界"],
                source="IMO 2021 Problem 1",
                tags=["invariant", "parity", "process"],
                solve_rate=0.70,
                average_score=5.1
            ),
            IMOProblem(
                year=2021,
                number=3,
                domain="number_theory",
                difficulty=6,
                statement="""证明：存在无限多个正整数 $n$，使得 $n^2 + 1$ 有一个大于 $2n + \sqrt{2n}$ 的素因子。""",
                solution=None,
                hints=["利用佩尔方程", "分析素因子的分布", "构造无穷序列"],
                source="IMO 2021 Problem 3",
                tags=["prime factors", "pell equation", "infinite descent"],
                solve_rate=0.08,
                average_score=0.6
            ),
            # 组合题目
            IMOProblem(
                year=2020,
                number=2,
                domain="combinatorics",
                difficulty=4,
                statement="""设 $n \geq 3$ 是整数。给定平面上 $n$ 个点，其中任意三点不共线。
一个包含这些点的多边形称为好的，如果它的顶点是给定点的一个子集，且每条边至少包含一个给定点
（除了端点）。求好多边形的最大边数。""",
                solution=None,
                hints=["考虑凸包", "分析点集的分布", "寻找极值构造"],
                source="IMO 2020 Problem 2",
                tags=["convex hull", "combinatorial geometry", "extremal"],
                solve_rate=0.28,
                average_score=2.1
            ),
            IMOProblem(
                year=2020,
                number=6,
                domain="combinatorics",
                difficulty=6,
                statement="""证明：存在一个正实数 $c$，使得以下结论成立：
对于每个整数 $n \geq 2$ 和每个由 $n$ 个正整数组成的集合 $S$，如果 $|S| \leq cn^{3/2}$，
则存在 $S$ 的一个子集 $T \subseteq S$，满足 $|T| \geq n/2$ 且 $T$ 中任意三个元素不构成等差数列。""",
                solution=None,
                hints=["使用概率方法", "分析3-AP-free集合", "应用容斥原理"],
                source="IMO 2020 Problem 6",
                tags=["arithmetic progression", "probabilistic method", "ramsey theory"],
                solve_rate=0.03,
                average_score=0.2
            ),
        ]
        
        # 为样例题目生成更多变体
        for year in range(2019, 2010, -1):
            for i, domain in enumerate(["algebra", "geometry", "number_theory", "combinatorics"]):
                for num in range(1, 7):
                    if random.random() > 0.3:  # 70%概率生成
                        sample_problems.append(IMOProblem(
                            year=year,
                            number=num,
                            domain=domain,
                            difficulty=num,
                            statement=f"[示例题目] {year}年IMO第{num}题 - {domain}领域\n\n"
                                     f"这是一个示例题目，描述{domain}领域的数学问题。",
                            solution="示例解答...",
                            hints=["提示1", "提示2", "提示3"],
                            source=f"IMO {year} Problem {num}",
                            tags=[domain, f"imo{year}"],
                            solve_rate=random.uniform(0.05, 0.80),
                            average_score=random.uniform(0.5, 5.5)
                        ))
        
        self.problems = sample_problems
        self._save_database()
    
    def _save_database(self) -> None:
        """保存数据库"""
        try:
            data = {
                'version': '1.0',
                'updated': datetime.now().isoformat(),
                'problems': [asdict(p) for p in self.problems]
            }
            with open(self.data_path, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
        except Exception as e:
            print(f"警告: 无法保存数据库: {e}")
    
    def filter_problems(self,
                       domain: Optional[str] = None,
                       difficulty_range: Optional[Tuple[int, int]] = None,
                       year_range: Optional[Tuple[int, int]] = None,
                       tags: Optional[List[str]] = None) -> List[IMOProblem]:
        """
        筛选题目
        
        Args:
            domain: 领域
            difficulty_range: 难度范围 (min, max)
            year_range: 年份范围 (min, max)
            tags: 标签列表
            
        Returns:
            筛选后的题目列表
        """
        results = self.problems.copy()
        
        if domain and domain != "mixed":
            results = [p for p in results if p.domain == domain]
        
        if difficulty_range:
            min_diff, max_diff = difficulty_range
            results = [p for p in results if min_diff <= p.difficulty <= max_diff]
        
        if year_range:
            min_year, max_year = year_range
            results = [p for p in results if min_year <= p.year <= max_year]
        
        if tags:
            results = [p for p in results if any(tag in p.tags for tag in tags)]
        
        return results
    
    def get_random_problems(self, 
                           count: int,
                           domain: Optional[str] = None,
                           difficulty: Optional[str] = None,
                           year_range: Optional[str] = None) -> List[IMOProblem]:
        """
        随机获取题目
        
        Args:
            count: 题目数量
            domain: 领域
            difficulty: 难度等级
            year_range: 年份范围 (如 "2020-2023")
            
        Returns:
            随机题目列表
        """
        # 解析难度范围
        difficulty_range = None
        if difficulty:
            diff_levels = {
                'easy': (1, 2),
                'medium': (3, 4),
                'hard': (5, 6),
            }
            difficulty_range = diff_levels.get(difficulty, (1, 6))
        
        # 解析年份范围
        year_range_tuple = None
        if year_range:
            parts = year_range.split('-')
            if len(parts) == 2:
                year_range_tuple = (int(parts[0]), int(parts[1]))
        
        filtered = self.filter_problems(
            domain=domain,
            difficulty_range=difficulty_range,
            year_range=year_range_tuple
        )
        
        if len(filtered) < count:
            print(f"警告: 只有 {len(filtered)} 个符合条件的题目，少于请求的 {count} 个")
            return filtered
        
        return random.sample(filtered, count)


class PaperGenerator:
    """试卷生成器"""
    
    def __init__(self, database: IMOProblemDatabase):
        self.db = database
    
    def generate_markdown(self, 
                         problems: List[IMOProblem],
                         title: str = "IMO 练习试卷",
                         include_solutions: bool = False,
                         include_hints: bool = False) -> str:
        """
        生成Markdown格式试卷
        
        Args:
            problems: 题目列表
            title: 试卷标题
            include_solutions: 是否包含解答
            include_hints: 是否包含提示
            
        Returns:
            Markdown内容
        """
        md = f"# {title}\n\n"
        md += f"生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M')}\n\n"
        md += f"---\n\n"
        
        # 试卷统计
        domains = {}
        difficulties = {}
        for p in problems:
            domains[p.domain] = domains.get(p.domain, 0) + 1
            difficulties[p.difficulty] = difficulties.get(p.difficulty, 0) + 1
        
        md += "## 试卷信息\n\n"
        md += f"- 题目数量: {len(problems)}\n"
        md += f"- 领域分布: {', '.join(f'{k}: {v}' for k, v in domains.items())}\n"
        md += f"- 难度分布: {', '.join(f'P{k}: {v}' for k, v in sorted(difficulties.items()))}\n\n"
        md += "---\n\n"
        
        # 题目
        md += "## 题目\n\n"
        for i, p in enumerate(problems, 1):
            md += f"### 第 {i} 题\n\n"
            md += f"**来源**: {p.source}  ",
            md += f"**领域**: {p.domain}  ",
            md += f"**难度**: {'⭐' * p.difficulty}\n\n"
            md += f"{p.statement}\n\n"
            
            if include_hints and p.hints:
                md += "**提示**:\n"
                for j, hint in enumerate(p.hints, 1):
                    md += f"{j}. {hint}\n"
                md += "\n"
            
            if include_solutions and p.solution:
                md += "**解答**:\n\n"
                md += f"```\n{p.solution}\n```\n\n"
            
            md += "---\n\n"
        
        return md
    
    def generate_latex(self,
                      problems: List[IMOProblem],
                      title: str = "IMO Practice") -> str:
        """生成LaTeX格式（用于PDF输出）"""
        latex = r"""\documentclass[12pt,a4paper]{article}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{geometry}
\usepackage{xeCJK}
\geometry{margin=2.5cm}

\theoremstyle{definition}
\newtheorem{problem}{Problem}

\begin{document}

"""
        latex += f"\\title{{{title}}}\n"
        latex += f"\\date{{{datetime.now().strftime('%Y-%m-%d')}}}\n"
        latex += "\\maketitle\n\n"
        
        for i, p in enumerate(problems, 1):
            latex += f"\\begin{{problem}}[{p.source} - {p.domain}]")
            latex += "\n"
            # 转换数学公式
            stmt = p.statement.replace('$', '$')
            latex += stmt + "\n"
            latex += "\\end{problem}\n\n"
        
        latex += "\\end{document}\n"
        return latex
    
    def generate_html(self,
                     problems: List[IMOProblem],
                     title: str = "IMO Practice") -> str:
        """生成HTML格式"""
        html = f"""<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>{title}</title>
    <script src="https://polyfill.io/v3/polyfill.min.js?features=es6"></script>
    <script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
    <style>
        body {{ font-family: 'Segoe UI', sans-serif; max-width: 900px; margin: 0 auto; padding: 20px; }}
        .problem {{ border: 1px solid #ddd; padding: 20px; margin: 20px 0; border-radius: 8px; }}
        .meta {{ color: #666; font-size: 0.9em; margin-bottom: 10px; }}
        h1 {{ color: #333; }}
        h2 {{ color: #555; border-bottom: 2px solid #eee; padding-bottom: 10px; }}
    </style>
</head>
<body>
    <h1>{title}</h1>
    <p>Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}</p>
"""
        
        for i, p in enumerate(problems, 1):
            html += f"""
    <div class="problem">
        <h2>Problem {i}</h2>
        <div class="meta">
            Source: {p.source} | Domain: {p.domain} | Difficulty: {'★' * p.difficulty}
        </div>
        <div>{p.statement}</div>
    </div>
"""
        
        html += "</body></html>"
        return html


def main():
    parser = argparse.ArgumentParser(
        description="IMO题目生成器 - 生成IMO练习试卷",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
使用示例:
  %(prog)s --domain algebra --difficulty hard --count 5
  %(prog)s --year 2020-2023 --output practice.md
  %(prog)s --mixed --count 6 --format pdf --include-hints
  %(prog)s --domain geometry --difficulty medium --solutions -o exam.md
        """
    )
    
    parser.add_argument('--domain', '-d', type=str,
                       choices=['algebra', 'geometry', 'number_theory', 'combinatorics', 'mixed'],
                       default='mixed',
                       help='题目领域')
    parser.add_argument('--difficulty', '-D', type=str,
                       choices=['easy', 'medium', 'hard', 'mixed'],
                       default='mixed',
                       help='难度等级')
    parser.add_argument('--year', '-y', type=str,
                       help='年份范围 (如: 2020-2023)')
    parser.add_argument('--count', '-c', type=int, default=6,
                       help='题目数量 (默认: 6)')
    parser.add_argument('--format', '-f', type=str,
                       choices=['markdown', 'latex', 'html', 'pdf'],
                       default='markdown',
                       help='输出格式')
    parser.add_argument('--output', '-o', type=Path,
                       help='输出文件路径')
    parser.add_argument('--title', '-t', type=str,
                       default='IMO Practice Exam',
                       help='试卷标题')
    parser.add_argument('--solutions', '-s', action='store_true',
                       help='包含解答')
    parser.add_argument('--hints', '-H', action='store_true',
                       help='包含提示')
    parser.add_argument('--seed', type=int,
                       help='随机种子')
    
    args = parser.parse_args()
    
    # 设置随机种子
    if args.seed:
        random.seed(args.seed)
    
    # 初始化数据库
    db = IMOProblemDatabase()
    
    # 获取题目
    problems = db.get_random_problems(
        count=args.count,
        domain=args.domain if args.domain != 'mixed' else None,
        difficulty=args.difficulty if args.difficulty != 'mixed' else None,
        year_range=args.year
    )
    
    if not problems:
        print("错误: 未找到符合条件的题目")
        return 1
    
    # 生成试卷
    generator = PaperGenerator(db)
    
    if args.format == 'markdown':
        content = generator.generate_markdown(
            problems, args.title, args.solutions, args.hints
        )
        ext = '.md'
    elif args.format == 'latex':
        content = generator.generate_latex(problems, args.title)
        ext = '.tex'
    elif args.format == 'html':
        content = generator.generate_html(problems, args.title)
        ext = '.html'
    else:  # pdf
        # 先生成LaTeX，然后需要编译
        content = generator.generate_latex(problems, args.title)
        ext = '.tex'
        print("PDF生成需要LaTeX编译器。已生成.tex文件，请手动编译。")
    
    # 输出
    if args.output:
        output_path = args.output
    else:
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        output_path = Path(f"imo_practice_{timestamp}{ext}")
    
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write(content)
    
    print(f"试卷已生成: {output_path}")
    print(f"包含 {len(problems)} 道题目")
    
    return 0


if __name__ == '__main__':
    exit(main())
