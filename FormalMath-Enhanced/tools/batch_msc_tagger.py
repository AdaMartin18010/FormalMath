#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
批量MSC编码标注工具 (Batch MSC Tagger)

功能:
- 读取数学文本文件
- 自动推荐MSC编码
- 批量添加YAML frontmatter
- 生成标注报告

使用示例:
    python batch_msc_tagger.py --input docs/ --output annotated/ --report report.md
    python batch_msc_tagger.py --file single.md --dry-run
    python batch_msc_tagger.py --input concept/ --confidence 0.8

作者: FormalMath-Enhanced
版本: 1.0.0
"""

import argparse
import re
import os
import json
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass, asdict


@dataclass
class MSCRecommendation:
    """MSC编码推荐结果"""
    code: str
    description: str
    confidence: float
    reason: str


@dataclass
class AnnotationReport:
    """标注报告"""
    total_files: int
    processed_files: int
    skipped_files: int
    recommendations: List[Dict]
    timestamp: str


class MSCTagger:
    """MSC编码标注器"""

    # MSC 2020 主要分类及其关键词映射
    MSC_CATEGORIES = {
        "00": {
            "name": "General",
            "keywords": ["history", "biography", "bibliography", "general"],
            "subcategories": {
                "01": "History and biography",
                "A05": "General mathematics",
            }
        },
        "03": {
            "name": "Mathematical logic and foundations",
            "keywords": ["logic", "set theory", "model theory", "proof theory", "recursive", "axiom"],
            "subcategories": {
                "B48": "Higher-order logic",
                "C57": "Proof theory",
                "E72": "Fuzzy set theory",
            }
        },
        "11": {
            "name": "Number theory",
            "keywords": ["number theory", "prime", "integer", "diophantine", "modular", "arithmetic"],
            "subcategories": {
                "A41": "Primes",
                "B68": "Approximation",
                "D09": "Quadratic forms",
            }
        },
        "14": {
            "name": "Algebraic geometry",
            "keywords": ["algebraic geometry", "variety", "scheme", "curve", "surface"],
            "subcategories": {
                "H52": "Algebraic curves",
                "J60": "Abelian varieties",
            }
        },
        "26": {
            "name": "Real functions",
            "keywords": ["real function", "continuous", "differentiable", "monotone", "convex"],
            "subcategories": {
                "A06": "One-variable calculus",
                "B25": "Convex functions",
            }
        },
        "30": {
            "name": "Functions of a complex variable",
            "keywords": ["complex analysis", "holomorphic", "analytic", "contour", "residue"],
            "subcategories": {
                "A99": "General complex analysis",
                "E20": "Entire functions",
            }
        },
        "34": {
            "name": "Ordinary differential equations",
            "keywords": ["ODE", "differential equation", "dynamical system", "stability"],
            "subcategories": {
                "A12": "Initial value problems",
                "C25": "Analytic theory",
            }
        },
        "35": {
            "name": "Partial differential equations",
            "keywords": ["PDE", "partial differential", "wave equation", "heat equation", "Laplace"],
            "subcategories": {
                "A15": "Elliptic equations",
                "L05": "Wave equation",
            }
        },
        "40": {
            "name": "Sequences, series, summability",
            "keywords": ["sequence", "series", "convergence", "summation", "divergent"],
            "subcategories": {
                "A05": "Convergence",
                "G10": "Summability",
            }
        },
        "42": {
            "name": "Harmonic analysis",
            "keywords": ["Fourier", "harmonic analysis", "orthogonal", "wavelet"],
            "subcategories": {
                "A16": "Fourier coefficients",
                "C05": "Orthogonal functions",
            }
        },
        "46": {
            "name": "Functional analysis",
            "keywords": ["functional analysis", "Banach", "Hilbert", "operator", "linear space"],
            "subcategories": {
                "B03": "Banach spaces",
                "C05": "Hilbert spaces",
            }
        },
        "51": {
            "name": "Geometry",
            "keywords": ["geometry", "Euclidean", "non-Euclidean", "projective", "affine"],
            "subcategories": {
                "A05": "Foundations",
                "M04": "Euclidean geometry",
            }
        },
        "54": {
            "name": "General topology",
            "keywords": ["topology", "topological space", "compact", "connected", "continuity"],
            "subcategories": {
                "A05": "Generalities",
                "D30": "Compactness",
            }
        },
        "60": {
            "name": "Probability theory",
            "keywords": ["probability", "stochastic", "random", "distribution", "Markov"],
            "subcategories": {
                "A05": "Axioms",
                "G50": "Stochastic processes",
            }
        },
        "62": {
            "name": "Statistics",
            "keywords": ["statistics", "estimation", "hypothesis", "regression", "sampling"],
            "subcategories": {
                "F03": "Hypothesis testing",
                "J05": "Linear regression",
            }
        },
        "65": {
            "name": "Numerical analysis",
            "keywords": ["numerical", "approximation", "finite element", "iteration", "discretization"],
            "subcategories": {
                "D99": "Numerical ODE",
                "M60": "Finite element methods",
            }
        },
        "68": {
            "name": "Computer science",
            "keywords": ["algorithm", "complexity", "computational", "automata", "formal language"],
            "subcategories": {
                "Q25": "Quantum computing",
                "T20": "Machine learning",
            }
        },
        "81": {
            "name": "Quantum theory",
            "keywords": ["quantum", "quantum mechanics", "Hilbert space", "observable"],
            "subcategories": {
                "Q10": "Foundations",
                "S22": "Quantum field theory",
            }
        },
        "97": {
            "name": "Mathematics education",
            "keywords": ["education", "teaching", "learning", "pedagogy", "curriculum"],
            "subcategories": {
                "C70": "Teaching",
                "U50": "Computer assisted",
            }
        },
    }

    def __init__(self, confidence_threshold: float = 0.5):
        self.confidence_threshold = confidence_threshold
        self.recommendations: List[Dict] = []

    def analyze_content(self, content: str) -> List[MSCRecommendation]:
        """
        分析内容并推荐MSC编码

        Args:
            content: 文档内容

        Returns:
            推荐列表，按置信度排序
        """
        content_lower = content.lower()
        recommendations = []

        for category_code, category_info in self.MSC_CATEGORIES.items():
            score = 0.0
            matched_keywords = []

            # 检查主分类关键词
            for keyword in category_info["keywords"]:
                count = content_lower.count(keyword.lower())
                if count > 0:
                    score += min(count * 0.1, 0.3)
                    matched_keywords.append(keyword)

            # 检查子分类
            best_subcategory = None
            best_sub_score = 0.0

            for sub_code, sub_name in category_info["subcategories"].items():
                sub_score = 0.0
                for word in sub_name.lower().split():
                    if len(word) > 3 and word in content_lower:
                        sub_score += 0.15

                if sub_score > best_sub_score:
                    best_sub_score = sub_score
                    best_subcategory = sub_code

            total_score = score + best_sub_score

            if total_score >= self.confidence_threshold:
                full_code = f"{category_code}{best_subcategory}" if best_subcategory else f"{category_code}-XX"

                recommendations.append(MSCRecommendation(
                    code=full_code,
                    description=f"{category_info['name']}",
                    confidence=min(total_score, 1.0),
                    reason=f"Matched keywords: {', '.join(matched_keywords[:5])}"
                ))

        # 按置信度排序
        recommendations.sort(key=lambda x: x.confidence, reverse=True)
        return recommendations[:5]  # 返回前5个推荐

    def generate_frontmatter(self, recommendations: List[MSCRecommendation],
                           title: str = "", author: str = "") -> str:
        """
        生成YAML frontmatter

        Args:
            recommendations: MSC推荐列表
            title: 文档标题
            author: 作者

        Returns:
            YAML frontmatter字符串
        """
        primary_msc = recommendations[0].code if recommendations else "00-XX"
        secondary_mscs = [r.code for r in recommendations[1:4]]

        frontmatter = f"""---
title: "{title or 'Untitled'}"
author: "{author or 'Unknown'}"
msc:
  primary: "{primary_msc}"
  secondary: {json.dumps(secondary_mscs)}
msc_recommendations:
"""

        for i, rec in enumerate(recommendations, 1):
            frontmatter += f"  - code: \"{rec.code}\"\n"
            frontmatter += f"    confidence: {rec.confidence:.2f}\n"
            frontmatter += f"    description: \"{rec.description}\"\n"

        frontmatter += f"annotated_at: \"{datetime.now().isoformat()}\"\n"
        frontmatter += "---\n\n"

        return frontmatter

    def process_file(self, file_path: Path, dry_run: bool = False) -> Dict:
        """
        处理单个文件

        Args:
            file_path: 文件路径
            dry_run: 是否只模拟运行

        Returns:
            处理结果字典
        """
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()

            # 检查是否已有frontmatter
            if content.startswith('---'):
                return {
                    "file": str(file_path),
                    "status": "skipped",
                    "reason": "Already has frontmatter"
                }

            # 提取标题
            title_match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
            title = title_match.group(1) if title_match else file_path.stem

            # 分析内容
            recommendations = self.analyze_content(content)

            result = {
                "file": str(file_path),
                "status": "processed",
                "title": title,
                "recommendations": [
                    asdict(r) for r in recommendations
                ]
            }

            if not dry_run and recommendations:
                # 生成并添加frontmatter
                frontmatter = self.generate_frontmatter(recommendations, title)
                new_content = frontmatter + content

                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(new_content)

                result["frontmatter_added"] = True

            self.recommendations.append(result)
            return result

        except Exception as e:
            error_result = {
                "file": str(file_path),
                "status": "error",
                "error": str(e)
            }
            self.recommendations.append(error_result)
            return error_result

    def process_directory(self, input_dir: Path, output_dir: Optional[Path] = None,
                         dry_run: bool = False) -> AnnotationReport:
        """
        处理整个目录

        Args:
            input_dir: 输入目录
            output_dir: 输出目录（可选）
            dry_run: 是否只模拟运行

        Returns:
            标注报告
        """
        total_files = 0
        processed_files = 0
        skipped_files = 0

        # 支持的文件扩展名
        extensions = {'.md', '.txt', '.rst'}

        for file_path in input_dir.rglob('*'):
            if file_path.suffix in extensions:
                total_files += 1

                if output_dir and not dry_run:
                    # 复制到输出目录
                    rel_path = file_path.relative_to(input_dir)
                    out_path = output_dir / rel_path
                    out_path.parent.mkdir(parents=True, exist_ok=True)

                    import shutil
                    shutil.copy2(file_path, out_path)
                    result = self.process_file(out_path, dry_run)
                else:
                    result = self.process_file(file_path, dry_run)

                if result["status"] == "processed":
                    processed_files += 1
                elif result["status"] == "skipped":
                    skipped_files += 1

        return AnnotationReport(
            total_files=total_files,
            processed_files=processed_files,
            skipped_files=skipped_files,
            recommendations=self.recommendations,
            timestamp=datetime.now().isoformat()
        )

    def generate_report(self, report: AnnotationReport, output_path: Path) -> None:
        """
        生成标注报告

        Args:
            report: 标注报告对象
            output_path: 输出路径
        """
        report_content = f"""# MSC编码标注报告

生成时间: {report.timestamp}

## 统计信息

| 指标 | 数值 |
|------|------|
| 总文件数 | {report.total_files} |
| 已处理 | {report.processed_files} |
| 已跳过 | {report.skipped_files} |
| 成功率 | {report.processed_files/max(report.total_files,1)*100:.1f}% |

## 详细结果

"""

        for rec in report.recommendations:
            report_content += f"### {rec['file']}\n\n"
            report_content += f"- **状态**: {rec['status']}\n"

            if 'title' in rec:
                report_content += f"- **标题**: {rec['title']}\n"

            if 'recommendations' in rec and rec['recommendations']:
                report_content += "- **MSC推荐**:\n"
                for r in rec['recommendations'][:3]:
                    report_content += f"  - `{r['code']}` - {r['description']} (置信度: {r['confidence']:.2f})\n"

            if 'error' in rec:
                report_content += f"- **错误**: {rec['error']}\n"

            report_content += "\n"

        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(report_content)


def main():
    parser = argparse.ArgumentParser(
        description="批量MSC编码标注工具",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
使用示例:
  %(prog)s --input docs/ --output annotated/ --report report.md
  %(prog)s --file single.md --dry-run
  %(prog)s --input concept/ --confidence 0.8 --report msc_report.md
        """
    )

    parser.add_argument('--input', '-i', type=Path,
                       help='输入目录路径')
    parser.add_argument('--file', '-f', type=Path,
                       help='单个文件路径')
    parser.add_argument('--output', '-o', type=Path,
                       help='输出目录路径（可选）')
    parser.add_argument('--report', '-r', type=Path,
                       help='报告输出路径')
    parser.add_argument('--confidence', '-c', type=float, default=0.5,
                       help='置信度阈值（默认: 0.5）')
    parser.add_argument('--dry-run', '-d', action='store_true',
                       help='模拟运行，不实际修改文件')
    parser.add_argument('--author', '-a', type=str, default='',
                       help='默认作者名称')

    args = parser.parse_args()

    if not args.input and not args.file:
        parser.error("必须指定 --input 或 --file")

    tagger = MSCTagger(confidence_threshold=args.confidence)

    if args.file:
        # 处理单个文件
        result = tagger.process_file(args.file, dry_run=args.dry_run)
        print(f"文件: {result['file']}")
        print(f"状态: {result['status']}")
        if 'recommendations' in result:
            print("MSC推荐:")
            for r in result['recommendations'][:3]:
                print(f"  - {r['code']}: {r['description']} (置信度: {r['confidence']:.2f})")
    else:
        # 处理目录
        if not args.input.exists():
            print(f"错误: 输入目录不存在: {args.input}")
            return 1

        if args.output:
            args.output.mkdir(parents=True, exist_ok=True)

        report = tagger.process_directory(
            args.input,
            output_dir=args.output,
            dry_run=args.dry_run
        )

        print(f"\n处理完成!")
        print(f"总文件数: {report.total_files}")
        print(f"已处理: {report.processed_files}")
        print(f"已跳过: {report.skipped_files}")

        # 生成报告
        if args.report:
            tagger.generate_report(report, args.report)
            print(f"报告已保存: {args.report}")

    return 0


if __name__ == '__main__':
    exit(main())
