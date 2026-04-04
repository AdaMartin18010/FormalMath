#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
生成质量报告

汇总所有质量检查结果生成报告
"""

import argparse
import subprocess
from pathlib import Path
from datetime import datetime
from typing import Dict, List


class QualityReportGenerator:
    """质量报告生成器"""
    
    def __init__(self, project_root: str = "."):
        self.project_root = Path(project_root)
        self.stats = {}
    
    def collect_stats(self) -> Dict:
        """收集统计信息"""
        stats = {
            'total_docs': 0,
            'with_msc': 0,
            'with_level': 0,
            'versions': {
                'basic': 0,
                'enhanced': 0,
                'deep': 0,
                'standard': 0
            },
            'lean_files': 0,
            'recent_commits': 0
        }
        
        # 统计文档
        for path in [self.project_root / 'docs', self.project_root / '数学家理念体系']:
            if path.exists():
                for md_file in path.rglob('*.md'):
                    stats['total_docs'] += 1
                    
                    # 检查版本
                    name = md_file.name
                    if '-基础版.md' in name:
                        stats['versions']['basic'] += 1
                    elif '-增强版.md' in name:
                        stats['versions']['enhanced'] += 1
                    elif '-深度扩展版.md' in name:
                        stats['versions']['deep'] += 1
                    elif '-国际标准版.md' in name:
                        stats['versions']['standard'] += 1
                    
                    # 检查 frontmatter
                    try:
                        content = md_file.read_text(encoding='utf-8', errors='ignore')
                        if 'msc_primary:' in content:
                            stats['with_msc'] += 1
                        if 'level:' in content:
                            stats['with_level'] += 1
                    except:
                        pass
        
        # 统计 Lean 文件
        stats['lean_files'] = len(list(self.project_root.rglob('*.lean')))
        
        # 最近提交数
        try:
            result = subprocess.run(
                ['git', 'log', '--oneline', '--since=7.days'],
                capture_output=True,
                text=True,
                check=True
            )
            stats['recent_commits'] = len(result.stdout.strip().split('\n'))
        except:
            pass
        
        self.stats = stats
        return stats
    
    def generate_report(self) -> str:
        """生成报告"""
        if not self.stats:
            self.collect_stats()
        
        lines = [
            "# FormalMath 质量周报",
            "",
            f"**生成时间**: {datetime.now().strftime('%Y年%m月%d日')}",
            "",
            "---",
            "",
            "## 📊 文档统计",
            "",
            f"| 指标 | 数量 | 占比 |",
            f"|------|------|------|",
            f"| 总文档数 | {self.stats['total_docs']} | 100% |",
            f"| 带 MSC 编码 | {self.stats['with_msc']} | {self._percent(self.stats['with_msc'], self.stats['total_docs'])} |",
            f"| 带层次标注 | {self.stats['with_level']} | {self._percent(self.stats['with_level'], self.stats['total_docs'])} |",
            "",
            "### 版本分布",
            "",
            f"| 版本类型 | 数量 |",
            f"|----------|------|",
            f"| 基础版 | {self.stats['versions']['basic']} |",
            f"| 增强版 | {self.stats['versions']['enhanced']} |",
            f"| 深度扩展版 | {self.stats['versions']['deep']} |",
            f"| 国际标准版 | {self.stats['versions']['standard']} |",
            "",
            "## 🔬 形式化证明",
            "",
            f"- Lean4 文件数: {self.stats['lean_files']}",
            "",
            "## 📈 近期活动",
            "",
            f"- 最近 7 天提交数: {self.stats['recent_comits'] if 'recent_comits' in self.stats else self.stats.get('recent_commits', 0)}",
            "",
            "## ⚠️ 质量警告",
            "",
            "### MSC 编码覆盖率低的分支",
            "",
            "待统计...",
            "",
            "### 超过 6 个月未更新的文档",
            "",
            "待统计...",
            "",
            "---",
            "",
            "*本报告由 GitHub Actions 自动生成*",
        ]
        
        return '\n'.join(lines)
    
    def _percent(self, part: int, total: int) -> str:
        """计算百分比"""
        if total == 0:
            return "0%"
        return f"{part/total*100:.1f}%"
    
    def save_report(self, output_path: str) -> None:
        """保存报告"""
        report = self.generate_report()
        Path(output_path).write_text(report, encoding='utf-8')
        print(f"报告已保存到: {output_path}")


def main():
    parser = argparse.ArgumentParser(description='生成质量报告')
    parser.add_argument('--output', type=str, required=True, help='输出文件路径')
    parser.add_argument('--project-root', type=str, default='.', help='项目根目录')
    
    args = parser.parse_args()
    
    generator = QualityReportGenerator(args.project_root)
    generator.save_report(args.output)


if __name__ == '__main__':
    main()
