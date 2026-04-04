#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
贡献者排行榜更新脚本

生成 CONTRIBUTORS.md 排行榜文件
"""

import argparse
import json
import re
import subprocess
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple
from collections import defaultdict


class LeaderboardGenerator:
    """排行榜生成器"""
    
    def __init__(self, project_root: str = "."):
        self.project_root = Path(project_root)
        self.contributors: Dict[str, Dict] = defaultdict(lambda: {
            'points': 0,
            'prs': 0,
            'commits': 0,
            'first_contribution': None,
            'last_contribution': None,
            'badges': set()
        })
    
    def collect_contributions(self) -> None:
        """收集贡献数据"""
        # 从 git 历史收集数据
        self._collect_from_git()
        
        # 从 PR 数据收集（如果有）
        # self._collect_from_prs()
    
    def _collect_from_git(self) -> None:
        """从 git 历史收集贡献数据"""
        try:
            # 获取所有提交
            result = subprocess.run(
                ['git', 'log', '--format=%H|%an|%ae|%ad|%s', '--date=short'],
                capture_output=True,
                text=True,
                check=True
            )
            
            for line in result.stdout.strip().split('\n'):
                if '|' not in line:
                    continue
                
                parts = line.split('|')
                if len(parts) < 5:
                    continue
                
                commit_hash, author_name, author_email, date, message = parts[:5]
                
                # 使用邮箱作为唯一标识
                author_key = author_email.lower()
                
                contributor = self.contributors[author_key]
                contributor['name'] = author_name
                contributor['email'] = author_email
                contributor['commits'] += 1
                
                if contributor['first_contribution'] is None:
                    contributor['first_contribution'] = date
                contributor['last_contribution'] = date
                
                # 根据提交消息估算积分
                points = self._estimate_points_from_commit(message)
                contributor['points'] += points
                
                # 检测徽章
                badges = self._detect_badges_from_commit(message)
                contributor['badges'].update(badges)
        
        except subprocess.CalledProcessError as e:
            print(f"Git 命令失败: {e}")
    
    def _estimate_points_from_commit(self, message: str) -> int:
        """根据提交消息估算积分"""
        message_lower = message.lower()
        points = 0
        
        if re.search(r'feat|add|新增', message_lower):
            if 'docs' in message_lower or '文档' in message:
                points = 50
            elif 'lean' in message_lower:
                points = 150
            else:
                points = 30
        elif re.search(r'fix|修复|修正', message_lower):
            points = 20
        elif re.search(r'docs|文档', message_lower):
            points = 10
        elif re.search(r'translat|翻译', message_lower):
            points = 40
        else:
            points = 5
        
        return points
    
    def _detect_badges_from_commit(self, message: str) -> List[str]:
        """从提交消息检测徽章"""
        badges = []
        message_lower = message.lower()
        
        if re.search(r'lean|形式化', message_lower):
            badges.append('🔬')
        
        if re.search(r'translat|翻译', message_lower):
            badges.append('🌐')
        
        if re.search(r'fix|修复|修正', message_lower):
            badges.append('🐛')
        
        return badges
    
    def generate_leaderboard(self) -> str:
        """生成排行榜 Markdown"""
        lines = [
            "# FormalMath 贡献者排行榜",
            "",
            f"**最后更新**: {datetime.now().strftime('%Y年%m月%d日')}",
            "",
            "> 本页面自动更新，感谢所有贡献者！",
            "",
            "---",
            "",
            "## 🏆 总积分榜",
            "",
            "| 排名 | 贡献者 | 积分 | 提交数 | 徽章 |",
            "|------|--------|------|--------|------|",
        ]
        
        # 排序
        sorted_contributors = sorted(
            self.contributors.items(),
            key=lambda x: x[1]['points'],
            reverse=True
        )
        
        # 生成表格
        for rank, (key, data) in enumerate(sorted_contributors[:50], 1):
            if data['points'] == 0:
                continue
            
            name = data.get('name', key)
            badges_str = ' '.join(sorted(data['badges'])) if data['badges'] else ''
            
            rank_emoji = {1: '🥇', 2: '🥈', 3: '🥉'}.get(rank, f'{rank}')
            
            lines.append(
                f"| {rank_emoji} | {name} | {data['points']} | {data['commits']} | {badges_str} |"
            )
        
        lines.extend([
            "",
            "---",
            "",
            "## 🎯 贡献等级",
            "",
            "| 等级 | 积分要求 | 说明 |",
            "|------|----------|------|",
            "| ⭐⭐⭐⭐⭐ | 5000+ | 项目维护者 |",
            "| ⭐⭐⭐⭐ | 2000-4999 | 核心贡献者 |",
            "| ⭐⭐⭐ | 500-1999 | 活跃贡献者 |",
            "| ⭐⭐ | 100-499 | 贡献者 |",
            "| ⭐ | 0-99 | 新成员 |",
            "",
            "---",
            "",
            "## 🏅 徽章说明",
            "",
            "| 徽章 | 含义 | 获得条件 |",
            "|------|------|----------|",
            "| 🔬 | 形式化专家 | 提交 Lean4 形式化证明 |",
            "| 🌐 | 翻译专家 | 完成翻译工作 |",
            "| 📚 | 文档大师 | 贡献 50+ 篇文档 |",
            "| 🐛 | 捉虫能手 | 修复 20+ 个错误 |",
            "| 👁️ | 审核专家 | 审核 50+ 个 PR |",
            "",
            "---",
            "",
            "## 📈 贡献统计",
            "",
        ])
        
        # 统计信息
        total_contributors = len(self.contributors)
        total_commits = sum(d['commits'] for d in self.contributors.values())
        total_points = sum(d['points'] for d in self.contributors.values())
        
        lines.extend([
            f"- **总贡献者**: {total_contributors} 人",
            f"- **总提交数**: {total_commits} 次",
            f"- **总积分**: {total_points} 分",
            "",
            "---",
            "",
            "## 🤝 如何上榜",
            "",
            "1. Fork 项目仓库",
            "2. 创建新分支进行贡献",
            "3. 提交 Pull Request",
            "4. 合并后自动记录贡献",
            "",
            "查看 [贡献指南](CONTRIBUTING.md) 了解详情。",
            "",
            "---",
            "",
            "*本页面由 GitHub Actions 自动生成*",
        ])
        
        return '\n'.join(lines)
    
    def save_leaderboard(self, output_path: str) -> None:
        """保存排行榜"""
        content = self.generate_leaderboard()
        Path(output_path).write_text(content, encoding='utf-8')
        print(f"排行榜已保存到: {output_path}")


def main():
    parser = argparse.ArgumentParser(description='更新贡献者排行榜')
    parser.add_argument('--output', type=str, default='CONTRIBUTORS.md',
                       help='输出文件路径')
    parser.add_argument('--project-root', type=str, default='.',
                       help='项目根目录')
    
    args = parser.parse_args()
    
    generator = LeaderboardGenerator(args.project_root)
    generator.collect_contributions()
    generator.save_leaderboard(args.output)


if __name__ == '__main__':
    main()
