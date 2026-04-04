#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
贡献积分计算脚本

根据 PR 内容计算贡献积分
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from dataclasses import dataclass, asdict
from typing import List, Dict, Optional


@dataclass
class RewardResult:
    """奖励计算结果"""
    pr_number: int
    contributor: str
    contribution_type: str
    points: int
    level: str
    badges: List[str]
    details: Dict


class RewardCalculator:
    """积分计算器"""
    
    # 积分规则
    POINTS_RULES = {
        'docs_new_basic': 50,
        'docs_new_enhanced': 100,
        'docs_new_deep': 200,
        'docs_fix_minor': 20,
        'docs_fix_major': 50,
        'lean_theorem': 300,
        'lean_proof': 150,
        'translation_cn_en': 60,  # 每千字
        'translation_en_cn': 50,  # 每千字
        'tool_feature': 100,
        'tool_fix': 30,
        'review_pr': 10,
        'issue_triage': 5,
    }
    
    # 等级阈值
    LEVEL_THRESHOLDS = [
        (0, '⭐ 新成员'),
        (100, '⭐⭐ 贡献者'),
        (500, '⭐⭐⭐ 活跃贡献者'),
        (2000, '⭐⭐⭐⭐ 核心贡献者'),
        (5000, '⭐⭐⭐⭐⭐ 项目维护者'),
    ]
    
    def __init__(self):
        self.badges = []
    
    def calculate_from_pr(self, pr_number: int, pr_author: str, 
                         pr_title: str) -> RewardResult:
        """根据 PR 信息计算积分"""
        
        # 分析 PR 类型
        contrib_type = self._classify_pr(pr_title)
        
        # 获取 PR 的变更统计
        stats = self._get_pr_stats(pr_number)
        
        # 计算基础积分
        base_points = self._calculate_base_points(contrib_type, stats)
        
        # 计算额外奖励
        bonus_points = self._calculate_bonus(stats, pr_title)
        
        total_points = base_points + bonus_points
        
        # 确定等级
        level = self._determine_level(total_points)  # 这里应该用累计积分
        
        # 检查徽章
        badges = self._check_badges(contrib_type, stats)
        
        return RewardResult(
            pr_number=pr_number,
            contributor=pr_author,
            contribution_type=contrib_type,
            points=total_points,
            level=level,
            badges=badges,
            details={
                'base_points': base_points,
                'bonus_points': bonus_points,
                'stats': stats,
                'pr_title': pr_title
            }
        )
    
    def _classify_pr(self, title: str) -> str:
        """分类 PR 类型"""
        title_lower = title.lower()
        
        type_patterns = {
            'docs_new_basic': r'docs.*基础版|add.*basic',
            'docs_new_enhanced': r'docs.*增强版|add.*enhanced',
            'docs_new_deep': r'docs.*深度版|add.*deep',
            'docs_fix': r'fix.*docs|docs.*fix|修正|修复',
            'lean_theorem': r'lean.*theorem|theorem.*lean|形式化.*定理',
            'lean_proof': r'lean.*proof|proof.*lean|形式化.*证明',
            'translation': r'translat|翻译',
            'tool_feature': r'tool|script|工具|脚本',
            'chore': r'chore|ci|workflow',
        }
        
        for contrib_type, pattern in type_patterns.items():
            if re.search(pattern, title_lower):
                return contrib_type
        
        return 'other'
    
    def _get_pr_stats(self, pr_number: int) -> Dict:
        """获取 PR 的统计信息"""
        stats = {
            'files_changed': 0,
            'additions': 0,
            'deletions': 0,
            'docs_added': 0,
            'docs_modified': 0,
            'lean_files': 0,
        }
        
        try:
            # 获取文件变更列表
            result = subprocess.run(
                ['git', 'diff', '--numstat', 'HEAD~1', 'HEAD'],
                capture_output=True,
                text=True,
                check=True
            )
            
            for line in result.stdout.strip().split('\n'):
                if not line:
                    continue
                parts = line.split('\t')
                if len(parts) >= 3:
                    additions = int(parts[0]) if parts[0].isdigit() else 0
                    deletions = int(parts[1]) if parts[1].isdigit() else 0
                    filename = parts[2]
                    
                    stats['files_changed'] += 1
                    stats['additions'] += additions
                    stats['deletions'] += deletions
                    
                    if filename.endswith('.md'):
                        if additions > deletions * 2:
                            stats['docs_added'] += 1
                        else:
                            stats['docs_modified'] += 1
                    elif filename.endswith('.lean'):
                        stats['lean_files'] += 1
        
        except subprocess.CalledProcessError:
            pass
        
        return stats
    
    def _calculate_base_points(self, contrib_type: str, stats: Dict) -> int:
        """计算基础积分"""
        if contrib_type.startswith('docs_new_'):
            return self.POINTS_RULES.get(contrib_type, 50)
        elif contrib_type == 'docs_fix':
            if stats.get('additions', 0) < 50:
                return self.POINTS_RULES['docs_fix_minor']
            else:
                return self.POINTS_RULES['docs_fix_major']
        elif contrib_type == 'lean_theorem':
            return self.POINTS_RULES['lean_theorem']
        elif contrib_type == 'lean_proof':
            return self.POINTS_RULES['lean_proof']
        elif contrib_type == 'translation':
            # 估算字数
            words = stats.get('additions', 0) // 6  # 粗略估算
            return (words // 1000) * self.POINTS_RULES['translation_en_cn']
        elif contrib_type == 'tool_feature':
            return self.POINTS_RULES['tool_feature']
        else:
            return 10  # 默认积分
    
    def _calculate_bonus(self, stats: Dict, title: str) -> int:
        """计算额外奖励"""
        bonus = 0
        
        # 大量文档贡献奖励
        if stats.get('docs_added', 0) >= 5:
            bonus += 50
        
        # 包含完整证明的奖励
        if re.search(r'完整证明|complete proof|full proof', title.lower()):
            bonus += 30
        
        # 包含形式化的奖励
        if stats.get('lean_files', 0) > 0 and 'lean' not in title.lower():
            bonus += 50
        
        return bonus
    
    def _determine_level(self, total_points: int) -> str:
        """确定贡献者等级"""
        for threshold, level in reversed(self.LEVEL_THRESHOLDS):
            if total_points >= threshold:
                return level
        return self.LEVEL_THRESHOLDS[0][1]
    
    def _check_badges(self, contrib_type: str, stats: Dict) -> List[str]:
        """检查获得的徽章"""
        badges = []
        
        # 首次贡献徽章（需要查询历史，这里简化处理）
        # badges.append('🏅 首次贡献')
        
        # 文档大师徽章
        if stats.get('docs_added', 0) >= 3:
            badges.append('📚 文档大师')
        
        # 形式化专家徽章
        if stats.get('lean_files', 0) >= 1:
            badges.append('🔬 形式化专家')
        
        return badges


def main():
    parser = argparse.ArgumentParser(description='计算 PR 贡献积分')
    parser.add_argument('--pr-number', type=int, required=True, help='PR 编号')
    parser.add_argument('--pr-author', type=str, required=True, help='PR 作者')
    parser.add_argument('--pr-title', type=str, required=True, help='PR 标题')
    parser.add_argument('--output', type=str, help='输出文件路径')
    
    args = parser.parse_args()
    
    calculator = RewardCalculator()
    result = calculator.calculate_from_pr(
        args.pr_number,
        args.pr_author,
        args.pr_title
    )
    
    # 输出结果
    output = json.dumps(asdict(result), indent=2, ensure_ascii=False)
    
    if args.output:
        Path(args.output).write_text(output, encoding='utf-8')
        print(f"结果已保存到: {args.output}")
    else:
        print(output)


if __name__ == '__main__':
    main()
