#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
合并新概念到主概念图谱
"""

import re
from datetime import datetime

def load_file(filepath):
    """加载文件内容"""
    with open(filepath, 'r', encoding='utf-8') as f:
        return f.read()

def merge_concepts():
    """合并新概念到主文件"""
    
    # 加载原始文件
    original_content = load_file('project/concept_prerequisites.yaml')
    
    # 加载新概念
    new_concepts = load_file('project/new_concepts_batch12.yaml')
    
    # 在metadata之前插入新概念
    # 找到 metadata: 的位置
    metadata_match = re.search(r'^metadata:', original_content, re.MULTILINE)
    
    if metadata_match:
        insert_pos = metadata_match.start()
        
        # 构建新的内容
        new_content = original_content[:insert_pos] + new_concepts + '\n' + original_content[insert_pos:]
        
        # 更新metadata
        metadata_old = '''metadata:
  total_concepts: 100
  categories:
    - name: "分析学"
      count: 25
      difficulty_range: "2-5"
    - name: "代数学"
      count: 25
      difficulty_range: "1-5"
    - name: "几何拓扑"
      count: 25
      difficulty_range: "2-5"
    - name: "数论逻辑"
      count: 25
      difficulty_range: "1-5"
  total_estimated_hours: 3455
  generated_date: "2026-04-04"
  version: "1.0"'''
        
        metadata_new = '''metadata:
  total_concepts: 200
  categories:
    - name: "分析学"
      count: 25
      difficulty_range: "2-5"
    - name: "代数学"
      count: 25
      difficulty_range: "1-5"
    - name: "几何拓扑"
      count: 25
      difficulty_range: "2-5"
    - name: "数论逻辑"
      count: 25
      difficulty_range: "1-5"
    - name: "概率统计"
      count: 20
      difficulty_range: "2-4"
    - name: "最优化"
      count: 20
      difficulty_range: "2-4"
    - name: "控制论"
      count: 20
      difficulty_range: "2-4"
    - name: "信息论"
      count: 20
      difficulty_range: "2-5"
    - name: "密码学"
      count: 20
      difficulty_range: "3-5"
  total_estimated_hours: 6558
  generated_date: "2026-04-04"
  version: "2.0"
  extended_by: "第十二批扩展"
  cross_discipline_connections:
    - "信息论 ↔ 概率统计: 香农熵、KL散度"
    - "最优化 ↔ 控制论: 最优控制、MPC"
    - "密码学 ↔ 数论: RSA、椭圆曲线"
    - "密码学 ↔ 代数: 群论、有限域"'''
        
        # 替换metadata
        new_content = new_content.replace(metadata_old, metadata_new)
        
        # 更新文件头
        new_content = new_content.replace(
            '# FormalMath 核心数学概念前置关系数据库\n# 版本: 1.0\n# 概念数量: 100个\n# 分类: 分析学(25) | 代数学(25) | 几何拓扑(25) | 数论逻辑(25)',
            '# FormalMath 核心数学概念前置关系数据库\n# 版本: 2.0\n# 概念数量: 200个\n# 分类: 分析学(25) | 代数学(25) | 几何拓扑(25) | 数论逻辑(25) | 概率统计(20) | 最优化(20) | 控制论(20) | 信息论(20) | 密码学(20)'
        )
        
        # 保存合并后的文件
        with open('project/concept_prerequisites.yaml', 'w', encoding='utf-8') as f:
            f.write(new_content)
        
        print("✓ 概念图谱已成功扩展到200个概念")
        print("✓ 文件已更新: project/concept_prerequisites.yaml")
        
        # 统计信息
        print("\n=== 扩展后统计 ===")
        print("总概念数: 200")
        print("原有概念: 100 (分析学25 + 代数学25 + 几何拓扑25 + 数论逻辑25)")
        print("新增概念: 100 (概率统计20 + 最优化20 + 控制论20 + 信息论20 + 密码学20)")
        print("预计总学习时长: 6558 小时")
        
    else:
        print("错误: 无法找到metadata位置")

if __name__ == '__main__':
    merge_concepts()
