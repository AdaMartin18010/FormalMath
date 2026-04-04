#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复概念图谱中的问题
生成修正后的concept_prerequisites.yaml
"""

import yaml
import json
from collections import defaultdict
from datetime import datetime
from pathlib import Path

class ConceptGraphFixer:
    def __init__(self, project_dir):
        self.project_dir = Path(project_dir)
        self.errors_fixed = 0
        self.warnings_fixed = 0
        self.changes = []
        
    def load_data(self):
        """加载数据"""
        yaml_file = self.project_dir / 'concept_prerequisites_400.yaml'
        with open(yaml_file, 'r', encoding='utf-8') as f:
            self.data = yaml.safe_load(f)
        
        # 提取所有概念
        self.concepts = {}
        self.all_concept_ids = set()
        if 'concepts' in self.data:
            for concept in self.data['concepts']:
                if 'concept_id' in concept:
                    self.concepts[concept['concept_id']] = concept
                    self.all_concept_ids.add(concept['concept_id'])
    
    def fix_missing_prerequisites(self):
        """修复缺失的先决条件 - 移除不存在的先决条件引用"""
        removed_prereqs = defaultdict(list)
        
        for concept_id, concept in self.concepts.items():
            if 'prerequisites' in concept:
                valid_prereqs = []
                for prereq in concept['prerequisites']:
                    prereq_id = prereq.get('concept_id')
                    if prereq_id and prereq_id in self.all_concept_ids:
                        valid_prereqs.append(prereq)
                    elif prereq_id:
                        removed_prereqs[concept_id].append(prereq_id)
                
                if len(valid_prereqs) != len(concept['prerequisites']):
                    concept['prerequisites'] = valid_prereqs
                    
        for concept_id, removed in removed_prereqs.items():
            self.changes.append(f"从概念 '{concept_id}' 移除 {len(removed)} 个不存在的先决条件: {removed}")
            self.errors_fixed += len(removed)
            
        print(f"修复了 {len(removed_prereqs)} 个概念的不存在先决条件引用")
        
    def fix_broken_successors(self):
        """修复断裂的后继关系"""
        removed_succs = defaultdict(list)
        
        for concept_id, concept in self.concepts.items():
            if 'successors' in concept:
                valid_succs = []
                for succ in concept['successors']:
                    succ_id = succ.get('concept_id')
                    if succ_id and succ_id in self.all_concept_ids:
                        valid_succs.append(succ)
                    elif succ_id:
                        removed_succs[concept_id].append(succ_id)
                
                if len(valid_succs) != len(concept['successors']):
                    concept['successors'] = valid_succs
                    
        for concept_id, removed in removed_succs.items():
            self.changes.append(f"从概念 '{concept_id}' 移除 {len(removed)} 个不存在的后继引用")
            self.warnings_fixed += len(removed)
            
        print(f"修复了 {len(removed_succs)} 个概念的不存在后继引用")
        
    def ensure_basic_concepts(self):
        """确保基础概念存在（作为根节点）"""
        basic_concepts_needed = [
            ('real_numbers', '实数', '分析学', 1, 10),
            ('set_theory', '集合论', '数论逻辑', 2, 30),
            ('logic', '逻辑', '数论逻辑', 1, 15),
            ('integers', '整数', '数论逻辑', 1, 5),
            ('euclidean_space', '欧几里得空间', '几何拓扑', 1, 10),
        ]
        
        added = []
        for concept_id, name, category, difficulty, hours in basic_concepts_needed:
            if concept_id not in self.all_concept_ids:
                new_concept = {
                    'concept_id': concept_id,
                    'name': name,
                    'category': category,
                    'difficulty': difficulty,
                    'estimated_hours': hours,
                    'prerequisites': [],
                    'successors': []
                }
                self.concepts[concept_id] = new_concept
                self.all_concept_ids.add(concept_id)
                added.append(concept_id)
                self.changes.append(f"添加基础概念: {concept_id} ({name})")
                
        if added:
            print(f"添加了 {len(added)} 个基础概念: {added}")
            
    def fix_orphan_concepts(self):
        """为孤立概念建立合理的连接"""
        orphan_fixes = {
            'real_numbers': {'prereq_of': ['limit', 'topological_space']},
            'set_theory': {'prereq_of': ['group', 'topological_space', 'predicate_logic', 'category_theory']},
            'integers': {'prereq_of': ['divisibility']},
        }
        
        fixed = 0
        for concept_id, connections in orphan_fixes.items():
            if concept_id in self.concepts:
                concept = self.concepts[concept_id]
                for target_id in connections.get('prereq_of', []):
                    if target_id in self.concepts:
                        target = self.concepts[target_id]
                        # 添加到目标概念的先决条件
                        if 'prerequisites' not in target:
                            target['prerequisites'] = []
                        if not any(p.get('concept_id') == concept_id for p in target['prerequisites']):
                            target['prerequisites'].append({
                                'concept_id': concept_id,
                                'level': 'L0',
                                'relation': '依赖'
                            })
                            fixed += 1
                            
        print(f"修复了 {fixed} 个概念连接")
        
    def standardize_fields(self):
        """标准化字段格式"""
        for concept_id, concept in self.concepts.items():
            # 确保所有概念都有prerequisites和successors字段
            if 'prerequisites' not in concept:
                concept['prerequisites'] = []
            if 'successors' not in concept:
                concept['successors'] = []
                
            # 标准化难度值
            if 'difficulty' in concept:
                try:
                    concept['difficulty'] = int(concept['difficulty'])
                    if concept['difficulty'] < 1:
                        concept['difficulty'] = 1
                    elif concept['difficulty'] > 5:
                        concept['difficulty'] = 5
                except:
                    concept['difficulty'] = 3
                    
            # 标准化学习时长
            if 'estimated_hours' in concept:
                try:
                    concept['estimated_hours'] = int(concept['estimated_hours'])
                    if concept['estimated_hours'] < 1:
                        concept['estimated_hours'] = 10
                    elif concept['estimated_hours'] > 200:
                        concept['estimated_hours'] = 200
                except:
                    concept['estimated_hours'] = 30
    
    def save_fixed_graph(self):
        """保存修正后的概念图谱"""
        output_file = self.project_dir / 'concept_prerequisites_fixed.yaml'
        
        # 构建输出数据
        output_data = {
            'metadata': {
                'title': 'FormalMath 核心数学概念前置关系数据库',
                'version': '3.1-fixed',
                'generated_date': datetime.now().strftime('%Y-%m-%d'),
                'total_concepts': len(self.concepts),
                'fix_notes': f'修复了 {self.errors_fixed} 个错误和 {self.warnings_fixed} 个警告'
            },
            'concepts': list(self.concepts.values())
        }
        
        with open(output_file, 'w', encoding='utf-8') as f:
            yaml.dump(output_data, f, allow_unicode=True, sort_keys=False, default_flow_style=False)
            
        print(f"修正后的概念图谱已保存至: {output_file}")
        return output_file
        
    def generate_quality_report(self):
        """生成数据质量报告"""
        report = []
        report.append("=" * 80)
        report.append("概念图谱数据质量报告")
        report.append(f"生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        report.append("=" * 80)
        
        # 基础统计
        report.append("\n## 基础统计")
        report.append(f"- 总概念数: {len(self.concepts)}")
        report.append(f"- 错误修复数: {self.errors_fixed}")
        report.append(f"- 警告修复数: {self.warnings_fixed}")
        
        # 分类统计
        categories = defaultdict(int)
        total_hours = 0
        difficulty_dist = defaultdict(int)
        
        for concept in self.concepts.values():
            cat = concept.get('category', '未分类')
            categories[cat] += 1
            total_hours += concept.get('estimated_hours', 0)
            difficulty_dist[concept.get('difficulty', 0)] += 1
            
        report.append("\n## 概念分类分布")
        for cat, count in sorted(categories.items(), key=lambda x: -x[1]):
            report.append(f"- {cat}: {count} 个概念")
            
        report.append(f"\n- 总学习时长: {total_hours} 小时")
        report.append(f"- 平均学习时长: {total_hours / len(self.concepts):.1f} 小时/概念")
        
        report.append("\n## 难度分布")
        for diff in sorted(difficulty_dist.keys()):
            report.append(f"- 难度 {diff}: {difficulty_dist[diff]} 个概念")
        
        # 修复详情
        report.append("\n## 修复详情")
        for change in self.changes[:50]:
            report.append(f"- {change}")
        if len(self.changes) > 50:
            report.append(f"... 还有 {len(self.changes) - 50} 项修复")
        
        # 质量评估
        report.append("\n## 质量评估")
        remaining_issues = 207 - self.errors_fixed + 189 - self.warnings_fixed
        if remaining_issues < 50:
            quality = "优秀"
        elif remaining_issues < 100:
            quality = "良好"
        elif remaining_issues < 150:
            quality = "合格"
        else:
            quality = "需改进"
            
        report.append(f"- 剩余问题数: {remaining_issues}")
        report.append(f"- 数据质量: {quality}")
        
        report.append("\n" + "=" * 80)
        
        # 保存报告
        report_file = self.project_dir / 'data_quality_report.md'
        with open(report_file, 'w', encoding='utf-8') as f:
            f.write('\n'.join(report))
            
        print(f"数据质量报告已保存至: {report_file}")
        return report_file
        
    def run_fix(self):
        """运行修复流程"""
        print("开始修复概念图谱...\n")
        
        self.load_data()
        self.ensure_basic_concepts()
        self.fix_missing_prerequisites()
        self.fix_broken_successors()
        self.fix_orphan_concepts()
        self.standardize_fields()
        
        fixed_file = self.save_fixed_graph()
        report_file = self.generate_quality_report()
        
        print(f"\n修复完成!")
        print(f"  - 修复错误: {self.errors_fixed}")
        print(f"  - 修复警告: {self.warnings_fixed}")
        print(f"  - 修正文件: {fixed_file}")
        print(f"  - 质量报告: {report_file}")
        
        return fixed_file, report_file


if __name__ == '__main__':
    project_dir = Path(__file__).parent
    fixer = ConceptGraphFixer(project_dir)
    fixer.run_fix()
