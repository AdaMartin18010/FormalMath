#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
概念图谱准确性验证脚本
验证400个概念的图谱数据质量
"""

import yaml
import json
import re
from collections import defaultdict
from datetime import datetime
from pathlib import Path

class ConceptGraphValidator:
    def __init__(self, project_dir):
        self.project_dir = Path(project_dir)
        self.errors = []
        self.warnings = []
        self.stats = {
            'total_concepts': 0,
            'valid_concepts': 0,
            'invalid_concepts': 0,
            'missing_prerequisites': 0,
            'orphan_concepts': 0,
            'difficulty_issues': 0,
            'hours_issues': 0
        }
        self.concepts = {}
        self.all_concept_ids = set()
        
    def load_data(self):
        """加载所有概念数据"""
        # 加载主要概念图谱
        yaml_file = self.project_dir / 'concept_prerequisites_400.yaml'
        with open(yaml_file, 'r', encoding='utf-8') as f:
            self.data = yaml.safe_load(f)
        
        # 加载统计数据
        stats_file = self.project_dir / 'concept_statistics_400.json'
        with open(stats_file, 'r', encoding='utf-8') as f:
            self.statistics = json.load(f)
        
        # 加载多语言术语表
        multilang_file = self.project_dir / 'multilang_terminology_table.json'
        with open(multilang_file, 'r', encoding='utf-8') as f:
            self.multilang = json.load(f)
            
        # 加载统一概念图谱
        unified_file = self.project_dir / 'unified_concept_graph.yaml'
        with open(unified_file, 'r', encoding='utf-8') as f:
            self.unified = yaml.safe_load(f)
        
        # 提取所有概念
        if 'concepts' in self.data:
            for concept in self.data['concepts']:
                if 'concept_id' in concept:
                    self.concepts[concept['concept_id']] = concept
                    self.all_concept_ids.add(concept['concept_id'])
        
        self.stats['total_concepts'] = len(self.concepts)
        
    def validate_concept_definitions(self):
        """验证概念定义"""
        print("\n=== 1. 概念定义验证 ===")
        
        required_fields = ['concept_id', 'name', 'category', 'difficulty', 'estimated_hours']
        valid_categories = {
            '分析学', '代数学', '几何拓扑', '数论逻辑', '概率统计', 
            '最优化', '控制论', '信息论', '密码学', '金融数学',
            '生物数学', '计算数学', '物理数学', '数据科学',
            '范畴论', '同调代数', '代数几何', '表示论', 
            '数论高级', '动力系统', '数理逻辑'
        }
        
        for concept_id, concept in self.concepts.items():
            # 检查必需字段
            for field in required_fields:
                if field not in concept:
                    self.errors.append(f"概念 '{concept_id}' 缺少必需字段: {field}")
                    
            # 验证分类
            if 'category' in concept and concept['category'] not in valid_categories:
                self.warnings.append(f"概念 '{concept_id}' 使用了非标准分类: {concept['category']}")
                
            # 验证名称
            if 'name' in concept:
                if not concept['name'] or len(concept['name']) < 1:
                    self.errors.append(f"概念 '{concept_id}' 名称为空")
                    
            # 验证ID格式
            if not re.match(r'^[a-z][a-z_0-9]*$', concept_id):
                self.warnings.append(f"概念ID '{concept_id}' 格式不符合规范(应使用小写字母和下划线)")
        
        print(f"  - 已验证 {len(self.concepts)} 个概念定义")
        print(f"  - 发现 {len([e for e in self.errors if '缺少必需字段' in e])} 个缺少字段错误")
        
    def validate_dependencies(self):
        """验证依赖关系"""
        print("\n=== 2. 依赖关系验证 ===")
        
        # 检查先决条件是否存在
        missing_prereqs = defaultdict(list)
        broken_successors = defaultdict(list)
        
        for concept_id, concept in self.concepts.items():
            # 验证先决条件
            if 'prerequisites' in concept:
                for prereq in concept['prerequisites']:
                    prereq_id = prereq.get('concept_id')
                    if prereq_id and prereq_id not in self.all_concept_ids:
                        missing_prereqs[concept_id].append(prereq_id)
                        self.stats['missing_prerequisites'] += 1
                        
            # 验证后继概念
            if 'successors' in concept:
                for succ in concept['successors']:
                    succ_id = succ.get('concept_id')
                    if succ_id and succ_id not in self.all_concept_ids:
                        broken_successors[concept_id].append(succ_id)
        
        # 检查循环依赖
        cycles = self._detect_cycles()
        
        if missing_prereqs:
            for concept_id, missing in missing_prereqs.items():
                self.errors.append(f"概念 '{concept_id}' 引用了不存在的先决条件: {missing}")
                
        if broken_successors:
            for concept_id, broken in broken_successors.items():
                self.warnings.append(f"概念 '{concept_id}' 引用了不存在的后继概念: {broken}")
                
        if cycles:
            for cycle in cycles:
                self.errors.append(f"检测到循环依赖: {' -> '.join(cycle)}")
        
        # 检查孤立概念
        orphan_concepts = []
        for concept_id, concept in self.concepts.items():
            has_prereq = bool(concept.get('prerequisites'))
            has_succ = bool(concept.get('successors'))
            if not has_prereq and not has_succ:
                orphan_concepts.append(concept_id)
                self.stats['orphan_concepts'] += 1
        
        if orphan_concepts:
            self.warnings.append(f"发现 {len(orphan_concepts)} 个孤立概念(无依赖关系)")
        
        print(f"  - 发现 {len(missing_prereqs)} 个概念引用不存在的先决条件")
        print(f"  - 发现 {len(cycles)} 个循环依赖")
        print(f"  - 发现 {len(orphan_concepts)} 个孤立概念")
        
    def _detect_cycles(self):
        """检测循环依赖"""
        visited = set()
        rec_stack = set()
        cycles = []
        
        def dfs(node, path):
            if node not in self.concepts:
                return None
                
            visited.add(node)
            rec_stack.add(node)
            path.append(node)
            
            concept = self.concepts.get(node, {})
            if 'prerequisites' in concept:
                for prereq in concept['prerequisites']:
                    prereq_id = prereq.get('concept_id')
                    if prereq_id and prereq_id in self.concepts:
                        if prereq_id not in visited:
                            result = dfs(prereq_id, path)
                            if result:
                                return result
                        elif prereq_id in rec_stack:
                            try:
                                cycle_start = path.index(prereq_id)
                                return path[cycle_start:] + [prereq_id]
                            except ValueError:
                                pass
            
            path.pop()
            rec_stack.remove(node)
            return None
        
        for concept_id in list(self.all_concept_ids):
            if concept_id not in visited and concept_id in self.concepts:
                cycle = dfs(concept_id, [])
                if cycle:
                    cycles.append(cycle)
                    
        return cycles
        
    def validate_attributes(self):
        """验证属性值"""
        print("\n=== 3. 属性验证 ===")
        
        difficulty_issues = 0
        hours_issues = 0
        
        for concept_id, concept in self.concepts.items():
            # 验证难度级别
            if 'difficulty' in concept:
                diff = concept['difficulty']
                if not isinstance(diff, int) or diff < 1 or diff > 5:
                    self.warnings.append(f"概念 '{concept_id}' 难度级别异常: {diff} (应在1-5之间)")
                    difficulty_issues += 1
                    
            # 验证学习时长
            if 'estimated_hours' in concept:
                hours = concept['estimated_hours']
                if not isinstance(hours, int) or hours < 1 or hours > 200:
                    self.warnings.append(f"概念 '{concept_id}' 学习时长异常: {hours}")
                    hours_issues += 1
                    
            # 验证级别
            if 'prerequisites' in concept:
                for prereq in concept['prerequisites']:
                    level = prereq.get('level', '')
                    if level and not re.match(r'^L[0-5]$', level):
                        self.warnings.append(f"概念 '{concept_id}' 的先决条件级别格式异常: {level}")
                        
        self.stats['difficulty_issues'] = difficulty_issues
        self.stats['hours_issues'] = hours_issues
        
        print(f"  - 发现 {difficulty_issues} 个难度级别问题")
        print(f"  - 发现 {hours_issues} 个学习时长问题")
        
    def validate_cross_references(self):
        """验证跨引用"""
        print("\n=== 4. 跨引用验证 ===")
        
        # 验证与统一概念图谱的一致性
        unified_concepts = {}
        if self.unified and 'concepts' in self.unified:
            for concept in self.unified['concepts']:
                if 'concept_id' in concept:
                    unified_concepts[concept['concept_id']] = concept
        
        inconsistent = 0
        for concept_id, concept in self.concepts.items():
            if concept_id in unified_concepts:
                unified = unified_concepts[concept_id]
                # 检查名称一致性
                if concept.get('name') != unified.get('name'):
                    self.warnings.append(f"概念 '{concept_id}' 名称不一致: {concept.get('name')} vs {unified.get('name')}")
                    inconsistent += 1
                # 检查分类一致性
                if concept.get('category') != unified.get('category'):
                    self.warnings.append(f"概念 '{concept_id}' 分类不一致: {concept.get('category')} vs {unified.get('category')}")
                    inconsistent += 1
        
        # 验证多语言术语
        multilang_coverage = 0
        terminology = self.multilang.get('terminology', {})
        for concept_id in self.concepts:
            if concept_id in terminology:
                multilang_coverage += 1
                
        # 验证Wikipedia链接
        wiki_coverage = 0
        for concept in unified_concepts.values():
            if concept.get('wikipedia_link'):
                wiki_coverage += 1
                
        print(f"  - 与统一概念图谱不一致: {inconsistent} 处")
        print(f"  - 多语言术语覆盖: {multilang_coverage}/{len(self.concepts)} ({multilang_coverage/len(self.concepts)*100:.1f}%)")
        print(f"  - Wikipedia链接覆盖: {wiki_coverage}/{len(unified_concepts)} ({wiki_coverage/len(unified_concepts)*100:.1f}%)")
        
    def generate_report(self):
        """生成验证报告"""
        report = []
        report.append("=" * 80)
        report.append("概念图谱验证报告")
        report.append(f"生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        report.append("=" * 80)
        
        # 统计信息
        report.append("\n## 统计信息")
        report.append(f"- 总概念数: {self.stats['total_concepts']}")
        report.append(f"- 错误数: {len(self.errors)}")
        report.append(f"- 警告数: {len(self.warnings)}")
        
        # 错误详情
        if self.errors:
            report.append("\n## 错误详情")
            for i, error in enumerate(self.errors[:50], 1):  # 最多显示50个错误
                report.append(f"{i}. [错误] {error}")
            if len(self.errors) > 50:
                report.append(f"... 还有 {len(self.errors) - 50} 个错误")
        
        # 警告详情
        if self.warnings:
            report.append("\n## 警告详情")
            for i, warning in enumerate(self.warnings[:50], 1):  # 最多显示50个警告
                report.append(f"{i}. [警告] {warning}")
            if len(self.warnings) > 50:
                report.append(f"... 还有 {len(self.warnings) - 50} 个警告")
        
        # 数据质量评分
        report.append("\n## 数据质量评分")
        total_issues = len(self.errors) + len(self.warnings)
        max_score = 100
        deduction = min(total_issues * 0.5, 50)  # 每个问题扣0.5分，最多扣50分
        score = max_score - deduction
        
        if score >= 90:
            quality = "优秀"
        elif score >= 80:
            quality = "良好"
        elif score >= 70:
            quality = "合格"
        else:
            quality = "需改进"
            
        report.append(f"- 质量评分: {score:.1f}/100")
        report.append(f"- 质量等级: {quality}")
        
        # 建议
        report.append("\n## 改进建议")
        if self.errors:
            report.append("1. 优先修复概念定义错误")
        if self.stats['missing_prerequisites'] > 0:
            report.append("2. 补充缺失的先决条件概念定义")
        if self.stats['orphan_concepts'] > 0:
            report.append("3. 为孤立概念建立适当的依赖关系")
        if len(self.warnings) > 20:
            report.append("4. 审查并修正属性值异常")
        
        report.append("\n" + "=" * 80)
        
        return '\n'.join(report)
        
    def run_validation(self):
        """运行完整验证"""
        print("开始验证概念图谱...")
        
        self.load_data()
        self.validate_concept_definitions()
        self.validate_dependencies()
        self.validate_attributes()
        self.validate_cross_references()
        
        report = self.generate_report()
        
        # 保存报告
        report_file = self.project_dir / 'concept_graph_validation_report.md'
        with open(report_file, 'w', encoding='utf-8') as f:
            f.write(report)
        
        print(f"\n验证完成！")
        print(f"报告已保存至: {report_file}")
        print(f"错误数: {len(self.errors)}, 警告数: {len(self.warnings)}")
        
        return report


if __name__ == '__main__':
    project_dir = Path(__file__).parent
    validator = ConceptGraphValidator(project_dir)
    validator.run_validation()
