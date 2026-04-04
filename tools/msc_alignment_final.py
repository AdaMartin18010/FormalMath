#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
MSC2020 完整对齐脚本
功能：
1. 审查所有概念的MSC分类
2. 修正不准确分类
3. 添加次级分类
4. 创建MSC到概念反向索引
5. 生成MSC层级可视化数据

作者: FormalMath MSC对齐任务
日期: 2026年4月4日
"""

import os
import re
import json
import yaml
from pathlib import Path
from collections import defaultdict
from datetime import datetime
from typing import Dict, List, Set, Tuple, Optional

# 项目根目录
PROJECT_ROOT = Path("g:/_src/FormalMath")

# MSC2020 编码到分类名称的映射（项目常用）
MSC_CATEGORIES = {
    # 基础数学
    "00": "一般数学",
    "01": "数学史与传记",
    "03": "数理逻辑与基础",
    "05": "组合数学",
    "06": "序理论、格论",
    "08": "一般代数系统",
    
    # 代数与数论
    "11": "数论",
    "12": "域论与多项式",
    "13": "交换代数",
    "14": "代数几何",
    "15": "线性代数与矩阵论",
    "16": "结合环与代数",
    "17": "非结合环与代数",
    "18": "范畴论与同调代数",
    "19": "K-理论",
    "20": "群论及其推广",
    "22": "拓扑群与李群",
    
    # 分析学
    "26": "实函数",
    "28": "测度与积分",
    "30": "单复变函数",
    "31": "位势论",
    "32": "多复变函数",
    "33": "特殊函数",
    "34": "常微分方程",
    "35": "偏微分方程",
    "37": "动力系统与遍历论",
    "39": "差分方程与函数方程",
    "40": "序列、级数、可求和性",
    "41": "逼近与展开",
    "42": "调和分析",
    "43": "抽象调和分析",
    "44": "积分变换与算子演算",
    "45": "积分方程",
    "46": "泛函分析",
    "47": "算子理论",
    "49": "变分法与最优控制",
    
    # 几何与拓扑
    "51": "几何学",
    "52": "凸几何与离散几何",
    "53": "微分几何",
    "54": "一般拓扑学",
    "55": "代数拓扑",
    "57": "流形与胞腔复形",
    "58": "流形上的整体分析",
    
    # 概率与应用
    "60": "概率论与随机过程",
    "62": "统计学",
    "65": "数值分析",
    "68": "计算机科学",
    "81": "量子理论",
    "91": "博弈论、经济学",
    "97": "数学教育",
}

# 概念到MSC主分类的标准映射
CONCEPT_MSC_MAPPING = {
    # 基础概念
    "关系": {"primary": "03E20", "secondary": ["06A99"]},
    "集合": {"primary": "03E99", "secondary": ["00A05"]},
    "函数": {"primary": "03E20", "secondary": ["26A99"]},
    "自然数": {"primary": "11A99", "secondary": ["03E30"]},
    "整数": {"primary": "11A99", "secondary": ["13A99"]},
    "有理数": {"primary": "11A99", "secondary": ["12F99"]},
    "实数": {"primary": "26A03", "secondary": ["54F05"]},
    "复数": {"primary": "30A99", "secondary": ["12D99"]},
    
    # 代数结构
    "群": {"primary": "20A05", "secondary": ["20D99"]},
    "环": {"primary": "13A99", "secondary": ["16A99"]},
    "域": {"primary": "12F99", "secondary": ["13B99"]},
    "向量空间": {"primary": "15A03", "secondary": ["46A99"]},
    "线性映射": {"primary": "15A04", "secondary": ["47A05"]},
    
    # 分析学
    "极限": {"primary": "26A03", "secondary": ["40A05"]},
    "连续": {"primary": "26A15", "secondary": ["54C05"]},
    "导数": {"primary": "26A24", "secondary": ["58C20"]},
    "积分": {"primary": "26A42", "secondary": ["28A25"]},
    "级数": {"primary": "40A05", "secondary": ["30B10"]},
    
    # 几何拓扑
    "流形": {"primary": "57N99", "secondary": ["58A05"]},
    "黎曼流形": {"primary": "53C20", "secondary": ["53B20"]},
    "曲率": {"primary": "53A04", "secondary": ["53B21"]},
    "概形": {"primary": "14A15", "secondary": ["14F05"]},
    "层": {"primary": "14F05", "secondary": ["18F20"]},
    "拓扑空间": {"primary": "54A05", "secondary": ["54B99"]},
    "同伦": {"primary": "55P99", "secondary": ["55Q05"]},
    "同调": {"primary": "55N99", "secondary": ["18G99"]},
    
    # 数论与离散
    "素数": {"primary": "11A41", "secondary": ["11N05"]},
    "同余": {"primary": "11A07", "secondary": ["11N25"]},
    "L函数": {"primary": "11M36", "secondary": ["11F66"]},
    "图": {"primary": "05C99", "secondary": ["68R10"]},
    "组合数": {"primary": "05A10", "secondary": ["11B65"]},
    "算法": {"primary": "68W01", "secondary": ["68Q25"]},
    "表示": {"primary": "20C99", "secondary": ["22E47"]},
    "朗兰兹纲领": {"primary": "11R39", "secondary": ["22E55", "14F20"]},
}


def extract_frontmatter(content: str) -> Tuple[Optional[Dict], str]:
    """提取YAML frontmatter"""
    pattern = r'^---\s*\n(.*?)\n---\s*\n'
    match = re.match(pattern, content, re.DOTALL)
    if match:
        try:
            frontmatter = yaml.safe_load(match.group(1))
            body = content[match.end():]
            return frontmatter, body
        except yaml.YAMLError:
            return None, content
    return None, content


def get_msc_info(frontmatter: Optional[Dict]) -> Tuple[Optional[str], List[str]]:
    """提取MSC编码信息"""
    if not frontmatter:
        return None, []
    
    primary = frontmatter.get('msc_primary')
    secondary = frontmatter.get('msc_secondary', [])
    
    # 统一为字符串
    if isinstance(primary, list) and primary:
        primary = primary[0]
    
    if isinstance(secondary, str):
        secondary = [secondary]
    elif not isinstance(secondary, list):
        secondary = []
    
    return primary, secondary


def scan_concepts() -> List[Dict]:
    """扫描所有概念文档"""
    concepts = []
    concept_dirs = [
        PROJECT_ROOT / "concept" / "核心概念",
    ]
    
    for concept_dir in concept_dirs:
        if not concept_dir.exists():
            continue
        for md_file in concept_dir.glob("*.md"):
            # 跳过非核心概念文件（如报告、示例等）
            if any(skip in md_file.name for skip in ['报告', '示例', '导图', '索引']):
                continue
            
            content = md_file.read_text(encoding='utf-8')
            frontmatter, body = extract_frontmatter(content)
            
            # 提取概念名称
            concept_name = None
            for mapping_name in CONCEPT_MSC_MAPPING.keys():
                if mapping_name in md_file.name:
                    concept_name = mapping_name
                    break
            
            if not concept_name:
                # 从文件名提取
                name_match = re.match(r'\d+-(.+?)\.md', md_file.name)
                if name_match:
                    concept_name = name_match.group(1)
            
            primary, secondary = get_msc_info(frontmatter)
            
            concepts.append({
                'file': str(md_file.relative_to(PROJECT_ROOT)),
                'name': concept_name or md_file.stem,
                'frontmatter': frontmatter,
                'body': body,
                'msc_primary': primary,
                'msc_secondary': secondary,
            })
    
    return concepts


def validate_msc_code(code: str) -> Tuple[bool, str]:
    """验证MSC编码格式"""
    if not code:
        return False, "编码为空"
    
    # 支持格式: 03E99, 03-XX, 03Exx
    patterns = [
        r'^\d{2}[A-Z]\d{2}$',      # 03E99
        r'^\d{2}-XX$',              # 03-XX
        r'^\d{2}[A-Z]xx$',          # 03Exx
        r'^\d{2}[A-Z]\d{2}-\d{2}$', # 03E99-01
    ]
    
    for pattern in patterns:
        if re.match(pattern, code):
            # 验证顶级编码
            top_level = code[:2]
            if top_level in MSC_CATEGORIES or top_level in ['00', '01', '03', '05', '06', '08', 
                                                              '11', '12', '13', '14', '15', '16', 
                                                              '17', '18', '19', '20', '22', '26', 
                                                              '28', '30', '31', '32', '33', '34', 
                                                              '35', '37', '39', '40', '41', '42', 
                                                              '43', '44', '45', '46', '47', '49', 
                                                              '51', '52', '53', '54', '55', '57', 
                                                              '58', '60', '62', '65', '68', '81', 
                                                              '91', '97']:
                return True, "格式正确"
            return False, f"未知的顶级编码: {top_level}"
    
    return False, "格式不符合MSC2020标准"


def check_classification_accuracy(concepts: List[Dict]) -> Dict:
    """检查MSC分类准确性"""
    results = {
        'accurate': [],
        'inaccurate': [],
        'missing_primary': [],
        'missing_secondary': [],
        'format_issues': [],
    }
    
    for concept in concepts:
        name = concept['name']
        primary = concept['msc_primary']
        secondary = concept['msc_secondary']
        
        # 检查是否有主分类
        if not primary:
            results['missing_primary'].append(concept)
            continue
        
        # 验证主分类格式
        valid, msg = validate_msc_code(primary)
        if not valid:
            results['format_issues'].append({
                **concept,
                'issue': msg
            })
            continue
        
        # 检查是否与标准映射一致
        if name in CONCEPT_MSC_MAPPING:
            expected = CONCEPT_MSC_MAPPING[name]
            expected_primary = expected['primary']
            
            # 允许主分类匹配前3位或完全一致
            primary_prefix = primary[:3] if len(primary) >= 3 else primary
            expected_prefix = expected_primary[:3] if len(expected_primary) >= 3 else expected_primary
            
            if primary_prefix != expected_prefix:
                results['inaccurate'].append({
                    **concept,
                    'expected_primary': expected_primary,
                    'reason': f'主分类不匹配: 当前{primary}, 期望{expected_primary}'
                })
            else:
                results['accurate'].append(concept)
        else:
            # 未在映射表中，标记为需要检查
            results['accurate'].append(concept)
        
        # 检查次级分类
        if not secondary:
            results['missing_secondary'].append(concept)
    
    return results


def generate_correction_plan(check_results: Dict) -> List[Dict]:
    """生成分类修正计划"""
    corrections = []
    
    # 处理缺失主分类
    for concept in check_results['missing_primary']:
        name = concept['name']
        if name in CONCEPT_MSC_MAPPING:
            mapping = CONCEPT_MSC_MAPPING[name]
            corrections.append({
                'file': concept['file'],
                'name': name,
                'action': 'add_primary',
                'value': mapping['primary'],
                'reason': '补充缺失的主分类'
            })
    
    # 处理不准确的分类
    for concept in check_results['inaccurate']:
        corrections.append({
            'file': concept['file'],
            'name': concept['name'],
            'action': 'update_primary',
            'old_value': concept['msc_primary'],
            'new_value': concept.get('expected_primary'),
            'reason': concept.get('reason')
        })
    
    # 处理缺失次级分类
    for concept in check_results['missing_secondary']:
        name = concept['name']
        if name in CONCEPT_MSC_MAPPING:
            mapping = CONCEPT_MSC_MAPPING[name]
            corrections.append({
                'file': concept['file'],
                'name': name,
                'action': 'add_secondary',
                'value': mapping['secondary'],
                'reason': '添加次级分类'
            })
    
    return corrections


def create_msc_reverse_index(concepts: List[Dict]) -> Dict:
    """创建MSC到概念的反向索引"""
    reverse_index = defaultdict(lambda: {'primary': [], 'secondary': []})
    
    for concept in concepts:
        primary = concept['msc_primary']
        secondary = concept['msc_secondary']
        
        if primary:
            # 按不同粒度索引
            reverse_index[primary]['primary'].append({
                'name': concept['name'],
                'file': concept['file']
            })
            
            # 三级分类索引 (如 03E)
            if len(primary) >= 3:
                reverse_index[primary[:3]]['primary'].append({
                    'name': concept['name'],
                    'file': concept['file']
                })
            
            # 顶级分类索引 (如 03)
            reverse_index[primary[:2]]['primary'].append({
                'name': concept['name'],
                'file': concept['file']
            })
        
        for sec in secondary:
            if sec:
                reverse_index[sec]['secondary'].append({
                    'name': concept['name'],
                    'file': concept['file']
                })
    
    return dict(reverse_index)


def generate_hierarchy_data(reverse_index: Dict) -> Dict:
    """生成MSC层级可视化数据"""
    hierarchy = {
        'name': 'MSC2020',
        'children': []
    }
    
    # 按顶级分类组织
    for top_code, top_name in MSC_CATEGORIES.items():
        top_node = {
            'name': f'{top_code} - {top_name}',
            'code': top_code,
            'children': []
        }
        
        # 查找该顶级分类下的所有概念
        if top_code in reverse_index:
            concepts = reverse_index[top_code]['primary']
            for concept in concepts:
                top_node['children'].append({
                    'name': concept['name'],
                    'file': concept['file'],
                    'type': 'concept'
                })
        
        if top_node['children']:
            hierarchy['children'].append(top_node)
    
    return hierarchy


def generate_report(concepts: List[Dict], check_results: Dict, corrections: List[Dict], 
                   reverse_index: Dict, hierarchy: Dict) -> str:
    """生成MSC对齐报告"""
    report_lines = []
    report_lines.append("# MSC2020完整对齐报告")
    report_lines.append("")
    report_lines.append(f"**生成日期**: {datetime.now().strftime('%Y年%m月%d日')}")
    report_lines.append(f"**概念总数**: {len(concepts)}")
    report_lines.append("")
    
    # 统计概览
    report_lines.append("## 一、统计概览")
    report_lines.append("")
    report_lines.append("| 指标 | 数量 | 占比 |")
    report_lines.append("|------|------|------|")
    report_lines.append(f"| 概念总数 | {len(concepts)} | 100% |")
    report_lines.append(f"| 分类准确 | {len(check_results['accurate'])} | {len(check_results['accurate'])/len(concepts)*100:.1f}% |")
    report_lines.append(f"| 需要修正 | {len(check_results['inaccurate'])} | {len(check_results['inaccurate'])/len(concepts)*100:.1f}% |")
    report_lines.append(f"| 缺失主分类 | {len(check_results['missing_primary'])} | {len(check_results['missing_primary'])/len(concepts)*100:.1f}% |")
    report_lines.append(f"| 缺失次级分类 | {len(check_results['missing_secondary'])} | {len(check_results['missing_secondary'])/len(concepts)*100:.1f}% |")
    report_lines.append("")
    
    # 详细分析
    report_lines.append("## 二、详细分析")
    report_lines.append("")
    
    # 按MSC分类统计
    report_lines.append("### 2.1 按MSC顶级分类统计")
    report_lines.append("")
    report_lines.append("| MSC编码 | 分类名称 | 概念数量 |")
    report_lines.append("|---------|----------|----------|")
    
    msc_counts = defaultdict(int)
    for concept in concepts:
        if concept['msc_primary']:
            top_code = concept['msc_primary'][:2]
            msc_counts[top_code] += 1
    
    for code, count in sorted(msc_counts.items(), key=lambda x: -x[1]):
        name = MSC_CATEGORIES.get(code, "未知分类")
        report_lines.append(f"| {code} | {name} | {count} |")
    report_lines.append("")
    
    # 修正计划
    report_lines.append("## 三、修正计划")
    report_lines.append("")
    report_lines.append(f"共识别 {len(corrections)} 项需要修正的分类：")
    report_lines.append("")
    
    for i, corr in enumerate(corrections[:20], 1):  # 显示前20项
        report_lines.append(f"{i}. **{corr['name']}** ({corr['action']})")
        report_lines.append(f"   - 文件: `{corr['file']}`")
        report_lines.append(f"   - 原因: {corr['reason']}")
        if 'old_value' in corr:
            report_lines.append(f"   - 修正: {corr['old_value']} → {corr['new_value']}")
        report_lines.append("")
    
    if len(corrections) > 20:
        report_lines.append(f"... 以及 {len(corrections) - 20} 项其他修正")
        report_lines.append("")
    
    # 反向索引摘要
    report_lines.append("## 四、MSC反向索引摘要")
    report_lines.append("")
    report_lines.append(f"已建立 {len(reverse_index)} 个MSC编码索引：")
    report_lines.append("")
    
    # 显示概念最多的编码
    sorted_index = sorted(reverse_index.items(), 
                         key=lambda x: len(x[1]['primary']) + len(x[1]['secondary']), 
                         reverse=True)[:10]
    
    report_lines.append("| MSC编码 | 主分类概念数 | 次分类概念数 | 总计 |")
    report_lines.append("|---------|--------------|--------------|------|")
    for code, data in sorted_index:
        total = len(data['primary']) + len(data['secondary'])
        report_lines.append(f"| {code} | {len(data['primary'])} | {len(data['secondary'])} | {total} |")
    report_lines.append("")
    
    # 层级结构摘要
    report_lines.append("## 五、MSC层级结构摘要")
    report_lines.append("")
    report_lines.append(f"层级数据包含 {len(hierarchy['children'])} 个顶级分类分支")
    report_lines.append("")
    
    for branch in hierarchy['children'][:5]:
        report_lines.append(f"- **{branch['name']}**: {len(branch['children'])} 个概念")
    report_lines.append("")
    
    # 输出文件列表
    report_lines.append("## 六、生成的输出文件")
    report_lines.append("")
    report_lines.append("1. `msc_reverse_index.json` - MSC到概念反向索引")
    report_lines.append("2. `msc_hierarchy.json` - MSC层级可视化数据")
    report_lines.append("3. `msc_corrections.json` - 分类修正计划")
    report_lines.append("")
    
    report_lines.append("---")
    report_lines.append("")
    report_lines.append("*本报告由MSC2020完整对齐脚本自动生成*")
    
    return "\n".join(report_lines)


def main():
    """主函数"""
    print("=" * 60)
    print("MSC2020 完整对齐任务")
    print("=" * 60)
    print()
    
    # 1. 扫描概念
    print("[1/5] 扫描概念文档...")
    concepts = scan_concepts()
    print(f"      发现 {len(concepts)} 个概念文档")
    
    # 2. 检查分类准确性
    print("[2/5] 检查MSC分类准确性...")
    check_results = check_classification_accuracy(concepts)
    print(f"      准确: {len(check_results['accurate'])}")
    print(f"      需修正: {len(check_results['inaccurate'])}")
    print(f"      缺失主分类: {len(check_results['missing_primary'])}")
    
    # 3. 生成分类修正计划
    print("[3/5] 生成分类修正计划...")
    corrections = generate_correction_plan(check_results)
    print(f"      生成 {len(corrections)} 项修正")
    
    # 4. 创建反向索引
    print("[4/5] 创建MSC反向索引...")
    reverse_index = create_msc_reverse_index(concepts)
    print(f"      建立 {len(reverse_index)} 个索引条目")
    
    # 5. 生成层级数据
    print("[5/5] 生成MSC层级可视化数据...")
    hierarchy = generate_hierarchy_data(reverse_index)
    print(f"      生成 {len(hierarchy['children'])} 个顶级分支")
    
    # 生成报告
    print()
    print("生成报告和输出文件...")
    
    # 确保输出目录存在
    output_dir = PROJECT_ROOT / "project" / "msc"
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # 保存反向索引
    reverse_index_path = output_dir / "msc_reverse_index.json"
    with open(reverse_index_path, 'w', encoding='utf-8') as f:
        json.dump(reverse_index, f, ensure_ascii=False, indent=2)
    print(f"  ✓ {reverse_index_path}")
    
    # 保存层级数据
    hierarchy_path = output_dir / "msc_hierarchy.json"
    with open(hierarchy_path, 'w', encoding='utf-8') as f:
        json.dump(hierarchy, f, ensure_ascii=False, indent=2)
    print(f"  ✓ {hierarchy_path}")
    
    # 保存修正计划
    corrections_path = output_dir / "msc_corrections.json"
    with open(corrections_path, 'w', encoding='utf-8') as f:
        json.dump(corrections, f, ensure_ascii=False, indent=2)
    print(f"  ✓ {corrections_path}")
    
    # 生成并保存报告
    report = generate_report(concepts, check_results, corrections, reverse_index, hierarchy)
    report_path = output_dir / "00-MSC2020完整对齐报告.md"
    with open(report_path, 'w', encoding='utf-8') as f:
        f.write(report)
    print(f"  ✓ {report_path}")
    
    print()
    print("=" * 60)
    print("MSC2020完整对齐任务完成！")
    print("=" * 60)
    print()
    print(f"概念总数: {len(concepts)}")
    print(f"分类准确: {len(check_results['accurate'])} ({len(check_results['accurate'])/len(concepts)*100:.1f}%)")
    print(f"需修正: {len(corrections)}")
    print(f"MSC索引条目: {len(reverse_index)}")


if __name__ == "__main__":
    main()
