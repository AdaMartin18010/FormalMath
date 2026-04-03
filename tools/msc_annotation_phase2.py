#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath项目MSC编码标注 - 第二阶段
目标：达到500篇标注
"""

import os
import re
from pathlib import Path
from datetime import datetime
from collections import defaultdict

# 扩展MSC映射（包含报告、词典等非核心内容）
EXTENDED_MSC_MAPPING = {
    # 元数据/文档类
    "报告": {"primary": "00A99", "secondary": ["00-XX", "01Axx"]},
    "总结": {"primary": "00A99", "secondary": ["00-XX"]},
    "规范": {"primary": "00A99", "secondary": ["00-XX"]},
    "标准": {"primary": "00A99", "secondary": ["00-XX"]},
    "索引": {"primary": "00A99", "secondary": ["00-XX"]},
    "导航": {"primary": "00A99", "secondary": ["00-XX"]},
    "词典": {"primary": "00A20", "secondary": ["00-XX", "01Axx"]},
    "术语": {"primary": "00A20", "secondary": ["00-XX"]},
    "说明": {"primary": "00A99", "secondary": ["00-XX"]},
    "模板": {"primary": "00A99", "secondary": ["00-XX"]},
    
    # 基础数学
    "基础": {"primary": "00A05", "secondary": ["00-XX", "97-XX"]},
    "集合": {"primary": "03E20", "secondary": ["03Exx"]},
    "ZFC": {"primary": "03E30", "secondary": ["03E25", "03E35"]},
    "公理": {"primary": "03E30", "secondary": ["03-XX"]},
    "数系": {"primary": "00A05", "secondary": ["11-XX"]},
    "自然数": {"primary": "03F30", "secondary": ["03E20"]},
    "测度": {"primary": "28Axx", "secondary": ["26A42"]},
    
    # 代数
    "代数": {"primary": "08-XX", "secondary": ["16-XX"]},
    "群": {"primary": "20-XX", "secondary": ["20Fxx"]},
    "环": {"primary": "16-XX", "secondary": ["13-XX"]},
    "域": {"primary": "12Fxx", "secondary": ["12Exx"]},
    "模": {"primary": "16Dxx", "secondary": ["13Cxx"]},
    "线性": {"primary": "15-XX", "secondary": ["15Axx"]},
    "李代数": {"primary": "17Bxx", "secondary": ["17-XX"]},
    "交换": {"primary": "13-XX", "secondary": ["14-XX"]},
    "同调": {"primary": "18Gxx", "secondary": ["13Dxx"]},
    "范畴": {"primary": "18-XX", "secondary": ["18Axx"]},
    "表示": {"primary": "20Cxx", "secondary": ["22E47"]},
    
    # 分析
    "分析": {"primary": "26-XX", "secondary": ["28-XX"]},
    "实分析": {"primary": "26Axx", "secondary": ["26Bxx"]},
    "复分析": {"primary": "30-XX", "secondary": ["31-XX"]},
    "泛函": {"primary": "46-XX", "secondary": ["47-XX"]},
    "调和": {"primary": "42-XX", "secondary": ["43-XX"]},
    "积分": {"primary": "28-XX", "secondary": ["26A42"]},
    "微分": {"primary": "26A24", "secondary": ["34-XX"]},
    "微分方程": {"primary": "34-XX", "secondary": ["35-XX"]},
    "偏微分": {"primary": "35-XX", "secondary": ["35Axx"]},
    "变分": {"primary": "49-XX", "secondary": ["35A15"]},
    
    # 几何
    "几何": {"primary": "51-XX", "secondary": ["52-XX"]},
    "欧几里得": {"primary": "51Mxx", "secondary": ["51Nxx"]},
    "解析几何": {"primary": "51N20", "secondary": ["14Nxx"]},
    "微分几何": {"primary": "53-XX", "secondary": ["53Axx"]},
    "射影": {"primary": "51A05", "secondary": ["51N15"]},
    "代数几何": {"primary": "14-XX", "secondary": ["14Nxx"]},
    "黎曼": {"primary": "53B20", "secondary": ["53Cxx"]},
    
    # 拓扑
    "拓扑": {"primary": "54-XX", "secondary": ["55-XX"]},
    "点集": {"primary": "54Axx", "secondary": ["54Bxx"]},
    "代数拓扑": {"primary": "55-XX", "secondary": ["55Nxx"]},
    "微分拓扑": {"primary": "57Rxx", "secondary": ["53Cxx"]},
    "同伦": {"primary": "55Pxx", "secondary": ["55Qxx"]},
    "同调论": {"primary": "55Nxx", "secondary": ["18Gxx"]},
    "纤维": {"primary": "55Rxx", "secondary": ["57R22"]},
    "流形": {"primary": "57Nxx", "secondary": ["57Rxx"]},
    
    # 数论
    "数论": {"primary": "11-XX", "secondary": ["11Axx"]},
    "初等": {"primary": "11Axx", "secondary": ["11Bxx"]},
    "解析": {"primary": "11Mxx", "secondary": ["11Nxx"]},
    "代数数论": {"primary": "11Rxx", "secondary": ["11Sxx"]},
    "算术": {"primary": "11Gxx", "secondary": ["11Dxx"]},
    
    # 逻辑
    "逻辑": {"primary": "03-XX", "secondary": ["03Bxx"]},
    "命题": {"primary": "03B05", "secondary": ["03B20"]},
    "谓词": {"primary": "03Cxx", "secondary": ["03B10"]},
    "模型": {"primary": "03Cxx", "secondary": ["03C64"]},
    "证明": {"primary": "03Fxx", "secondary": ["03B35"]},
    "递归": {"primary": "03Dxx", "secondary": ["03D20"]},
    
    # 计算
    "计算": {"primary": "65-XX", "secondary": ["68-XX"]},
    "数值": {"primary": "65Dxx", "secondary": ["65Lxx"]},
    "算法": {"primary": "68Wxx", "secondary": ["68Qxx"]},
    "优化": {"primary": "90Cxx", "secondary": ["49Mxx"]},
    
    # 概率统计
    "概率": {"primary": "60-XX", "secondary": ["60Axx"]},
    "统计": {"primary": "62-XX", "secondary": ["62Fxx"]},
    "随机": {"primary": "60Gxx", "secondary": ["60Hxx"]},
    
    # 形式化
    "形式化": {"primary": "68Vxx", "secondary": ["03B35"]},
    "Lean": {"primary": "68V20", "secondary": ["03B35"]},
    "Coq": {"primary": "68V20", "secondary": ["03B35"]},
    "自动": {"primary": "68T15", "secondary": ["03B35"]},
    
    # 语义
    "语义": {"primary": "03C65", "secondary": ["03C90"]},
    "语法": {"primary": "03B65", "secondary": ["03Cxx"]},
    "类型": {"primary": "03B15", "secondary": ["03B40"]},
}


def has_msc(content):
    """检查文件是否已有MSC编码"""
    return 'msc_primary:' in content


def detect_msc_from_filename(filename, content):
    """根据文件名和内容检测MSC编码"""
    search_text = (filename + " " + content[:1000]).lower()
    
    primary = None
    secondary = set()
    
    # 关键词匹配
    for keyword, mapping in EXTENDED_MSC_MAPPING.items():
        if keyword.lower() in search_text:
            if primary is None:
                primary = mapping["primary"]
            secondary.update(mapping["secondary"])
    
    # 如果没有匹配到，使用默认
    if primary is None:
        primary = "00-XX"
        secondary = ["00-XX"]
    else:
        secondary = list(secondary)[:3]
    
    return primary, secondary


def add_msc_to_frontmatter(content, primary, secondary):
    """添加MSC编码到frontmatter"""
    if content.strip().startswith('---'):
        # 已有frontmatter
        if has_msc(content):
            return content
        
        lines = content.split('\n')
        new_lines = []
        in_frontmatter = False
        frontmatter_end = 0
        
        for i, line in enumerate(lines):
            if line.strip() == '---':
                if not in_frontmatter:
                    in_frontmatter = True
                else:
                    frontmatter_end = i
                    break
        
        msc_lines = [
            f'msc_primary: "{primary}"',
            f'msc_secondary: {secondary}'
        ]
        
        new_lines = lines[:frontmatter_end] + msc_lines + lines[frontmatter_end:]
        return '\n'.join(new_lines)
    else:
        # 没有frontmatter
        frontmatter = f'''---
msc_primary: "{primary}"
msc_secondary: {secondary}
---

'''
        return frontmatter + content


def process_file(filepath):
    """处理单个文件"""
    try:
        with open(filepath, 'r', encoding='utf-8-sig') as f:
            content = f.read()
        
        if has_msc(content):
            return "already_has_msc", None
        
        filename = os.path.basename(filepath)
        primary, secondary = detect_msc_from_filename(filename, content)
        
        new_content = add_msc_to_frontmatter(content, primary, secondary)
        
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(new_content)
        
        return "success", {"primary": primary, "secondary": secondary}
    except Exception as e:
        return "error", str(e)


def main():
    """主函数"""
    docs_path = Path("docs")
    target_count = 500  # 目标500篇
    
    stats = {
        "total": 0,
        "already_has_msc": 0,
        "annotated": 0,
        "errors": 0,
        "by_folder": defaultdict(lambda: {"total": 0, "annotated": 0}),
        "msc_codes": defaultdict(int)
    }
    
    print("=" * 60)
    print("FormalMath项目MSC编码标注 - 第二阶段")
    print("=" * 60)
    print(f"开始时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"目标: 达到{target_count}篇标注")
    print()
    
    # 收集所有需要处理的文件
    all_files = []
    for filepath in docs_path.rglob("*.md"):
        all_files.append(filepath)
    
    # 按文件夹分组处理
    for filepath in all_files:
        stats["total"] += 1
        folder = filepath.parent.name
        stats["by_folder"][folder]["total"] += 1
        
        # 检查当前是否已达到目标
        current_annotated = stats["already_has_msc"] + stats["annotated"]
        if current_annotated >= target_count:
            break
        
        result, info = process_file(str(filepath))
        
        if result == "already_has_msc":
            stats["already_has_msc"] += 1
        elif result == "success":
            stats["annotated"] += 1
            stats["by_folder"][folder]["annotated"] += 1
            stats["msc_codes"][info["primary"]] += 1
            
            if stats["annotated"] % 25 == 0:
                current_total = stats["already_has_msc"] + stats["annotated"]
                print(f"进度: {current_total}/{target_count} 篇已标注")
        else:
            stats["errors"] += 1
    
    # 生成报告
    print()
    print("=" * 60)
    print("第二阶段标注完成报告")
    print("=" * 60)
    print(f"结束时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    print(f"📊 总体统计:")
    print(f"   总文档数: {stats['total']}")
    print(f"   已有MSC: {stats['already_has_msc']}")
    print(f"   本次新增: {stats['annotated']}")
    print(f"   错误数: {stats['errors']}")
    current_coverage = (stats['already_has_msc'] + stats['annotated']) / max(stats['total'], 1) * 100
    print(f"   当前覆盖率: {current_coverage:.1f}%")
    print(f"   总计已标注: {stats['already_has_msc'] + stats['annotated']} 篇")
    print()
    
    # 保存报告
    report_path = Path("docs/00-全局文档索引-MSC标注报告-阶段2.md")
    report_content = f'''# FormalMath项目MSC编码标注报告 - 阶段2

生成时间: {datetime.now().strftime('%Y年%m月%d日 %H:%M:%S')}

## 📊 总体统计

| 指标 | 数值 |
|------|------|
| 总文档数 | {stats['total']} |
| 已有MSC编码 | {stats['already_has_msc']} |
| 本次新增标注 | {stats['annotated']} |
| 错误数 | {stats['errors']} |
| **当前覆盖率** | **{current_coverage:.1f}%** |
| **总计已标注** | **{stats['already_has_msc'] + stats['annotated']} 篇** |

## 🏷️ 新增MSC编码统计 (Top 15)

| MSC编码 | 使用次数 |
|---------|----------|
'''
    for code, count in sorted(stats["msc_codes"].items(), key=lambda x: -x[1])[:15]:
        report_content += f"| {code} | {count} |\n"
    
    report_content += '''
---
*报告由MSC编码标注冲刺脚本自动生成*
'''
    
    with open(report_path, 'w', encoding='utf-8') as f:
        f.write(report_content)
    
    print(f"详细报告已保存: {report_path}")


if __name__ == "__main__":
    main()
