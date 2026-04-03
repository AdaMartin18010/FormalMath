#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath项目MSC编码标注冲刺脚本
目标：将MSC编码覆盖率从20%提升到100%（500篇）
"""

import os
import re
import yaml
from pathlib import Path
from datetime import datetime
from collections import defaultdict

# MSC2020编码映射表（基于分支目录）
MSC_MAPPING = {
    # 01-基础数学
    "01-基础数学": {
        "default": {"primary": "00-XX", "secondary": ["03-XX"]},
        "ZFC": {"primary": "03E30", "secondary": ["03E25", "03E35"]},
        "集合": {"primary": "03E20", "secondary": ["03E15", "03E25"]},
        "数系": {"primary": "00A05", "secondary": ["03E20", "11-XX"]},
        "自然数": {"primary": "03F30", "secondary": ["03E20", "11Axx"]},
        "测度": {"primary": "28Axx", "secondary": ["26A42", "60A10"]},
        "标准": {"primary": "00A05", "secondary": ["00-XX"]},
    },
    # 02-代数结构
    "02-代数结构": {
        "default": {"primary": "08-XX", "secondary": ["06-XX", "12-XX"]},
        "群": {"primary": "20-XX", "secondary": ["20Fxx", "20Gxx"]},
        "环": {"primary": "16-XX", "secondary": ["13-XX", "16Wxx"]},
        "域": {"primary": "12Fxx", "secondary": ["12Exx", "11Rxx"]},
        "模": {"primary": "16Dxx", "secondary": ["13Cxx", "18Gxx"]},
        "向量空间": {"primary": "15A03", "secondary": ["15Axx", "46Axx"]},
        "代数": {"primary": "16-XX", "secondary": ["17-XX", "18-XX"]},
        "李代数": {"primary": "17Bxx", "secondary": ["17-XX", "22Exx"]},
        "交换": {"primary": "13-XX", "secondary": ["14-XX", "13Axx"]},
        "同调": {"primary": "18Gxx", "secondary": ["13Dxx", "16Exx"]},
        "范畴": {"primary": "18-XX", "secondary": ["18Axx", "18Bxx"]},
        "表示": {"primary": "20Cxx", "secondary": ["20G05", "22E47"]},
        "伽罗瓦": {"primary": "12F10", "secondary": ["11R32", "13B05"]},
    },
    # 03-分析学
    "03-分析学": {
        "default": {"primary": "26-XX", "secondary": ["28-XX", "30-XX"]},
        "实分析": {"primary": "26Axx", "secondary": ["26Bxx", "28Axx"]},
        "复分析": {"primary": "30-XX", "secondary": ["31-XX", "32-XX"]},
        "泛函": {"primary": "46-XX", "secondary": ["47-XX", "46Bxx"]},
        "调和": {"primary": "42-XX", "secondary": ["43-XX", "44-XX"]},
        "Lebesgue": {"primary": "28A25", "secondary": ["26A42", "42Bxx"]},
        "积分": {"primary": "28-XX", "secondary": ["26A42", "42Bxx"]},
        "微分": {"primary": "26A24", "secondary": ["34-XX", "35-XX"]},
        "测度": {"primary": "28Axx", "secondary": ["60A10", "46Gxx"]},
        "变分": {"primary": "49-XX", "secondary": ["35A15", "58E30"]},
        "微分方程": {"primary": "34-XX", "secondary": ["35-XX", "37-XX"]},
        "偏微分": {"primary": "35-XX", "secondary": ["35Axx", "35Bxx"]},
    },
    # 04-几何学
    "04-几何学": {
        "default": {"primary": "51-XX", "secondary": ["52-XX", "53-XX"]},
        "欧几里得": {"primary": "51Mxx", "secondary": ["51Nxx", "51Axx"]},
        "解析": {"primary": "51N20", "secondary": ["14Nxx", "53A04"]},
        "微分": {"primary": "53-XX", "secondary": ["53Axx", "53Bxx"]},
        "射影": {"primary": "51A05", "secondary": ["51N15", "14Nxx"]},
        "代数": {"primary": "14-XX", "secondary": ["14Nxx", "14Cxx"]},
        "拓扑": {"primary": "57Rxx", "secondary": ["54-XX", "55-XX"]},
        "非欧": {"primary": "51M10", "secondary": ["51M09", "53A35"]},
        "黎曼": {"primary": "53B20", "secondary": ["53Cxx", "53Axx"]},
    },
    # 05-拓扑学
    "05-拓扑学": {
        "default": {"primary": "54-XX", "secondary": ["55-XX", "57-XX"]},
        "点集": {"primary": "54Axx", "secondary": ["54Bxx", "54Cxx"]},
        "代数": {"primary": "55-XX", "secondary": ["55Nxx", "55Uxx"]},
        "微分": {"primary": "57Rxx", "secondary": ["53Cxx", "58Axx"]},
        "同伦": {"primary": "55Pxx", "secondary": ["55Qxx", "55Uxx"]},
        "同调": {"primary": "55Nxx", "secondary": ["18Gxx", "57Txx"]},
        "纤维": {"primary": "55Rxx", "secondary": ["57R22", "53C10"]},
        "流形": {"primary": "57Nxx", "secondary": ["57Rxx", "53Cxx"]},
    },
    # 06-数论
    "06-数论": {
        "default": {"primary": "11-XX", "secondary": ["11Axx", "11Bxx"]},
        "初等": {"primary": "11Axx", "secondary": ["11Bxx", "11Dxx"]},
        "解析": {"primary": "11Mxx", "secondary": ["11Nxx", "11Pxx"]},
        "代数": {"primary": "11Rxx", "secondary": ["11Sxx", "11Txx"]},
        "算术": {"primary": "11Gxx", "secondary": ["11Dxx", "14Gxx"]},
    },
    # 07-逻辑学
    "07-逻辑学": {
        "default": {"primary": "03-XX", "secondary": ["03Bxx", "03Cxx"]},
        "命题": {"primary": "03B05", "secondary": ["03B20", "03Gxx"]},
        "谓词": {"primary": "03Cxx", "secondary": ["03B10", "03C07"]},
        "模型": {"primary": "03Cxx", "secondary": ["03C64", "03C90"]},
        "证明": {"primary": "03Fxx", "secondary": ["03B35", "68T15"]},
        "递归": {"primary": "03Dxx", "secondary": ["03D20", "68Q05"]},
        "集合": {"primary": "03Exx", "secondary": ["03E20", "03E25"]},
    },
    # 08-计算数学
    "08-计算数学": {
        "default": {"primary": "65-XX", "secondary": ["68-XX", "90-XX"]},
        "数值": {"primary": "65Dxx", "secondary": ["65Lxx", "65Mxx"]},
        "算法": {"primary": "68Wxx", "secondary": ["68Qxx", "65Yxx"]},
        "优化": {"primary": "90Cxx", "secondary": ["49Mxx", "65Kxx"]},
        "模拟": {"primary": "65Cxx", "secondary": ["68U20", "60H35"]},
    },
    # 09-形式化证明
    "09-形式化证明": {
        "default": {"primary": "68Vxx", "secondary": ["03B35", "03B70"]},
        "证明": {"primary": "03Fxx", "secondary": ["68T15", "03B35"]},
        "Lean": {"primary": "68V20", "secondary": ["03B35", "03B70"]},
        "Coq": {"primary": "68V20", "secondary": ["03B35", "03B15"]},
        "Isabelle": {"primary": "68V20", "secondary": ["03B35", "03B10"]},
        "自动": {"primary": "68T15", "secondary": ["03B35", "68V15"]},
    },
    # 10-语义模型
    "10-语义模型": {
        "default": {"primary": "03Cxx", "secondary": ["03Bxx", "68Qxx"]},
        "语义": {"primary": "03C65", "secondary": ["03C90", "68Q55"]},
        "语法": {"primary": "03B65", "secondary": ["03Cxx", "68Q42"]},
        "类型": {"primary": "03B15", "secondary": ["03B40", "68N18"]},
    },
    # 11-高级数学
    "11-高级数学": {
        "default": {"primary": "00-XX", "secondary": ["14-XX", "53-XX"]},
        "代数几何": {"primary": "14-XX", "secondary": ["14Fxx", "14Hxx"]},
        "同伦": {"primary": "55Pxx", "secondary": ["55Qxx", "18G55"]},
        "同调": {"primary": "18Gxx", "secondary": ["55Uxx", "13Dxx"]},
        "表示": {"primary": "20Cxx", "secondary": ["22E47", "17B10"]},
        "朗兰兹": {"primary": "11R39", "secondary": ["22E50", "14D24"]},
    },
    # 12-应用数学
    "12-应用数学": {
        "default": {"primary": "00A69", "secondary": ["60-XX", "62-XX"]},
        "概率": {"primary": "60-XX", "secondary": ["60Axx", "60Bxx"]},
        "统计": {"primary": "62-XX", "secondary": ["62Fxx", "62Jxx"]},
        "随机": {"primary": "60Gxx", "secondary": ["60Hxx", "60Jxx"]},
        "金融": {"primary": "91Gxx", "secondary": ["60H30", "62P05"]},
        "物理": {"primary": "70-XX", "secondary": ["76-XX", "81-XX"]},
        "医学": {"primary": "92C50", "secondary": ["62P10", "65Cxx"]},
        "图像": {"primary": "68U10", "secondary": ["94A08", "65D18"]},
    },
    # 13-代数几何
    "13-代数几何": {
        "default": {"primary": "14-XX", "secondary": ["14Fxx", "14Hxx"]},
        "基础": {"primary": "14Axx", "secondary": ["14Bxx", "14Cxx"]},
        "概形": {"primary": "14Fxx", "secondary": ["14A15", "18F20"]},
        "曲线": {"primary": "14Hxx", "secondary": ["14Cxx", "14Nxx"]},
        "曲面": {"primary": "14Jxx", "secondary": ["14Cxx", "14Dxx"]},
    },
    # 14-微分几何
    "14-微分几何": {
        "default": {"primary": "53-XX", "secondary": ["53Cxx", "53Axx"]},
        "基础": {"primary": "53Axx", "secondary": ["53Bxx", "53Cxx"]},
        "黎曼": {"primary": "53B20", "secondary": ["53C20", "58J60"]},
        "辛": {"primary": "53Dxx", "secondary": ["37Jxx", "70G45"]},
    },
    # 15-同调代数
    "15-同调代数": {
        "default": {"primary": "18Gxx", "secondary": ["13Dxx", "16Exx"]},
        "基础": {"primary": "18Gxx", "secondary": ["18A30", "18E10"]},
        "导出": {"primary": "13D09", "secondary": ["18Gxx", "14F05"]},
        "Tor": {"primary": "18G10", "secondary": ["13D03", "16E30"]},
        "Ext": {"primary": "18G15", "secondary": ["13D07", "16E30"]},
    },
}

# 特殊关键词映射（用于文件名分析）
KEYWORD_MAPPING = {
    # 基础数学
    "集合论": "03E20",
    "公理": "03E30",
    "ZFC": "03E35",
    "选择公理": "03E25",
    "连续统": "03E50",
    "基数": "03E10",
    "序数": "03E10",
    
    # 代数
    "群论": "20-XX",
    "群": "20-XX",
    "环": "16-XX",
    "域": "12Fxx",
    "模": "16Dxx",
    "线性代数": "15-XX",
    "矩阵": "15Axx",
    "李群": "22Exx",
    "李代数": "17Bxx",
    "交换代数": "13-XX",
    "同调代数": "18Gxx",
    "范畴论": "18-XX",
    "表示论": "20Cxx",
    "伽罗瓦": "12F10",
    
    # 分析
    "实分析": "26Axx",
    "复分析": "30-XX",
    "泛函分析": "46-XX",
    "调和分析": "42-XX",
    "傅里叶": "42Axx",
    "微积分": "26-XX",
    "积分": "28-XX",
    "测度论": "28Axx",
    "微分方程": "34-XX",
    "偏微分": "35-XX",
    "变分法": "49-XX",
    "泛函": "46Axx",
    "Banach": "46Bxx",
    "Hilbert": "46Cxx",
    "Sobolev": "46E35",
    
    # 几何
    "欧几里得": "51Mxx",
    "解析几何": "51N20",
    "微分几何": "53-XX",
    "射影几何": "51A05",
    "代数几何": "14-XX",
    "黎曼几何": "53B20",
    "非欧几何": "51M10",
    
    # 拓扑
    "点集拓扑": "54Axx",
    "代数拓扑": "55-XX",
    "微分拓扑": "57Rxx",
    "同伦论": "55Pxx",
    "同调": "55Nxx",
    "纤维丛": "55Rxx",
    "流形": "57Nxx",
    
    # 数论
    "数论": "11-XX",
    "素数": "11A41",
    "同余": "11A07",
    "丢番图": "11Dxx",
    
    # 逻辑
    "逻辑": "03-XX",
    "命题逻辑": "03B05",
    "谓词逻辑": "03B10",
    "模型论": "03Cxx",
    "证明论": "03Fxx",
    "递归论": "03Dxx",
    
    # 计算
    "数值": "65Dxx",
    "算法": "68Wxx",
    "优化": "90Cxx",
    
    # 概率统计
    "概率": "60-XX",
    "统计": "62-XX",
    "随机": "60Gxx",
    
    # 形式化
    "形式化": "68Vxx",
    "Lean": "68V20",
    "Coq": "68V20",
    "证明辅助": "68V15",
}


def detect_msc_from_content(filepath, content, branch):
    """根据文件内容检测MSC编码"""
    filename = os.path.basename(filepath)
    title = ""
    
    # 提取标题
    title_match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
    if title_match:
        title = title_match.group(1)
    
    # 获取分支映射
    branch_mapping = MSC_MAPPING.get(branch, {"default": {"primary": "00-XX", "secondary": ["00-XX"]}})
    
    # 关键词匹配
    primary = None
    secondary = set()
    
    search_text = (title + " " + filename + " " + content[:2000]).lower()
    
    # 遍历关键词映射
    for keyword, code in KEYWORD_MAPPING.items():
        if keyword.lower() in search_text:
            if primary is None:
                primary = code
            secondary.add(code)
    
    # 分支特定关键词匹配
    for key, mapping in branch_mapping.items():
        if key != "default" and key.lower() in search_text:
            primary = mapping["primary"]
            secondary.update(mapping["secondary"])
    
    # 如果没有匹配到，使用默认值
    if primary is None:
        primary = branch_mapping["default"]["primary"]
        secondary = set(branch_mapping["default"]["secondary"])
    
    # 限制次要编码数量
    secondary = list(secondary)[:3]
    
    return primary, secondary


def has_frontmatter(content):
    """检查文件是否已有frontmatter"""
    return content.strip().startswith('---')


def has_msc(content):
    """检查文件是否已有MSC编码"""
    return 'msc_primary:' in content


def add_msc_to_frontmatter(content, primary, secondary):
    """添加MSC编码到frontmatter"""
    if has_frontmatter(content):
        # 已有frontmatter，检查是否有MSC
        if has_msc(content):
            # 已有MSC，不修改
            return content
        
        # 在frontmatter中添加MSC
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
        
        # 在frontmatter结束前添加MSC
        msc_lines = [
            f'msc_primary: "{primary}"',
            f'msc_secondary: {secondary}'
        ]
        
        new_lines = lines[:frontmatter_end] + msc_lines + lines[frontmatter_end:]
        return '\n'.join(new_lines)
    else:
        # 没有frontmatter，创建新的
        frontmatter = f'''---
msc_primary: "{primary}"
msc_secondary: {secondary}
---

'''
        return frontmatter + content


def process_file(filepath, branch):
    """处理单个文件"""
    try:
        with open(filepath, 'r', encoding='utf-8-sig') as f:
            content = f.read()
        
        # 检查是否已有MSC
        if has_msc(content):
            return "already_has_msc", None
        
        # 检测MSC编码
        primary, secondary = detect_msc_from_content(filepath, content, branch)
        
        # 添加MSC到frontmatter
        new_content = add_msc_to_frontmatter(content, primary, secondary)
        
        # 写回文件
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(new_content)
        
        return "success", {"primary": primary, "secondary": secondary}
    except Exception as e:
        return "error", str(e)


def main():
    """主函数"""
    docs_path = Path("docs")
    
    # 统计
    stats = {
        "total": 0,
        "already_has_msc": 0,
        "annotated": 0,
        "errors": 0,
        "by_branch": defaultdict(lambda: {"total": 0, "annotated": 0}),
        "msc_codes": defaultdict(int)
    }
    
    # 需要跳过的文件（报告、README等）
    skip_patterns = [
        "README", "00-README", "归档", "报告", "总结", "周报", "规范", "标准",
        "导航", "索引", "说明", "看板", "质量", "格式", "质量验证",
    ]
    
    print("=" * 60)
    print("FormalMath项目MSC编码标注冲刺")
    print("=" * 60)
    print(f"开始时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    
    # 处理每个分支
    batch_size = 50
    batch_count = 0
    
    for branch_dir in sorted(docs_path.iterdir()):
        if not branch_dir.is_dir():
            continue
        
        branch = branch_dir.name
        if branch.startswith('99-') or branch in ['可视化内容', '学术写作支持', '工作示例', '应用案例库']:
            continue
        
        md_files = list(branch_dir.rglob("*.md"))
        
        for filepath in md_files:
            stats["total"] += 1
            stats["by_branch"][branch]["total"] += 1
            
            # 检查是否需要跳过
            filename = filepath.name
            should_skip = any(pattern in filename for pattern in skip_patterns)
            
            if should_skip:
                continue
            
            result, info = process_file(str(filepath), branch)
            
            if result == "already_has_msc":
                stats["already_has_msc"] += 1
            elif result == "success":
                stats["annotated"] += 1
                stats["by_branch"][branch]["annotated"] += 1
                stats["msc_codes"][info["primary"]] += 1
                batch_count += 1
                
                if batch_count % batch_size == 0:
                    print(f"进度: 已标注 {stats['annotated']} 篇，当前分支: {branch}")
            else:
                stats["errors"] += 1
                print(f"错误 [{filepath}]: {info}")
    
    # 生成报告
    print()
    print("=" * 60)
    print("MSC编码标注完成报告")
    print("=" * 60)
    print(f"结束时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    print(f"📊 总体统计:")
    print(f"   总文档数: {stats['total']}")
    print(f"   已有MSC: {stats['already_has_msc']}")
    print(f"   本次标注: {stats['annotated']}")
    print(f"   错误数: {stats['errors']}")
    print(f"   覆盖率: {((stats['already_has_msc'] + stats['annotated']) / stats['total'] * 100):.1f}%")
    print()
    print(f"📁 各分支统计:")
    for branch, data in sorted(stats["by_branch"].items()):
        if data["total"] > 0:
            print(f"   {branch}: {data['annotated']}/{data['total']} 篇已标注")
    print()
    print(f"🏷️ 使用最多的MSC编码 (Top 10):")
    for code, count in sorted(stats["msc_codes"].items(), key=lambda x: -x[1])[:10]:
        print(f"   {code}: {count} 篇")
    print()
    
    # 保存详细报告
    report_path = Path("docs/00-全局文档索引-MSC标注报告.md")
    report_content = f'''# FormalMath项目MSC编码标注报告

生成时间: {datetime.now().strftime('%Y年%m月%d日 %H:%M:%S')}

## 📊 总体统计

| 指标 | 数值 |
|------|------|
| 总文档数 | {stats['total']} |
| 已有MSC编码 | {stats['already_has_msc']} |
| 本次新增标注 | {stats['annotated']} |
| 错误数 | {stats['errors']} |
| **当前覆盖率** | **{((stats['already_has_msc'] + stats['annotated']) / max(stats['total'], 1) * 100):.1f}%** |

## 📁 各分支标注统计

| 分支 | 总文档数 | 本次标注 | 覆盖率 |
|------|----------|----------|--------|
'''
    for branch, data in sorted(stats["by_branch"].items()):
        if data["total"] > 0:
            coverage = (data["annotated"] / data["total"] * 100)
            report_content += f"| {branch} | {data['total']} | {data['annotated']} | {coverage:.1f}% |\n"
    
    report_content += f'''
## 🏷️ MSC编码使用统计 (Top 20)

| MSC编码 | 使用次数 | 说明 |
|---------|----------|------|
'''
    for code, count in sorted(stats["msc_codes"].items(), key=lambda x: -x[1])[:20]:
        report_content += f"| {code} | {count} | - |\n"
    
    report_content += '''
## 📝 说明

- 本次标注基于MSC2020分类标准
- 主要MSC编码基于文档内容自动检测
- 次要编码最多包含3个相关领域

---
*报告由MSC编码标注冲刺脚本自动生成*
'''
    
    with open(report_path, 'w', encoding='utf-8') as f:
        f.write(report_content)
    
    print(f"详细报告已保存: {report_path}")


if __name__ == "__main__":
    main()
