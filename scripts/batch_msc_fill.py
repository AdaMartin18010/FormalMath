#!/usr/bin/env python3
"""
Batch MSC encoding filler for FormalMath project.
Automatically assigns MSC codes to Markdown files missing them.
"""

import os
import re
from pathlib import Path

PROJECT_ROOT = Path(r"G:\_src\FormalMath")

# MSC mapping based on directory paths
DIR_MSC_MAP = {
    # Core branches
    "01-基础数学": ("03-XX", ["00A05", "97A50"]),
    "02-代数结构": ("16-XX", ["13-XX", "20-XX"]),
    "03-分析学": ("26-XX", ["28-XX", "30-XX"]),
    "04-几何与拓扑": ("51-XX", ["53-XX", "54-XX", "55-XX"]),
    "05-数论": ("11-XX", ["11Axx", "11Nxx"]),
    "05-微分方程": ("34-XX", ["35-XX", "37-XX"]),
    "06-概率论与统计": ("60-XX", ["62-XX"]),
    "07-数理逻辑": ("03-XX", ["68Qxx"]),
    "08-计算数学": ("65-XX", ["68-XX"]),
    "09-形式化证明": ("03B35", ["68T15", "03B70"]),
    "09-组合数学与离散数学": ("05-XX", ["68Rxx"]),
    "10-应用数学": ("00A69", ["70-XX", "80-XX", "90-XX"]),
    "11-高级数学": ("00A05", ["14-XX", "18-XX", "22-XX"]),
    "12-代数拓扑": ("55-XX", ["55Nxx", "55Pxx"]),
    "13-代数几何": ("14-XX", ["14Fxx", "14Hxx"]),
    "14-微分几何": ("53-XX", ["53Cxx", "53Dxx"]),
    "15-同调代数": ("18Gxx", ["55Uxx", "13Dxx"]),
    "16-偏微分方程": ("35-XX", ["35Jxx", "35Kxx", "35Lxx"]),
    "21-最优化": ("49-XX", ["90Cxx"]),
    "22-控制论": ("93-XX", ["49-XX"]),
    "23-信息论": ("94-XX", ["60-XX"]),
    "24-密码学": ("94A60", ["11T71", "68P25"]),
    "25-金融数学": ("91Gxx", ["60Hxx", "62P05"]),
    "26-生物数学": ("92Bxx", ["34Cxx", "92Cxx"]),
    "29-数据科学": ("62-XX", ["68T05", "68Wxx"]),
    
    # Special dirs
    "00-FAQ": ("00A99", ["97A99"]),
    "00-习题示例反例库": ("00A07", ["00A99"]),
    "00-表征实例库": ("00A05", ["00A99"]),
    "00-多维矩阵对比": ("00A99", ["97A99"]),
    "00-概念关联图谱": ("00A99", ["97A99"]),
    "00-工作示例库": ("00A05", ["00A99"]),
    "00-全局学习路径": ("97A30", ["97A99"]),
    "00-全局定理依赖网络": ("00A99", ["97A99"]),
    "00-交叉引用网络": ("00A99", ["97A99"]),
    "00-竞赛培训": ("00A07", ["97A80"]),
    "00-决策推理图": ("00A99", ["97A99"]),
    "00-实战问题解决": ("00A69", ["97A99"]),
    "00-数学史": ("01-XX", ["97A30"]),
    "00-思维导图": ("00A99", ["97A99"]),
    "00-推理判断树": ("00A99", ["97A99"]),
    "00-未解决问题": ("00A99", ["01-XX"]),
    "00-银层核心课程": ("97A30", ["00A05"]),
    "00-证明树": ("03B35", ["00A99"]),
    "00-知识层次体系": ("00A99", ["97A99"]),
    "00-知识图谱": ("00A99", ["97A99"]),
    "00-指南与FAQ": ("00A99", ["97A99"]),
    "00-学术写作支持系统": ("00A99", ["97A99"]),
    "00-合并内容": ("00A99", ["97A99"]),
    "00-核心概念理解三问": ("00A99", ["97A99"]),
    "00-贡献者指南": ("00A99", ["97A99"]),
    "04-International-Alignment": ("97A99", ["00A99"]),
    "04-习题与练习": ("00A07", ["97A99"]),
    "06-实例与案例分析": ("00A69", ["97A99"]),
    "07-反例与辨析": ("00A07", ["00A99"]),
    "07-数值分析": ("65-XX", ["68Wxx"]),
    "10-语义模型": ("03Bxx", ["68Qxx"]),
    "11-数学物理": ("70-XX", ["81-XX", "82-XX"]),
    "11-数学应用": ("00A69", ["90-XX"]),
    "11-综合应用": ("00A69", ["97A99"]),
    "12-学术资源": ("00A99", ["97A99"]),
    "13-数学前沿": ("00A99", ["01-XX"]),
    "99-归档文档": ("00A99", ["97A99"]),
    "en": ("00A99", ["97A99"]),
    "i18n": ("00A99", ["97A99"]),
    "supplement": ("00A99", ["97A99"]),
    "应用案例库": ("00A69", ["97A99"]),
    "可视化": ("00A99", ["97A99"]),
    "可视化内容": ("00A99", ["97A99"]),
    "格洛腾迪克": ("14Fxx", ["18Gxx", "14Axx"]),
    "管理员手册": ("00A99", ["97A99"]),
    "开发文档": ("00A99", ["97A99"]),
    "用户手册": ("00A99", ["97A99"]),
    "comparison-matrices": ("00A99", ["97A99"]),
    "concept-mindmaps": ("00A99", ["97A99"]),
    "decision-trees": ("00A99", ["97A99"]),
    "inference-trees": ("00A99", ["97A99"]),
    "generated": ("00A99", ["97A99"]),
}

# Mathematician MSC mapping
MATH_MSC_MAP = {
    "阿贝尔": ("14-XX", ["20-XX", "01A55"]),
    "阿蒂亚": ("58-XX", ["19-XX", "55-XX", "01A70"]),
    "阿基米德": ("01A20", ["51-XX"]),
    "巴拿赫": ("46-XX", ["01A60"]),
    "波尔查诺": ("01A55", ["26-XX"]),
    "波利亚": ("00A35", ["97Dxx"]),
    "伯努利": ("01A45", ["60-XX"]),
    "布尔": ("03Gxx", ["06-XX", "01A55"]),
    "布劳威尔": ("55Mxx", ["03F60", "01A60"]),
    "策梅洛": ("03E25", ["01A60"]),
    "陈省身": ("53-XX", ["55-XX", "01A70"]),
    "戴德金": ("01A55", ["11-XX", "13-XX"]),
    "德利涅": ("14Fxx", ["01A70"]),
    "狄利克雷": ("01A55", ["11-XX"]),
    "笛卡尔": ("01A45", ["51-XX"]),
    "费马": ("01A45", ["11-XX"]),
    "冯诺依曼": ("46Lxx", ["91Axx", "68-XX", "01A70"]),
    "弗兰克尔": ("03E99", ["01A60"]),
    "傅里叶": ("01A55", ["42-XX"]),
    "伽罗瓦": ("01A55", ["12-XX"]),
    "高斯": ("01A55", ["11-XX", "53-XX"]),
    "哥德尔": ("03Fxx", ["01A60"]),
    "格洛腾迪克": ("14Fxx", ["18Gxx", "01A70"]),
    "根岑": ("03F05", ["01A60"]),
    "哈密顿": ("01A55", ["70-XX", "53-XX"]),
    "海廷": ("03F55", ["01A60"]),
    "嘉当": ("53-XX", ["22-XX", "01A70"]),
    "凯莱": ("01A55", ["05-XX", "20-XX"]),
    "康托尔": ("03Exx", ["01A55"]),
    "柯西": ("01A55", ["30-XX", "26-XX"]),
    "科恩": ("03E35", ["01A70"]),
    "克莱因": ("01A55", ["51-XX", "22-XX"]),
    "克罗内克": ("01A55", ["11-XX"]),
    "拉格朗日": ("01A50", ["70-XX", "11-XX"]),
    "拉马努金": ("01A60", ["11-XX", "33-XX"]),
    "拉普拉斯": ("01A50", ["60-XX", "35-XX"]),
    "莱布尼茨": ("01A45", ["03-XX"]),
    "朗兰兹": ("11Fxx", ["22Exx", "01A70"]),
    "勒贝格": ("01A60", ["28-XX"]),
    "勒让德": ("01A50", ["33-XX", "11-XX"]),
    "黎曼": ("01A55", ["11Mxx", "53-XX", "30-XX"]),
    "李": ("22Exx", ["17Bxx", "01A55"]),
    "鲁里": ("18Nxx", ["55Uxx", "01A70"]),
    "罗巴切夫斯基": ("01A55", ["51-XX"]),
    "罗素": ("03A05", ["01A60"]),
    "牛顿": ("01A45", ["70-XX", "01-XX"]),
    "诺特": ("01A70", ["13-XX", "16-XX", "17-XX"]),
    "欧几里得": ("01A20", ["51-XX"]),
    "欧拉": ("01A50", ["05-XX", "11-XX", "33-XX"]),
    "帕斯卡": ("01A45", ["05-XX", "60-XX"]),
    "庞加莱": ("01A55", ["55-XX", "37-XX", "53-XX"]),
    "泊松": ("01A55", ["60-XX", "35-XX"]),
    "乔姆斯基": ("68Q45", ["03Dxx", "01A70"]),
    "切比雪夫": ("01A55", ["41-XX", "11-XX"]),
    "丘奇": ("03B40", ["68Qxx", "01A70"]),
    "塞尔": ("14Fxx", ["55-XX", "01A70"]),
    "施瓦茨": ("01A70", ["46-XX", "35-XX"]),
    "塔斯基": ("03Cxx", ["01A60"]),
    "图灵": ("03Dxx", ["68Qxx", "01A70"]),
    "外尔": ("01A60", ["22Exx", "53-XX", "81-XX"]),
    "韦伊": ("14-XX", ["11-XX", "01A70"]),
    "魏尔斯特拉斯": ("01A55", ["30-XX", "26-XX"]),
    "伍丁": ("03E55", ["03E60", "01A70"]),
    "希尔伯特": ("01A55", ["03-XX", "46-XX", "11-XX"]),
    "肖尔策": ("14Fxx", ["14Gxx", "01A70"]),
    "谢拉": ("03Cxx", ["01A70"]),
    "雅可比": ("01A55", ["11-XX", "33-XX"]),
}


def get_msc_for_path(rel_path: str) -> tuple:
    """Determine MSC codes based on file path."""
    parts = rel_path.replace("\\", "/").split("/")
    
    # Check mathematician directories
    if parts[0] == "数学家理念体系":
        for name, msc in MATH_MSC_MAP.items():
            if name in parts[1] if len(parts) > 1 else False:
                return msc
        return ("01-XX", ["97A30"])
    
    # Check concept directories
    if parts[0] == "concept":
        if len(parts) > 1:
            sub = parts[1]
            if "思维导图" in sub or "知识关联" in sub:
                return ("00A99", ["97A99"])
            if "认知" in sub or "教育" in sub:
                return ("97Cxx", ["97A99"])
            if "范畴论" in sub:
                return ("18-XX", ["00A99"])
            if "集合论" in sub:
                return ("03Exx", ["00A99"])
        return ("00A99", ["97A99"])
    
    # Check standard directory mapping
    for part in parts:
        if part in DIR_MSC_MAP:
            return DIR_MSC_MAP[part]
    
    # Default fallback based on path keywords
    path_lower = rel_path.lower()
    if "lean4" in path_lower or "形式化" in path_lower:
        return ("03B35", ["68T15"])
    if "习题" in path_lower or "练习" in path_lower:
        return ("00A07", ["97A99"])
    if "反例" in path_lower:
        return ("00A07", ["00A99"])
    if "实例" in path_lower:
        return ("00A05", ["00A99"])
    if "对齐" in path_lower or "alignment" in path_lower:
        return ("97A99", ["00A99"])
    if "报告" in path_lower or "report" in path_lower:
        return ("00A99", ["97A99"])
    if "计划" in path_lower or "plan" in path_lower:
        return ("00A99", ["97A99"])
    
    return ("00A99", ["97A99"])


def has_frontmatter(content: str) -> bool:
    return bool(re.match(r'^---\s*\n', content))


def add_msc_to_file(file_path: Path, msc_primary: str, msc_secondary: list):
    """Add MSC encoding to a file."""
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
        
        if not content.strip():
            return False
        
        msc_yaml = f"""---
msc_primary: {msc_primary}
msc_secondary:
"""
        for sec in msc_secondary:
            msc_yaml += f"  - {sec}\n"
        
        if has_frontmatter(content):
            # Already has frontmatter - insert MSC after opening ---
            # Find first ---
            match = re.match(r'^(---\s*\n)(.*?)(\n---\s*\n)', content, re.DOTALL)
            if match:
                # Check if msc_primary already exists
                if 'msc_primary' in match.group(2):
                    return False  # Already has MSC
                
                new_frontmatter = match.group(1) + match.group(2).rstrip() + "\n" + msc_yaml.replace("---\n", "") + "---\n"
                new_content = new_frontmatter + content[match.end():]
                
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(new_content)
                return True
        else:
            # No frontmatter - add one at the beginning
            new_content = msc_yaml + "---\n\n" + content
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(new_content)
            return True
        
        return False
    except Exception as e:
        print(f"Error processing {file_path}: {e}")
        return False


def main():
    exclude_dirs = {'.git', '.lake', 'node_modules', '__pycache__', 'search_index', 'vector_store', 'temp_scripts', '00-归档'}
    
    total = 0
    fixed = 0
    errors = 0
    
    for root, dirs, files in os.walk(PROJECT_ROOT):
        dirs[:] = [d for d in dirs if d not in exclude_dirs and not d.startswith('.')]
        for f in files:
            if not f.endswith('.md'):
                continue
            total += 1
            file_path = Path(root) / f
            rel_path = str(file_path.relative_to(PROJECT_ROOT))
            
            try:
                with open(file_path, 'r', encoding='utf-8', errors='ignore') as fh:
                    content = fh.read(1500)
                
                if re.search(r'^---\s*\n.*?msc_primary', content, re.MULTILINE | re.DOTALL):
                    continue  # Already has MSC
                
                msc_primary, msc_secondary = get_msc_for_path(rel_path)
                if add_msc_to_file(file_path, msc_primary, msc_secondary):
                    fixed += 1
                    print(f"[FIXED] {rel_path} -> {msc_primary}")
                
            except Exception as e:
                errors += 1
                print(f"[ERROR] {rel_path}: {e}")
    
    print(f"\n{'='*60}")
    print(f"MSC Batch Fill Complete")
    print(f"Total .md files scanned: {total}")
    print(f"Files fixed: {fixed}")
    print(f"Errors: {errors}")
    print(f"{'='*60}")


if __name__ == "__main__":
    main()
