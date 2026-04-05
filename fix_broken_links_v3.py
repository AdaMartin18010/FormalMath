#!/usr/bin/env python3
"""
修复FormalMath项目中的断链 - 第三轮（最终）
"""
import os
import re
import json

# 最终链接映射
FINAL_LINK_MAPPING = {
    # 几何学基础中的文件
    "../04-几何与拓扑/01-几何学基础/辛几何.md": "../04-几何与拓扑/01-几何学基础/06-辛几何-增强版.md",
    "../04-几何与拓扑/01-几何学基础/热带几何.md": "../04-几何与拓扑/01-几何学基础/00-README.md",
    
    # 导出代数几何
    "../11-高级数学/导出代数几何.md": "../11-高级数学/05-导出代数几何.md",
    
    # INDEX.md
    "../INDEX.md": "../../INDEX.md",
    
    # 案例库内部相对链接
    "../01-基础数学/": "../../../01-基础数学/",
    "../02-代数结构/": "../../../02-代数结构/",
    "../03-分析学/": "../../../03-分析学/",
}

# 需要特殊处理的目录链接 - 指向00-README.md
DIRECTORY_TO_README = {
    "../02-代数结构/": "../02-代数结构/00-README.md",
    "../03-分析学/": "../03-分析学/00-README.md",
    "../04-几何与拓扑/02-代数拓扑/": "../04-几何与拓扑/02-微分几何-扩展/00-README.md",
    "../04-几何与拓扑/": "../04-几何与拓扑/00-README.md",
    "../05-数论/": "../05-数论/00-README.md",
    "../06-概率论与统计/": "../06-概率论与统计/00-README.md",
    "../07-数理逻辑/": "../07-数理逻辑/README.md",
    "../08-计算数学/": "../08-计算数学/00-README.md",
    "../09-组合数学与离散数学/02-图论/": "../09-组合数学与离散数学/02-图论/00-README.md",
    "../09-组合数学与离散数学/": "../09-组合数学与离散数学/01-组合数学/00-README.md",
}


def fix_file_v3(file_path, fixes_made):
    """修复单个文件中的断链 - 第三轮"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        return False

    original_content = content
    file_fixed = False

    # 应用最终链接映射
    for old_link, new_link in FINAL_LINK_MAPPING.items():
        pattern = rf'\[([^\]]*)\]\({re.escape(old_link)}\)'
        matches = list(re.finditer(pattern, content))
        if matches:
            for match in matches:
                text = match.group(1)
                content = content.replace(match.group(0), f'[{text}]({new_link})')
                fixes_made.append({
                    'file': file_path,
                    'old': match.group(0),
                    'new': f'[{text}]({new_link})',
                    'type': 'final_mapping'
                })
                file_fixed = True

    # 处理目录链接 - 指向README
    for old_dir, new_file in DIRECTORY_TO_README.items():
        # 匹配目录链接（以/结尾）
        pattern = rf'\[([^\]]*)\]\({re.escape(old_dir)}\)'
        matches = list(re.finditer(pattern, content))
        if matches:
            for match in matches:
                text = match.group(1)
                content = content.replace(match.group(0), f'[{text}]({new_file})')
                fixes_made.append({
                    'file': file_path,
                    'old': match.group(0),
                    'new': f'[{text}]({new_file})',
                    'type': 'directory_to_readme'
                })
                file_fixed = True

    if file_fixed and content != original_content:
        try:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(content)
            return True
        except Exception as e:
            print(f"Error writing {file_path}: {e}")
            return False
    
    return False


def main():
    target_dirs = [
        "docs/05-数论",
        "docs/06-概率论与统计",
        "docs/07-数理逻辑",
        "docs/08-计算数学",
        "docs/09-组合数学与离散数学",
        "docs/10-应用数学",
        "docs/11-高级数学",
    ]

    fixes_made = []
    files_fixed = 0

    print("开始第三轮（最终）断链修复...")

    for target_dir in target_dirs:
        if not os.path.exists(target_dir):
            continue
        
        for root, _, filenames in os.walk(target_dir):
            for filename in filenames:
                if filename.endswith('.md'):
                    file_path = os.path.join(root, filename)
                    file_path = file_path.replace('\\', '/')
                    if fix_file_v3(file_path, fixes_made):
                        files_fixed += 1

    total_links_fixed = len(fixes_made)

    print(f"\n第三轮修复完成!")
    print(f"修复文件数: {files_fixed}")
    print(f"修复链接数: {total_links_fixed}")

    # 保存修复记录
    report = {
        'files_fixed': files_fixed,
        'total_links_fixed': total_links_fixed,
        'fixes': fixes_made
    }

    with open('link_fixes_report_v3.json', 'w', encoding='utf-8') as f:
        json.dump(report, f, ensure_ascii=False, indent=2)


if __name__ == '__main__':
    main()
