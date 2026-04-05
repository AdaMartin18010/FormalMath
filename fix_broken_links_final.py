#!/usr/bin/env python3
"""
修复FormalMath项目中的断链 - 最终轮
"""
import os
import re
import json

# 最终映射
FINAL_FIXES = {
    # etale上同调 - 映射到相关文件
    "../04-几何与拓扑/02-微分几何-扩展/etale-cohomology.md": "../04-几何与拓扑/02-微分几何-扩展/00-README.md",
    
    # 案例库中的错误相对路径
    "../../../01-基础数学/": "../../../01-基础数学/00-README.md",
    "../../../02-代数结构/": "../../../02-代数结构/00-README.md",
    "../../../03-分析学/": "../../../03-分析学/00-README.md",
    
    # 修复分析学中的路径问题
    "../../../03-分析学/02-实分析.md": "../../../03-分析学/00-README.md",
    "../../../03-分析学/": "../../../03-分析学/00-README.md",
    "../../../02-代数结构/": "../../../02-代数结构/00-README.md",
    
    # 其他
    "../04-几何与拓扑/01-几何学基础/": "../04-几何与拓扑/01-几何学基础/00-README.md",
    "../04-几何与拓扑/03-拓扑学内容/": "../04-几何与拓扑/03-拓扑学内容/00-README.md",
}


def fix_file_final(file_path, fixes_made):
    """最终修复"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        return False

    original_content = content
    file_fixed = False

    for old_link, new_link in FINAL_FIXES.items():
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
                    'type': 'final_fix'
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

    print("开始最终断链修复...")

    for target_dir in target_dirs:
        if not os.path.exists(target_dir):
            continue
        
        for root, _, filenames in os.walk(target_dir):
            for filename in filenames:
                if filename.endswith('.md'):
                    file_path = os.path.join(root, filename)
                    file_path = file_path.replace('\\', '/')
                    if fix_file_final(file_path, fixes_made):
                        files_fixed += 1

    print(f"\n最终修复完成!")
    print(f"修复文件数: {files_fixed}")
    print(f"修复链接数: {len(fixes_made)}")


if __name__ == '__main__':
    main()
