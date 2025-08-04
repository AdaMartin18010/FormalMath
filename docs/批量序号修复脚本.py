#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
批量序号修复脚本
用于修复FormalMath文档库中的序号问题
"""

import os
import re
import glob
from pathlib import Path

def fix_advanced_math_documents():
    """修复高级数学文档的序号"""
    
    # 高级数学文档目录
    advanced_math_dir = "docs/11-高级数学"
    
    # 获取所有高级数学文档
    files = glob.glob(f"{advanced_math_dir}/*.md")
    files.sort()  # 按文件名排序
    
    for file_path in files:
        print(f"正在处理: {file_path}")
        
        # 读取文件内容
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # 获取文件名（不含扩展名）
        filename = Path(file_path).stem
        file_number = filename.split('-')[0]  # 获取文件编号
        
        # 确定正确的序号前缀
        if file_number.isdigit():
            section_number = f"11.{file_number}"
        else:
            continue
        
        # 修复主标题
        old_title_pattern = rf"^# {file_number}\. "
        new_title = f"# {section_number} "
        content = re.sub(old_title_pattern, new_title, content, flags=re.MULTILINE)
        
        # 修复目录中的主标题链接
        old_link_pattern = rf"\[{file_number}\. "
        new_link = f"[{section_number} "
        content = re.sub(old_link_pattern, new_link, content)
        
        old_anchor_pattern = rf"#{file_number}-"
        new_anchor = f"#{section_number.replace('.', '')}-"
        content = re.sub(old_anchor_pattern, new_anchor, content)
        
        # 修复章节标题 (## 3.1 -> ## 11.3.1)
        old_section_pattern = rf"## {file_number}\."
        new_section = f"## {section_number}."
        content = re.sub(old_section_pattern, new_section, content)
        
        # 修复子章节标题 (### 3.1.1 -> ### 11.3.1.1)
        old_subsection_pattern = rf"### {file_number}\."
        new_subsection = f"### {section_number}."
        content = re.sub(old_subsection_pattern, new_subsection, content)
        
        # 修复目录中的章节链接
        old_section_link_pattern = rf"\[{file_number}\.{file_number}\."
        new_section_link = f"[{section_number}.{file_number}."
        content = re.sub(old_section_link_pattern, new_section_link, content)
        
        # 修复目录中的子章节链接
        old_subsection_link_pattern = rf"\[{file_number}\.{file_number}\.{file_number}\."
        new_subsection_link = f"[{section_number}.{file_number}.{file_number}."
        content = re.sub(old_subsection_link_pattern, new_subsection_link, content)
        
        # 修复锚点链接
        old_anchor_section_pattern = rf"#{file_number}{file_number}-"
        new_anchor_section = f"#{section_number.replace('.', '')}{file_number}-"
        content = re.sub(old_anchor_section_pattern, new_anchor_section, content)
        
        old_anchor_subsection_pattern = rf"#{file_number}{file_number}{file_number}-"
        new_anchor_subsection = f"#{section_number.replace('.', '')}{file_number}{file_number}-"
        content = re.sub(old_anchor_subsection_pattern, new_anchor_subsection, content)
        
        # 写回文件
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(content)
        
        print(f"完成修复: {file_path}")

def fix_applied_math_documents():
    """修复应用数学文档的序号"""
    
    # 应用数学文档目录
    applied_math_dir = "docs/12-应用数学"
    
    # 获取所有应用数学文档
    files = glob.glob(f"{applied_math_dir}/*.md")
    files.sort()
    
    for file_path in files:
        print(f"正在处理: {file_path}")
        
        # 读取文件内容
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # 获取文件名（不含扩展名）
        filename = Path(file_path).stem
        file_number = filename.split('-')[0]  # 获取文件编号
        
        # 确定正确的序号前缀
        if file_number.isdigit():
            section_number = f"12.{file_number}"
        else:
            continue
        
        # 修复主标题
        old_title_pattern = rf"^# {file_number}\. "
        new_title = f"# {section_number} "
        content = re.sub(old_title_pattern, new_title, content, flags=re.MULTILINE)
        
        # 修复章节标题 (## 1. -> ## 12.1.)
        old_section_pattern = r"## (\d+)\. "
        def replace_section(match):
            old_num = match.group(1)
            new_num = f"12.{old_num}"
            return f"## {new_num}. "
        content = re.sub(old_section_pattern, replace_section, content)
        
        # 修复子章节标题 (### 1.1 -> ### 12.1.1)
        old_subsection_pattern = r"### (\d+)\.(\d+) "
        def replace_subsection(match):
            old_major = match.group(1)
            old_minor = match.group(2)
            new_major = f"12.{old_major}"
            return f"### {new_major}.{old_minor} "
        content = re.sub(old_subsection_pattern, replace_subsection, content)
        
        # 修复四级标题 (#### 1.1.1 -> #### 12.1.1.1)
        old_fourth_pattern = r"#### (\d+)\.(\d+)\.(\d+) "
        def replace_fourth(match):
            old_major = match.group(1)
            old_minor = match.group(2)
            old_sub = match.group(3)
            new_major = f"12.{old_major}"
            return f"#### {new_major}.{old_minor}.{old_sub} "
        content = re.sub(old_fourth_pattern, replace_fourth, content)
        
        # 修复目录中的链接
        # 这里需要更复杂的处理，暂时跳过
        
        # 写回文件
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(content)
        
        print(f"完成修复: {file_path}")

def main():
    """主函数"""
    print("开始批量修复序号...")
    
    # 修复高级数学文档
    print("\n=== 修复高级数学文档 ===")
    fix_advanced_math_documents()
    
    # 修复应用数学文档
    print("\n=== 修复应用数学文档 ===")
    fix_applied_math_documents()
    
    print("\n批量修复完成！")
    print("注意：请手动检查修复结果，确保所有链接和序号都正确。")

if __name__ == "__main__":
    main() 