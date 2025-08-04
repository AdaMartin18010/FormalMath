#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath 智能序号修复脚本
自动修复文档中的主题和子主题序号问题
"""

import os
import re
import json
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from datetime import datetime

class SmartNumberingFixer:
    """智能序号修复器"""
    
    def __init__(self, docs_path: str = "docs"):
        self.docs_path = Path(docs_path)
        self.fixed_files = []
        self.stats = {
            "total_files": 0,
            "fixed_files": 0,
            "total_fixes": 0
        }
        
    def fix_all_documents(self) -> Dict[str, int]:
        """修复所有文档的序号问题"""
        print("🚀 开始智能序号修复...")
        
        results = {}
        
        # 遍历所有markdown文件
        for md_file in self.docs_path.rglob("*.md"):
            if md_file.name.startswith(".") or "README" in md_file.name:
                continue
                
            print(f"🔧 处理文件: {md_file}")
            fixes = self.fix_single_document(md_file)
            if fixes > 0:
                results[str(md_file)] = fixes
                self.fixed_files.append(str(md_file))
                
        return results
    
    def fix_single_document(self, file_path: Path) -> int:
        """修复单个文档的序号问题"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            original_content = content
            fixed_content = self.apply_smart_fixes(content, file_path)
            
            if fixed_content != original_content:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(fixed_content)
                return 1
                
        except Exception as e:
            print(f"❌ 修复文件 {file_path} 时出错: {e}")
            
        return 0
    
    def apply_smart_fixes(self, content: str, file_path: Path) -> str:
        """应用智能修复"""
        # 获取文件的基础序号
        base_numbering = self.get_base_numbering(file_path)
        
        # 修复标题序号
        content = self.fix_title_numbering_smart(content, base_numbering)
        
        # 修复目录序号
        content = self.fix_toc_numbering_smart(content)
        
        # 修复定理序号
        content = self.fix_theorem_numbering_smart(content, base_numbering)
        
        return content
    
    def get_base_numbering(self, file_path: Path) -> str:
        """获取文件的基础序号"""
        relative_path = file_path.relative_to(self.docs_path)
        parts = relative_path.parts
        
        if len(parts) >= 2:
            category = parts[0]  # 如 "01-基础数学"
            subcategory = parts[1]  # 如 "01-集合论基础.md"
            
            # 解析类别序号
            category_match = re.match(r'(\d+)-(.+)', category)
            if category_match:
                category_num = category_match.group(1)
                
                # 解析子类别序号
                subcategory_match = re.match(r'(\d+)-(.+)', subcategory)
                if subcategory_match:
                    subcategory_num = subcategory_match.group(1)
                    return f"{category_num}.{subcategory_num}"
        
        return "1"
    
    def fix_title_numbering_smart(self, content: str, base_numbering: str) -> str:
        """智能修复标题序号"""
        lines = content.split('\n')
        fixed_lines = []
        current_numbering = {}
        base_parts = base_numbering.split('.')
        
        for line in lines:
            # 检查是否是标题行
            title_match = re.match(r'^(#{1,6})\s+(.+)$', line)
            if title_match:
                level = title_match.group(1)
                title_text = title_match.group(2)
                
                # 确定应该的序号格式
                level_num = len(level)
                
                if level_num == 1:  # 主标题
                    numbering = base_numbering
                elif level_num == 2:  # 二级标题
                    if 2 not in current_numbering:
                        current_numbering[2] = 1
                    else:
                        current_numbering[2] += 1
                    numbering = f"{base_numbering}.{current_numbering[2]}"
                elif level_num == 3:  # 三级标题
                    if 2 not in current_numbering:
                        current_numbering[2] = 1
                    if 3 not in current_numbering:
                        current_numbering[3] = 1
                    else:
                        current_numbering[3] += 1
                    numbering = f"{base_numbering}.{current_numbering[2]}.{current_numbering[3]}"
                elif level_num == 4:  # 四级标题
                    if 2 not in current_numbering:
                        current_numbering[2] = 1
                    if 3 not in current_numbering:
                        current_numbering[3] = 1
                    if 4 not in current_numbering:
                        current_numbering[4] = 1
                    else:
                        current_numbering[4] += 1
                    numbering = f"{base_numbering}.{current_numbering[2]}.{current_numbering[3]}.{current_numbering[4]}"
                else:
                    # 更深层次的标题
                    numbering_parts = [base_numbering]
                    for i in range(2, level_num + 1):
                        if i not in current_numbering:
                            current_numbering[i] = 1
                        else:
                            current_numbering[i] += 1
                        numbering_parts.append(str(current_numbering[i]))
                    numbering = ".".join(numbering_parts)
                
                # 检查标题是否已有序号
                existing_numbering = re.match(r'^(\d+(?:\.\d+)*)\s*', title_text)
                if not existing_numbering:
                    # 添加序号
                    fixed_title = f"{numbering} {title_text}"
                    fixed_lines.append(f"{level} {fixed_title}")
                else:
                    # 已有序号，检查是否需要修正
                    existing = existing_numbering.group(1)
                    if existing != numbering:
                        # 替换序号
                        fixed_title = re.sub(r'^\d+(?:\.\d+)*\s*', f"{numbering} ", title_text)
                        fixed_lines.append(f"{level} {fixed_title}")
                    else:
                        fixed_lines.append(line)
            else:
                fixed_lines.append(line)
        
        return '\n'.join(fixed_lines)
    
    def fix_toc_numbering_smart(self, content: str) -> str:
        """智能修复目录序号"""
        # 查找目录部分
        toc_pattern = r'(##\s*目录.*?\n)(.*?)(?=\n##|\n$)'
        toc_match = re.search(toc_pattern, content, re.DOTALL)
        
        if toc_match:
            toc_header = toc_match.group(1)
            toc_content = toc_match.group(2)
            
            # 修复目录中的链接序号
            lines = toc_content.split('\n')
            fixed_lines = []
            
            for line in lines:
                # 查找链接
                link_match = re.search(r'\[([^\]]+)\]\(#[^)]+\)', line)
                if link_match:
                    link_text = link_match.group(1)
                    
                    # 检查链接文本中的序号
                    numbering_match = re.match(r'^(\d+(?:\.\d+)*)\s*', link_text)
                    if numbering_match:
                        # 保持原样，因为链接序号应该与标题序号一致
                        fixed_lines.append(line)
                    else:
                        # 没有序号的链接，保持原样
                        fixed_lines.append(line)
                else:
                    fixed_lines.append(line)
            
            # 重建目录部分
            fixed_toc = toc_header + '\n'.join(fixed_lines)
            content = re.sub(toc_pattern, fixed_toc, content, flags=re.DOTALL)
        
        return content
    
    def fix_theorem_numbering_smart(self, content: str, base_numbering: str) -> str:
        """智能修复定理序号"""
        # 查找并修复定义和定理的序号
        theorem_pattern = r'\*\*(定义|定理|公理|引理|推论)\s+(\d+(?:\.\d+)*)\*\*'
        
        def replace_theorem(match):
            theorem_type = match.group(1)
            numbering = match.group(2)
            
            # 检查序号格式
            if self.is_valid_numbering_format(numbering):
                return match.group(0)  # 保持原样
            else:
                # 生成新的序号
                new_numbering = f"{base_numbering}.1"  # 使用基础序号
                return f"**{theorem_type} {new_numbering}**"
        
        content = re.sub(theorem_pattern, replace_theorem, content)
        
        return content
    
    def is_valid_numbering_format(self, numbering: str) -> bool:
        """验证序号格式是否有效"""
        # 检查基本格式
        if not re.match(r'^\d+(?:\.\d+)*$', numbering):
            return False
            
        # 检查层次合理性
        parts = numbering.split('.')
        for i, part in enumerate(parts):
            if not part.isdigit() or int(part) == 0:
                return False
                
        return True
    
    def generate_fix_report(self, results: Dict[str, int]) -> str:
        """生成修复报告"""
        report = []
        report.append("# FormalMath 智能序号修复报告")
        report.append(f"修复时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        report.append("")
        
        if not results:
            report.append("✅ 无需修复，所有文档序号都是规范的")
            return "\n".join(report)
            
        report.append(f"## 修复结果 ({len(results)} 个文件)")
        report.append("")
        
        total_fixes = 0
        for file_path, fixes in results.items():
            report.append(f"### {file_path}")
            report.append(f"- 修复了 {fixes} 个序号问题")
            report.append("")
            total_fixes += fixes
            
        report.append(f"## 统计信息")
        report.append(f"- 修复文件数: {len(results)}")
        report.append(f"- 总修复数: {total_fixes}")
        report.append("")
        
        return "\n".join(report)
    
    def run_smart_fix(self) -> Dict[str, int]:
        """运行智能修复"""
        print("🚀 开始智能序号修复...")
        
        # 修复所有文档
        results = self.fix_all_documents()
        
        # 生成报告
        report = self.generate_fix_report(results)
        
        # 保存报告
        report_path = self.docs_path / "智能序号修复报告.md"
        with open(report_path, 'w', encoding='utf-8') as f:
            f.write(report)
            
        print(f"📊 修复完成，修复了 {len(results)} 个文件")
        print(f"📄 详细报告已保存到: {report_path}")
        
        return results

def main():
    """主函数"""
    fixer = SmartNumberingFixer()
    
    # 运行智能修复
    results = fixer.run_smart_fix()
    
    if results:
        print(f"🎉 成功修复了 {len(results)} 个文件的序号问题！")
    else:
        print("🎉 所有文档的序号都是规范的！")

if __name__ == "__main__":
    main() 