#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath 项目序号规范化持续推进脚本
持续检查和修复文档中的主题和子主题序号问题
"""

import os
import re
import json
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from datetime import datetime

class NumberingValidator:
    """序号验证和修复器"""
    
    def __init__(self, docs_path: str = "docs"):
        self.docs_path = Path(docs_path)
        self.issues = []
        self.fixes = []
        self.stats = {
            "total_files": 0,
            "files_with_issues": 0,
            "total_issues": 0,
            "fixed_issues": 0
        }
        
    def scan_all_documents(self) -> Dict[str, List[str]]:
        """扫描所有文档的序号问题"""
        print("🔍 开始扫描所有文档的序号问题...")
        
        all_issues = {}
        
        # 遍历所有markdown文件
        for md_file in self.docs_path.rglob("*.md"):
            if md_file.name.startswith(".") or "README" in md_file.name:
                continue
                
            issues = self.check_document_numbering(md_file)
            if issues:
                all_issues[str(md_file)] = issues
                
        return all_issues
    
    def check_document_numbering(self, file_path: Path) -> List[str]:
        """检查单个文档的序号问题"""
        issues = []
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            # 检查标题序号
            title_issues = self.check_title_numbering(content, file_path)
            issues.extend(title_issues)
            
            # 检查目录序号
            toc_issues = self.check_toc_numbering(content, file_path)
            issues.extend(toc_issues)
            
            # 检查定义和定理序号
            theorem_issues = self.check_theorem_numbering(content, file_path)
            issues.extend(theorem_issues)
            
        except Exception as e:
            issues.append(f"读取文件时出错: {e}")
            
        return issues
    
    def check_title_numbering(self, content: str, file_path: Path) -> List[str]:
        """检查标题序号的一致性"""
        issues = []
        
        # 提取所有标题
        title_pattern = r'^(#{1,6})\s+(.+)$'
        titles = re.findall(title_pattern, content, re.MULTILINE)
        
        # 分析标题层次和序号
        expected_numbering = self.analyze_expected_numbering(file_path)
        
        for i, (level, title) in enumerate(titles):
            # 检查序号格式
            numbering_issues = self.validate_title_numbering(title, level, expected_numbering, i)
            if numbering_issues:
                issues.extend(numbering_issues)
                
        return issues
    
    def analyze_expected_numbering(self, file_path: Path) -> Dict[str, str]:
        """分析文件应该使用的序号格式"""
        # 根据文件路径确定序号格式
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
                    return {
                        "category": category_num,
                        "subcategory": subcategory_num,
                        "format": f"{category_num}.{subcategory_num}"
                    }
        
        return {"format": "unknown"}
    
    def validate_title_numbering(self, title: str, level: str, expected: Dict[str, str], index: int) -> List[str]:
        """验证标题序号格式"""
        issues = []
        
        # 提取序号部分
        numbering_match = re.match(r'^(\d+(?:\.\d+)*)\s*', title)
        if not numbering_match:
            return [f"标题缺少序号: {title}"]
            
        numbering = numbering_match.group(1)
        
        # 检查序号层次
        parts = numbering.split('.')
        expected_levels = len(level)  # #的数量对应层次
        
        if len(parts) != expected_levels:
            issues.append(f"序号层次不匹配: {title} (期望{expected_levels}层，实际{len(parts)}层)")
            
        # 检查序号连续性
        if index > 0:
            # 这里可以添加更复杂的连续性检查
            pass
            
        return issues
    
    def check_toc_numbering(self, content: str, file_path: Path) -> List[str]:
        """检查目录中的序号一致性"""
        issues = []
        
        # 提取目录部分
        toc_pattern = r'##\s*目录.*?\n(.*?)(?=\n##|\n$)'
        toc_match = re.search(toc_pattern, content, re.DOTALL)
        
        if toc_match:
            toc_content = toc_match.group(1)
            
            # 检查目录中的链接序号
            link_pattern = r'\[([^\]]+)\]\(#[^)]+\)'
            links = re.findall(link_pattern, toc_content)
            
            for link in links:
                # 检查链接文本中的序号格式
                numbering_match = re.match(r'^(\d+(?:\.\d+)*)\s*', link)
                if numbering_match:
                    numbering = numbering_match.group(1)
                    # 验证序号格式
                    if not self.is_valid_numbering_format(numbering):
                        issues.append(f"目录中序号格式错误: {link}")
                        
        return issues
    
    def check_theorem_numbering(self, content: str, file_path: Path) -> List[str]:
        """检查定义和定理的序号"""
        issues = []
        
        # 查找定义和定理
        theorem_pattern = r'\*\*(定义|定理|公理|引理|推论)\s+(\d+(?:\.\d+)*)\*\*'
        theorems = re.findall(theorem_pattern, content)
        
        for theorem_type, numbering in theorems:
            if not self.is_valid_numbering_format(numbering):
                issues.append(f"{theorem_type}序号格式错误: {numbering}")
                
        return issues
    
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
    
    def fix_document_numbering(self, file_path: Path) -> bool:
        """修复文档中的序号问题"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            original_content = content
            fixed_content = self.apply_numbering_fixes(content, file_path)
            
            if fixed_content != original_content:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(fixed_content)
                return True
                
        except Exception as e:
            print(f"修复文件 {file_path} 时出错: {e}")
            
        return False
    
    def apply_numbering_fixes(self, content: str, file_path: Path) -> str:
        """应用序号修复"""
        expected_numbering = self.analyze_expected_numbering(file_path)
        
        # 修复标题序号
        content = self.fix_title_numbering(content, expected_numbering)
        
        # 修复目录序号
        content = self.fix_toc_numbering(content, expected_numbering)
        
        # 修复定理序号
        content = self.fix_theorem_numbering(content, expected_numbering)
        
        return content
    
    def fix_title_numbering(self, content: str, expected: Dict[str, str]) -> str:
        """修复标题序号"""
        # 分析文档结构
        lines = content.split('\n')
        fixed_lines = []
        current_numbering = {}
        
        for line in lines:
            # 检查是否是标题行
            title_match = re.match(r'^(#{1,6})\s+(.+)$', line)
            if title_match:
                level = title_match.group(1)
                title_text = title_match.group(2)
                
                # 确定应该的序号格式
                level_num = len(level)
                if level_num == 1:  # 主标题
                    if expected.get("format") != "unknown":
                        # 使用文件路径确定的序号
                        numbering = expected["format"]
                    else:
                        # 使用默认序号
                        numbering = "1"
                else:
                    # 子标题，根据层次生成序号
                    if level_num not in current_numbering:
                        current_numbering[level_num] = 1
                    else:
                        current_numbering[level_num] += 1
                    
                    # 构建层次序号
                    numbering_parts = []
                    for i in range(1, level_num + 1):
                        if i not in current_numbering:
                            current_numbering[i] = 1
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
    
    def fix_toc_numbering(self, content: str, expected: Dict[str, str]) -> str:
        """修复目录序号"""
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
                        # 这里可以根据需要修正序号
                        # 暂时保持原样
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
    
    def fix_theorem_numbering(self, content: str, expected: Dict[str, str]) -> str:
        """修复定理序号"""
        # 查找并修复定义和定理的序号
        theorem_pattern = r'\*\*(定义|定理|公理|引理|推论)\s+(\d+(?:\.\d+)*)\*\*'
        
        def replace_theorem(match):
            theorem_type = match.group(1)
            numbering = match.group(2)
            
            # 检查序号格式
            if self.is_valid_numbering_format(numbering):
                return match.group(0)  # 保持原样
            else:
                # 生成新的序号（这里简化处理）
                new_numbering = "1.1"  # 默认序号
                return f"**{theorem_type} {new_numbering}**"
        
        content = re.sub(theorem_pattern, replace_theorem, content)
        
        return content
    
    def generate_report(self, issues: Dict[str, List[str]]) -> str:
        """生成问题报告"""
        report = []
        report.append("# FormalMath 序号规范化检查报告")
        report.append(f"生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        report.append("")
        
        if not issues:
            report.append("✅ 未发现序号问题")
            return "\n".join(report)
            
        report.append(f"## 发现的问题 ({len(issues)} 个文件)")
        report.append("")
        
        for file_path, file_issues in issues.items():
            report.append(f"### {file_path}")
            for issue in file_issues:
                report.append(f"- {issue}")
            report.append("")
            
        return "\n".join(report)
    
    def run_full_check(self) -> Dict[str, List[str]]:
        """运行完整的检查流程"""
        print("🚀 开始序号规范化检查...")
        
        # 扫描所有问题
        issues = self.scan_all_documents()
        
        # 生成报告
        report = self.generate_report(issues)
        
        # 保存报告
        report_path = self.docs_path / "序号规范化检查报告.md"
        with open(report_path, 'w', encoding='utf-8') as f:
            f.write(report)
            
        print(f"📊 检查完成，发现 {len(issues)} 个文件有问题")
        print(f"📄 详细报告已保存到: {report_path}")
        
        return issues

def main():
    """主函数"""
    validator = NumberingValidator()
    
    # 运行完整检查
    issues = validator.run_full_check()
    
    # 询问是否自动修复
    if issues:
        print("\n🔧 是否要自动修复发现的问题? (y/n)")
        response = input().lower().strip()
        
        if response == 'y':
            print("🔧 开始自动修复...")
            fixed_count = 0
            
            for file_path in issues.keys():
                path = Path(file_path)
                if validator.fix_document_numbering(path):
                    fixed_count += 1
                    print(f"✅ 已修复: {file_path}")
                    
            print(f"🎉 修复完成，共修复 {fixed_count} 个文件")
        else:
            print("⏭️ 跳过自动修复")
    else:
        print("🎉 所有文档的序号都是规范的！")

if __name__ == "__main__":
    main() 