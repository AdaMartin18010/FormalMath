#!/usr/bin/env python3
"""
FormalMath 数据完整性修复工具
自动修复常见的数据完整性问题
"""

import json
import yaml
import re
import os
import shutil
from pathlib import Path
from datetime import datetime

class DataIntegrityFixer:
    def __init__(self, base_path="."):
        self.base_path = Path(base_path)
        self.fixes = []
        
    def log_fix(self, file_path, issue, action):
        """记录修复操作"""
        self.fixes.append({
            "file": str(file_path),
            "issue": issue,
            "action": action,
            "timestamp": datetime.now().isoformat()
        })
        print(f"  ✓ {file_path}: {action}")

    def fix_yaml_quotes(self):
        """修复YAML文件中的引号问题"""
        print("🔧 修复YAML引号问题...")
        
        yaml_files = list(self.base_path.rglob("*.yaml")) + list(self.base_path.rglob("*.yml"))
        
        for file_path in yaml_files:
            # 跳过特定目录
            if any(x in str(file_path) for x in ['node_modules', '.git', 'k8s']):
                continue
                
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read()
                    
                original_content = content
                
                # 修复中文引号嵌套问题："..."..." -> "...'...' 或使用转义
                # 查找 "..."..." 模式（中文引号嵌套）
                pattern = r'"([^"]*"[^"]*)"'
                
                def fix_nested_quotes(match):
                    inner = match.group(1)
                    # 将内部的 " 替换为 '
                    fixed = inner.replace('"', "'")
                    return f'"{fixed}"'
                
                content = re.sub(pattern, fix_nested_quotes, content)
                
                if content != original_content:
                    # 备份原文件
                    backup_path = str(file_path) + ".backup"
                    shutil.copy2(file_path, backup_path)
                    
                    with open(file_path, 'w', encoding='utf-8') as f:
                        f.write(content)
                        
                    self.log_fix(file_path, "中文引号嵌套", "修复引号嵌套问题")
                    
            except Exception as e:
                print(f"  ✗ {file_path}: 无法修复 - {e}")

    def fix_json_escapes(self):
        """修复JSON转义问题"""
        print("🔧 修复JSON转义问题...")
        
        # 修复 UPMC-french-mathematical-terminology.json
        target_file = self.base_path / "project" / "UPMC-french-mathematical-terminology.json"
        if target_file.exists():
            try:
                with open(target_file, 'r', encoding='utf-8') as f:
                    content = f.read()
                    
                # 修复常见的JSON转义问题
                # Windows路径中的反斜杠需要转义
                content = content.replace('\\', '\\\\')
                # 但不要把已经转义的双反斜杠变成四反斜杠
                content = content.replace('\\\\\\\\', '\\\\')
                
                # 尝试解析修复后的内容
                try:
                    json.loads(content)
                    
                    backup_path = str(target_file) + ".backup"
                    shutil.copy2(target_file, backup_path)
                    
                    with open(target_file, 'w', encoding='utf-8') as f:
                        f.write(content)
                        
                    self.log_fix(target_file, "JSON转义错误", "修复反斜杠转义")
                except json.JSONDecodeError:
                    print(f"  ✗ {target_file}: 修复后仍无法解析，跳过")
                    
            except Exception as e:
                print(f"  ✗ {target_file}: 无法修复 - {e}")

    def add_missing_headers(self):
        """为缺少标题的文档添加标题"""
        print("🔧 检查并添加缺失的文档标题...")
        
        md_files = list(self.base_path.rglob("*.md"))
        
        for file_path in md_files:
            if any(x in str(file_path) for x in ['node_modules', '.git', '00-归档']):
                continue
                
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read()
                    
                # 检查是否有一级标题
                if not re.search(r'^#\s+', content, re.MULTILINE):
                    # 生成标题
                    title = file_path.stem.replace('-', ' ').replace('_', ' ')
                    
                    # 跳过非常短的文件
                    if len(content) < 200:
                        continue
                        
                    # 添加标题
                    new_content = f"# {title}\n\n{content}"
                    
                    backup_path = str(file_path) + ".backup"
                    shutil.copy2(file_path, backup_path)
                    
                    with open(file_path, 'w', encoding='utf-8') as f:
                        f.write(new_content)
                        
                    self.log_fix(file_path, "缺少文档标题", f"添加标题: {title}")
                    
            except Exception as e:
                print(f"  ✗ {file_path}: 无法修复 - {e}")

    def generate_fix_report(self):
        """生成修复报告"""
        report_lines = [
            "# FormalMath 数据完整性修复报告",
            "",
            f"**修复时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
            f"**修复总数**: {len(self.fixes)}",
            "",
            "## 修复详情",
            "",
        ]
        
        if self.fixes:
            for fix in self.fixes:
                report_lines.append(f"- **{fix['file']}**")
                report_lines.append(f"  - 问题: {fix['issue']}")
                report_lines.append(f"  - 操作: {fix['action']}")
                report_lines.append("")
        else:
            report_lines.append("未进行任何修复操作")
            
        report_lines.extend([
            "",
            "## 备份文件",
            "",
            "所有被修改的文件都有 `.backup` 备份。如需恢复，请运行：",
            "```powershell",
            r"Get-ChildItem -Recurse -Filter '*.backup' | ForEach-Object { Move-Item $_.FullName ($_.FullName -replace '\.backup$', '') -Force }",
            "```",
            "",
        ])
        
        return "\n".join(report_lines)

    def run_fixes(self):
        """运行所有修复"""
        print("=" * 60)
        print("FormalMath 数据完整性修复")
        print("=" * 60)
        print()
        
        self.fix_yaml_quotes()
        self.fix_json_escapes()
        self.add_missing_headers()
        
        print()
        print("=" * 60)
        print(f"修复完成: 共修复 {len(self.fixes)} 个问题")
        print("=" * 60)


if __name__ == "__main__":
    fixer = DataIntegrityFixer(".")
    fixer.run_fixes()
    
    # 生成并保存报告
    report = fixer.generate_fix_report()
    
    report_path = "output/data_integrity_fix_report.md"
    os.makedirs("output", exist_ok=True)
    
    with open(report_path, 'w', encoding='utf-8') as f:
        f.write(report)
        
    print(f"\n📄 修复报告已保存至: {report_path}")
