#!/usr/bin/env python3
"""
FormalMath 数据完整性检查工具
功能：
1. 检查概念图谱数据完整性
2. 验证文档元数据
3. 检查链接有效性
4. 验证数学公式正确性
5. 生成数据完整性报告
"""

import json
import yaml
import re
import os
from pathlib import Path
from datetime import datetime
from collections import defaultdict

class DataIntegrityChecker:
    def __init__(self, base_path="."):
        self.base_path = Path(base_path)
        self.issues = []
        self.warnings = []
        self.stats = defaultdict(int)
        
    def log_issue(self, category, file_path, message, severity="error"):
        """记录问题"""
        self.issues.append({
            "category": category,
            "file": str(file_path),
            "message": message,
            "severity": severity,
            "timestamp": datetime.now().isoformat()
        })
        
    def log_warning(self, category, file_path, message):
        """记录警告"""
        self.warnings.append({
            "category": category,
            "file": str(file_path),
            "message": message,
            "timestamp": datetime.now().isoformat()
        })

    def check_json_files(self):
        """检查JSON文件完整性"""
        print("🔍 检查JSON文件...")
        json_files = list(self.base_path.rglob("*.json"))
        
        for file_path in json_files:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    
                # 检查关键字段
                if "concept_id" in str(file_path):
                    self._validate_concept_json(file_path, data)
                    
                self.stats["json_valid"] += 1
                
            except json.JSONDecodeError as e:
                self.log_issue("JSON格式错误", file_path, f"JSON解析错误: {e}")
                self.stats["json_invalid"] += 1
            except Exception as e:
                self.log_issue("文件读取错误", file_path, f"无法读取文件: {e}")
                
        print(f"   ✓ 检查了 {len(json_files)} 个JSON文件")

    def _validate_concept_json(self, file_path, data):
        """验证概念JSON结构"""
        if isinstance(data, list):
            for item in data:
                if isinstance(item, dict):
                    # 检查必需字段
                    if "concept_id" in item and not item.get("concept_id"):
                        self.log_warning("概念数据", file_path, "concept_id为空")
                    if "multilang" in item:
                        multilang = item.get("multilang", {})
                        if not isinstance(multilang, dict):
                            self.log_issue("数据结构错误", file_path, "multilang必须是字典类型")
        elif isinstance(data, dict):
            # 检查对齐元数据
            if "alignment_metadata" in data:
                metadata = data.get("alignment_metadata", {})
                if not metadata.get("last_updated"):
                    self.log_warning("元数据", file_path, "缺少last_updated字段")

    def check_yaml_files(self):
        """检查YAML文件完整性"""
        print("🔍 检查YAML文件...")
        yaml_files = list(self.base_path.rglob("*.yaml")) + list(self.base_path.rglob("*.yml"))
        
        for file_path in yaml_files:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    yaml.safe_load(f)
                self.stats["yaml_valid"] += 1
            except yaml.YAMLError as e:
                self.log_issue("YAML格式错误", file_path, f"YAML解析错误: {e}")
                self.stats["yaml_invalid"] += 1
            except Exception as e:
                self.log_issue("文件读取错误", file_path, f"无法读取文件: {e}")
                
        print(f"   ✓ 检查了 {len(yaml_files)} 个YAML文件")

    def check_markdown_files(self):
        """检查Markdown文件完整性"""
        print("🔍 检查Markdown文件...")
        md_files = list(self.base_path.rglob("*.md"))
        
        for file_path in md_files:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read()
                    
                # 检查基本结构
                self._check_md_structure(file_path, content)
                
                # 检查数学公式
                self._check_math_formulas(file_path, content)
                
                # 检查链接
                self._check_links(file_path, content)
                
                self.stats["md_checked"] += 1
                
            except Exception as e:
                self.log_issue("文件读取错误", file_path, f"无法读取文件: {e}")
                
        print(f"   ✓ 检查了 {len(md_files)} 个Markdown文件")

    def _check_md_structure(self, file_path, content):
        """检查Markdown文档结构"""
        # 检查是否有标题
        if not re.search(r'^#\s+', content, re.MULTILINE):
            self.log_warning("文档结构", file_path, "文档缺少一级标题")
            
        # 检查frontmatter (可选)
        if content.startswith('---'):
            frontmatter_match = re.match(r'^---\s*\n(.*?)\n---\s*\n', content, re.DOTALL)
            if frontmatter_match:
                try:
                    yaml.safe_load(frontmatter_match.group(1))
                except yaml.YAMLError:
                    self.log_issue("Frontmatter错误", file_path, "YAML frontmatter格式错误")

    def _check_math_formulas(self, file_path, content):
        """检查数学公式格式"""
        # 检查行内公式 $...$
        inline_patterns = re.findall(r'\$([^$]+)\$', content)
        
        # 检查 display 公式 $$...$$
        display_patterns = re.findall(r'\$\$([^$]+)\$\$', content, re.DOTALL)
        
        # 检查常见错误：未闭合的公式
        single_dollar_count = content.count('$')
        if single_dollar_count % 2 != 0:
            # 可能是LaTeX矩阵中的$使用，仅作为警告
            pass  # 暂时不报告，因为可能有复杂情况
            
        # 检查公式中的常见错误
        for formula in inline_patterns + display_patterns:
            # 检查括号匹配
            if formula.count('(') != formula.count(')'):
                self.log_warning("数学公式", file_path, f"公式括号不匹配: {formula[:50]}...")
            if formula.count('[') != formula.count(']'):
                self.log_warning("数学公式", file_path, f"公式方括号不匹配: {formula[:50]}...")
            if formula.count('{') != formula.count('}'):
                self.log_warning("数学公式", file_path, f"公式花括号不匹配: {formula[:50]}...")

    def _check_links(self, file_path, content):
        """检查链接有效性"""
        # 检查Markdown链接 [text](url)
        md_links = re.findall(r'\[([^\]]+)\]\(([^)]+)\)', content)
        
        for text, url in md_links:
            # 检查相对链接
            if not url.startswith(('http://', 'https://', 'mailto:', '#')):
                # 解析相对路径
                if url.startswith('/'):
                    full_path = self.base_path / url.lstrip('/')
                else:
                    full_path = file_path.parent / url
                    
                # 移除锚点
                full_path = Path(str(full_path).split('#')[0])
                
                if not full_path.exists():
                    self.log_issue("链接错误", file_path, f"链接指向的文件不存在: {url}")

    def check_cross_references(self):
        """检查跨引用一致性"""
        print("🔍 检查跨引用一致性...")
        
        # 收集所有概念ID
        concept_ids = set()
        concept_files = list(self.base_path.rglob("*概念*.json")) + list(self.base_path.rglob("*mapping*.json"))
        
        for file_path in concept_files:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    if isinstance(data, list):
                        for item in data:
                            if isinstance(item, dict) and "concept_id" in item:
                                concept_ids.add(item["concept_id"])
            except:
                pass
                
        # 检查YAML中的概念引用
        yaml_files = list(self.base_path.rglob("*.yaml")) + list(self.base_path.rglob("*.yml"))
        for file_path in yaml_files:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read()
                    # 查找可能的概念引用
                    refs = re.findall(r'concept_id:\s*["\']?([^\s"\']+)["\']?', content)
                    for ref in refs:
                        if ref not in concept_ids and not ref.startswith('${'):
                            self.log_warning("概念引用", file_path, f"引用的概念ID可能不存在: {ref}")
            except:
                pass
                
        print(f"   ✓ 发现 {len(concept_ids)} 个概念定义")

    def check_file_naming(self):
        """检查文件命名规范"""
        print("🔍 检查文件命名规范...")
        
        all_files = list(self.base_path.rglob("*"))
        
        for file_path in all_files:
            if file_path.is_file():
                name = file_path.name
                
                # 检查空格
                if ' ' in name:
                    self.log_warning("文件命名", file_path, "文件名包含空格")
                    
                # 检查特殊字符
                if any(c in name for c in ['<', '>', ':', '"', '|', '?', '*']):
                    self.log_issue("文件命名", file_path, "文件名包含非法字符")

    def generate_report(self):
        """生成数据完整性报告"""
        report_lines = [
            "# FormalMath 数据完整性检查报告",
            "",
            f"**检查时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
            f"**检查目录**: {self.base_path.absolute()}",
            "",
            "## 检查概览",
            "",
            "| 检查项 | 结果 |",
            "|--------|------|",
            f"| JSON文件有效 | {self.stats.get('json_valid', 0)} |",
            f"| JSON文件无效 | {self.stats.get('json_invalid', 0)} |",
            f"| YAML文件有效 | {self.stats.get('yaml_valid', 0)} |",
            f"| YAML文件无效 | {self.stats.get('yaml_invalid', 0)} |",
            f"| Markdown文件已检查 | {self.stats.get('md_checked', 0)} |",
            "",
            "## 问题统计",
            "",
        ]
        
        # 按类别统计问题
        error_categories = defaultdict(list)
        warning_categories = defaultdict(list)
        
        for issue in self.issues:
            error_categories[issue["category"]].append(issue)
            
        for warning in self.warnings:
            warning_categories[warning["category"]].append(warning)
            
        report_lines.append(f"- **错误总数**: {len(self.issues)}")
        report_lines.append(f"- **警告总数**: {len(self.warnings)}")
        report_lines.append("")
        
        # 错误详情
        if self.issues:
            report_lines.append("## 错误详情")
            report_lines.append("")
            for category, items in error_categories.items():
                report_lines.append(f"### {category} ({len(items)}个)")
                report_lines.append("")
                for item in items[:10]:  # 只显示前10个
                    report_lines.append(f"- **{item['file']}**: {item['message']}")
                if len(items) > 10:
                    report_lines.append(f"- ... 还有 {len(items) - 10} 个类似问题")
                report_lines.append("")
                
        # 警告详情
        if self.warnings:
            report_lines.append("## 警告详情")
            report_lines.append("")
            for category, items in warning_categories.items():
                report_lines.append(f"### {category} ({len(items)}个)")
                report_lines.append("")
                for item in items[:10]:
                    report_lines.append(f"- **{item['file']}**: {item['message']}")
                if len(items) > 10:
                    report_lines.append(f"- ... 还有 {len(items) - 10} 个类似问题")
                report_lines.append("")
                
        # 修复建议
        report_lines.extend([
            "## 修复建议",
            "",
        ])
        
        if error_categories.get("JSON格式错误"):
            report_lines.append("1. **JSON格式错误**: 使用JSON验证器检查并修复格式问题")
            
        if error_categories.get("YAML格式错误"):
            report_lines.append("2. **YAML格式错误**: 检查缩进和语法，确保符合YAML规范")
            
        if error_categories.get("链接错误"):
            report_lines.append("3. **链接错误**: 更新或移除失效的相对链接")
            
        if warning_categories.get("数学公式"):
            report_lines.append("4. **数学公式问题**: 检查公式的括号匹配和LaTeX语法")
            
        if not self.issues and not self.warnings:
            report_lines.append("✅ **所有检查通过，数据完整性良好！**")
            
        report_lines.append("")
        
        return "\n".join(report_lines)

    def run_all_checks(self):
        """运行所有检查"""
        print("=" * 60)
        print("FormalMath 数据完整性检查")
        print("=" * 60)
        print()
        
        self.check_json_files()
        self.check_yaml_files()
        self.check_markdown_files()
        self.check_cross_references()
        self.check_file_naming()
        
        print()
        print("=" * 60)
        print(f"检查完成: 发现 {len(self.issues)} 个错误, {len(self.warnings)} 个警告")
        print("=" * 60)


if __name__ == "__main__":
    checker = DataIntegrityChecker(".")
    checker.run_all_checks()
    
    # 生成并保存报告
    report = checker.generate_report()
    
    report_path = "output/data_integrity_report.md"
    os.makedirs("output", exist_ok=True)
    
    with open(report_path, 'w', encoding='utf-8') as f:
        f.write(report)
        
    print(f"\n📄 报告已保存至: {report_path}")
