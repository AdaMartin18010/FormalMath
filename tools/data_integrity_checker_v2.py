#!/usr/bin/env python3
"""
FormalMath 数据完整性检查工具 V2
改进：过滤误报，聚焦核心问题
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
        self.excluded_patterns = [
            'node_modules',
            '.git',
            '.vscode',
            '__pycache__',
            '00-归档'
        ]
        
    def should_check(self, file_path):
        """检查是否应该检查该文件"""
        path_str = str(file_path)
        for pattern in self.excluded_patterns:
            if pattern in path_str:
                return False
        return True
        
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
        json_files = [f for f in self.base_path.rglob("*.json") if self.should_check(f)]
        
        for file_path in json_files:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    
                # 检查关键字段
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
                    if "concept_id" in item and not item.get("concept_id"):
                        self.log_warning("概念数据", file_path, "concept_id为空")
        elif isinstance(data, dict):
            if "alignment_metadata" in data:
                metadata = data.get("alignment_metadata", {})
                if not metadata.get("last_updated"):
                    self.log_warning("元数据", file_path, "缺少last_updated字段")

    def check_yaml_files(self):
        """检查YAML文件完整性"""
        print("🔍 检查YAML文件...")
        yaml_files = [f for f in (list(self.base_path.rglob("*.yaml")) + list(self.base_path.rglob("*.yml"))) 
                      if self.should_check(f)]
        
        for file_path in yaml_files:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read()
                    
                # 跳过多文档YAML（Kubernetes配置等）
                if '---' in content and content.count('---') > 1:
                    self.stats["yaml_multi_doc"] += 1
                    continue
                    
                yaml.safe_load(content)
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
        md_files = [f for f in self.base_path.rglob("*.md") if self.should_check(f)]
        
        for file_path in md_files:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read()
                    
                # 检查基本结构
                self._check_md_structure(file_path, content)
                
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
            # 跳过短文件和模板文件
            if len(content) > 500 and 'template' not in str(file_path).lower():
                self.log_warning("文档结构", file_path, "文档缺少一级标题")

    def _check_links(self, file_path, content):
        """检查链接有效性"""
        # 检查Markdown链接 [text](url)
        md_links = re.findall(r'\[([^\]]+)\]\(([^)]+)\)', content)
        
        for text, url in md_links:
            # 跳过外部链接和锚点链接
            if url.startswith(('http://', 'https://', 'mailto:')):
                continue
            if url.startswith('#'):
                continue
                
            # 检查相对链接
            if url.startswith('/'):
                full_path = self.base_path / url.lstrip('/')
            else:
                full_path = file_path.parent / url
                
            # 移除锚点
            full_path = Path(str(full_path).split('#')[0])
            
            # 检查文件是否存在
            if not full_path.exists():
                # 尝试添加.md后缀
                if not str(full_path).endswith('.md'):
                    full_path_md = Path(str(full_path) + '.md')
                    if full_path_md.exists():
                        continue
                        
                # 跳过一些已知的可能不存在路径
                if any(x in str(url) for x in ['../../issues', '../../discussions', '../../pulls']):
                    continue
                    
                self.log_issue("链接错误", file_path, f"链接指向的文件不存在: {url}")

    def check_cross_references(self):
        """检查跨引用一致性"""
        print("🔍 检查跨引用一致性...")
        
        # 收集所有概念ID
        concept_ids = set()
        concept_files = [
            f for f in (list(self.base_path.rglob("*概念*.json")) + 
                       list(self.base_path.rglob("*mapping*.json")) +
                       list(self.base_path.rglob("*mapping*.yaml")))
            if self.should_check(f)
        ]
        
        for file_path in concept_files:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    if file_path.suffix == '.json':
                        data = json.load(f)
                    else:
                        data = yaml.safe_load(f)
                        
                if isinstance(data, list):
                    for item in data:
                        if isinstance(item, dict) and "concept_id" in item:
                            concept_ids.add(item["concept_id"])
                elif isinstance(data, dict):
                    # 递归查找concept_id
                    def find_concept_ids(obj):
                        if isinstance(obj, dict):
                            if "concept_id" in obj:
                                concept_ids.add(obj["concept_id"])
                            for v in obj.values():
                                find_concept_ids(v)
                        elif isinstance(obj, list):
                            for item in obj:
                                find_concept_ids(item)
                    find_concept_ids(data)
            except:
                pass
                
        # 检查YAML中的概念引用
        yaml_files = [f for f in (list(self.base_path.rglob("*.yaml")) + list(self.base_path.rglob("*.yml")))
                      if self.should_check(f)]
                      
        for file_path in yaml_files:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read()
                    
                # 查找可能的概念引用
                refs = re.findall(r'concept_id:\s*["\']?([^\s"\']+)["\']?', content)
                for ref in refs:
                    if ref not in concept_ids and not ref.startswith(('${', '{', '[')):
                        self.log_warning("概念引用", file_path, f"引用的概念ID可能不存在: {ref}")
            except:
                pass
                
        print(f"   ✓ 发现 {len(concept_ids)} 个概念定义")

    def check_file_naming(self):
        """检查文件命名规范"""
        print("🔍 检查文件命名规范...")
        
        all_files = [f for f in self.base_path.rglob("*") if self.should_check(f)]
        
        for file_path in all_files:
            if file_path.is_file():
                name = file_path.name
                
                # 检查空格（仅针对项目核心文件）
                if ' ' in name:
                    # 跳过某些允许空格的情况
                    if any(x in str(file_path) for x in ['工作示例', '核心定理']):
                        self.log_warning("文件命名", file_path, "文件名包含空格（建议使用中横线或下划线）")

    def generate_report(self):
        """生成数据完整性报告"""
        report_lines = [
            "# FormalMath 数据完整性检查报告",
            "",
            f"**检查时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
            f"**检查目录**: {self.base_path.absolute()}",
            f"**检查范围**: 排除 node_modules, .git, .vscode, 00-归档",
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
            report_lines.append("## 错误详情 (需要修复)")
            report_lines.append("")
            for category, items in sorted(error_categories.items()):
                report_lines.append(f"### {category} ({len(items)}个)")
                report_lines.append("")
                # 去重并限制数量
                seen = set()
                unique_items = []
                for item in items:
                    key = (item['file'], item['message'])
                    if key not in seen:
                        seen.add(key)
                        unique_items.append(item)
                        
                for item in unique_items[:20]:
                    report_lines.append(f"- **{item['file']}**: {item['message']}")
                if len(unique_items) > 20:
                    report_lines.append(f"- ... 还有 {len(unique_items) - 20} 个类似问题")
                report_lines.append("")
                
        # 警告详情
        if self.warnings:
            report_lines.append("## 警告详情 (建议优化)")
            report_lines.append("")
            for category, items in sorted(warning_categories.items()):
                report_lines.append(f"### {category} ({len(items)}个)")
                report_lines.append("")
                seen = set()
                unique_items = []
                for item in items:
                    key = (item['file'], item['message'])
                    if key not in seen:
                        seen.add(key)
                        unique_items.append(item)
                        
                for item in unique_items[:15]:
                    report_lines.append(f"- **{item['file']}**: {item['message']}")
                if len(unique_items) > 15:
                    report_lines.append(f"- ... 还有 {len(unique_items) - 15} 个类似问题")
                report_lines.append("")
                
        # 修复建议
        report_lines.extend([
            "## 修复建议",
            "",
        ])
        
        if error_categories.get("JSON格式错误"):
            report_lines.append("### JSON格式错误")
            report_lines.append("1. 使用JSON验证器（如 jsonlint.com）检查文件")
            report_lines.append("2. 修复引号、逗号等语法问题")
            report_lines.append("")
            
        if error_categories.get("YAML格式错误"):
            report_lines.append("### YAML格式错误")
            report_lines.append("1. 检查缩进（使用空格而非Tab）")
            report_lines.append("2. 确保特殊字符正确转义")
            report_lines.append("3. 检查冒号后是否有空格")
            report_lines.append("")
            
        if error_categories.get("链接错误"):
            report_lines.append("### 链接错误")
            report_lines.append("1. 更新失效的相对链接指向正确的文件路径")
            report_lines.append("2. 对于已删除的文件，移除相关链接")
            report_lines.append("3. 使用绝对路径 `/docs/...` 或正确的相对路径 `./file.md`")
            report_lines.append("")
            
        if warning_categories.get("文件命名"):
            report_lines.append("### 文件命名")
            report_lines.append("1. 文件名中的空格替换为中横线 `-` 或下划线 `_`")
            report_lines.append("2. 避免使用特殊字符")
            report_lines.append("")
            
        if not self.issues and not self.warnings:
            report_lines.append("✅ **所有检查通过，数据完整性良好！**")
            
        report_lines.append("")
        
        return "\n".join(report_lines)

    def run_all_checks(self):
        """运行所有检查"""
        print("=" * 60)
        print("FormalMath 数据完整性检查 V2")
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
    
    report_path = "output/data_integrity_report_v2.md"
    os.makedirs("output", exist_ok=True)
    
    with open(report_path, 'w', encoding='utf-8') as f:
        f.write(report)
        
    print(f"\n📄 报告已保存至: {report_path}")
