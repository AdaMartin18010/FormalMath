#!/usr/bin/env python3
"""
FormalMath项目docs核心分支断链修复脚本
扫描并修复docs/01-基础数学/、docs/02-代数结构/、docs/03-分析学/、docs/04-几何与拓扑/中的断链问题
"""

import os
import re
import json
from pathlib import Path
from collections import defaultdict

# 项目根目录
PROJECT_ROOT = Path("G:/_src/FormalMath")
DOCS_DIR = PROJECT_ROOT / "docs"

# 目标分支
TARGET_BRANCHES = [
    "01-基础数学",
    "02-代数结构", 
    "03-分析学",
    "04-几何与拓扑"
]

# 链接匹配正则
LINK_PATTERN = re.compile(r'\[([^\]]+)\]\(([^)]+)\)')
# 锚点链接模式
ANCHOR_LINK_PATTERN = re.compile(r'^(.+?)#(.+)$')

class LinkChecker:
    def __init__(self):
        self.all_files = set()  # 所有存在的文件（相对docs的路径）
        self.all_anchors = defaultdict(set)  # 每个文件的锚点
        self.broken_links = []  # 断链列表
        self.fixed_links = []  # 修复的链接
        self.stats = {
            branch: {"broken": 0, "fixed": 0, "by_type": {"internal": 0, "cross_branch": 0, "anchor": 0}}
            for branch in TARGET_BRANCHES
        }
        
    def scan_all_files(self):
        """扫描所有目标分支的文件"""
        print("=" * 60)
        print("步骤1: 扫描所有文件...")
        print("=" * 60)
        
        for branch in TARGET_BRANCHES:
            branch_path = DOCS_DIR / branch
            if not branch_path.exists():
                print(f"警告: 分支目录不存在: {branch}")
                continue
                
            for md_file in branch_path.rglob("*.md"):
                # 计算相对于docs的路径
                rel_path = md_file.relative_to(DOCS_DIR).as_posix()
                self.all_files.add(rel_path)
                
                # 提取文件中的锚点
                anchors = self.extract_anchors(md_file)
                self.all_anchors[rel_path].update(anchors)
                
        print(f"共扫描到 {len(self.all_files)} 个Markdown文件")
        
    def extract_anchors(self, file_path):
        """提取文件中的所有锚点（标题）"""
        anchors = set()
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            # 匹配标题
            header_pattern = re.compile(r'^#{1,6}\s+(.+)$', re.MULTILINE)
            for match in header_pattern.finditer(content):
                title = match.group(1).strip()
                # 生成锚点ID (GitHub风格)
                anchor = self.generate_anchor_id(title)
                anchors.add(anchor)
                
            # 也匹配显式HTML锚点
            html_anchor_pattern = re.compile(r'<a[^>]*name=["\']([^"\']+)["\'][^>]*>', re.IGNORECASE)
            for match in html_anchor_pattern.finditer(content):
                anchors.add(match.group(1))
                
        except Exception as e:
            print(f"警告: 无法读取文件 {file_path}: {e}")
            
        return anchors
    
    def generate_anchor_id(self, title):
        """生成GitHub风格的锚点ID"""
        # 移除Markdown格式
        title = re.sub(r'<[^>]+>', '', title)
        title = re.sub(r'\[([^\]]+)\]\([^)]+\)', r'\1', title)
        # 转换为小写
        anchor = title.lower()
        # 替换空格和特殊字符为-
        anchor = re.sub(r'[^\w\s-]', '', anchor)
        anchor = re.sub(r'\s+', '-', anchor)
        anchor = anchor.strip('-')
        return anchor
    
    def check_all_links(self):
        """检查所有文件中的链接"""
        print("\n" + "=" * 60)
        print("步骤2: 检查所有链接...")
        print("=" * 60)
        
        for branch in TARGET_BRANCHES:
            branch_path = DOCS_DIR / branch
            if not branch_path.exists():
                continue
                
            for md_file in branch_path.rglob("*.md"):
                self.check_file_links(md_file, branch)
                
    def check_file_links(self, file_path, branch):
        """检查单个文件的链接"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            file_rel_path = file_path.relative_to(DOCS_DIR).as_posix()
            file_dir = file_rel_path.rsplit('/', 1)[0] if '/' in file_rel_path else ''
            
            for match in LINK_PATTERN.finditer(content):
                link_text = match.group(1)
                link_target = match.group(2)
                
                # 跳过外部链接
                if link_target.startswith(('http://', 'https://', 'mailto:')):
                    continue
                    
                # 检查链接
                self.validate_link(file_path, file_rel_path, file_dir, 
                                   link_text, link_target, branch, match)
                
        except Exception as e:
            print(f"警告: 无法检查文件 {file_path}: {e}")
            
    def validate_link(self, file_path, file_rel_path, file_dir, 
                      link_text, link_target, branch, match):
        """验证链接是否有效"""
        # 解析链接
        anchor_match = ANCHOR_LINK_PATTERN.match(link_target)
        target_file = anchor_match.group(1) if anchor_match else link_target
        anchor = anchor_match.group(2) if anchor_match else None
        
        # 确定目标文件的完整路径
        if not target_file or target_file == '':
            # 纯锚点链接，指向当前文件
            target_file = file_rel_path
        elif target_file.startswith('/'):
            # 绝对路径（相对于docs）
            target_file = target_file.lstrip('/')
        else:
            # 相对路径
            target_file = os.path.normpath(os.path.join(file_dir, target_file)).replace('\\', '/')
            
        # 检查文件是否存在
        target_exists = target_file in self.all_files
        anchor_exists = False
        
        if target_exists and anchor:
            anchor_exists = anchor in self.all_anchors[target_file]
            # 也尝试原始锚点（未转义的）
            if not anchor_exists:
                anchor_exists = anchor.replace('-', '') in [a.replace('-', '') for a in self.all_anchors[target_file]]
                
        # 记录断链
        if not target_exists:
            broken_info = {
                "file": str(file_rel_path),
                "branch": branch,
                "link_text": link_text,
                "link_target": link_target,
                "type": "file_not_found",
                "line": content[:match.start()].count('\n') + 1 if 'content' in dir() else 0
            }
            self.broken_links.append(broken_info)
            self.stats[branch]["broken"] += 1
            if target_file.startswith(tuple(b.replace('docs/', '') for b in TARGET_BRANCHES if b != branch)):
                self.stats[branch]["by_type"]["cross_branch"] += 1
            else:
                self.stats[branch]["by_type"]["internal"] += 1
                
        elif anchor and not anchor_exists:
            broken_info = {
                "file": str(file_rel_path),
                "branch": branch,
                "link_text": link_text,
                "link_target": link_target,
                "type": "anchor_not_found",
                "target_file": target_file,
                "anchor": anchor
            }
            self.broken_links.append(broken_info)
            self.stats[branch]["broken"] += 1
            self.stats[branch]["by_type"]["anchor"] += 1

    def try_fix_links(self):
        """尝试修复断链"""
        print("\n" + "=" * 60)
        print("步骤3: 尝试修复断链...")
        print("=" * 60)
        
        fixes_by_file = defaultdict(list)
        
        for broken in self.broken_links:
            fix = self.find_fix(broken)
            if fix:
                fixes_by_file[broken["file"]].append({
                    "original": broken["link_target"],
                    "fixed": fix["new_target"],
                    "link_text": broken["link_text"],
                    "fix_type": fix["type"]
                })
                self.fixed_links.append({
                    **broken,
                    "fix": fix
                })
                self.stats[broken["branch"]]["fixed"] += 1
                
        # 应用修复
        for file_rel_path, fixes in fixes_by_file.items():
            self.apply_fixes(file_rel_path, fixes)
            
    def find_fix(self, broken):
        """查找修复方案"""
        target = broken["link_target"]
        branch = broken["branch"]
        
        # 解析目标
        anchor_match = ANCHOR_LINK_PATTERN.match(target)
        target_file = anchor_match.group(1) if anchor_match else target
        anchor = anchor_match.group(2) if anchor_match else None
        
        # 策略1: 尝试找到相似文件名
        if target_file and not target_file.startswith(('http://', 'https://')):
            # 移除路径，只取文件名
            target_name = target_file.split('/')[-1].replace('.md', '')
            
            # 在目标分支中搜索
            for existing_file in self.all_files:
                if not existing_file.startswith(branch):
                    continue
                    
                existing_name = existing_file.split('/')[-1].replace('.md', '')
                
                # 完全匹配
                if target_name == existing_name:
                    new_target = existing_file.replace(f"{branch}/", "")
                    if anchor:
                        # 检查锚点是否存在
                        if anchor in self.all_anchors[existing_file]:
                            return {"new_target": f"{new_target}#{anchor}", "type": "correct_path"}
                        else:
                            # 尝试找到相似锚点
                            similar_anchor = self.find_similar_anchor(anchor, self.all_anchors[existing_file])
                            if similar_anchor:
                                return {"new_target": f"{new_target}#{similar_anchor}", "type": "correct_path_and_anchor"}
                            return {"new_target": new_target, "type": "correct_path_remove_anchor"}
                    return {"new_target": new_target, "type": "correct_path"}
                    
                # 模糊匹配
                if self.similar_names(target_name, existing_name):
                    new_target = existing_file.replace(f"{branch}/", "")
                    if anchor:
                        new_target += f"#{anchor}"
                    return {"new_target": new_target, "type": "fuzzy_match"}
                    
        # 策略2: 跨分支链接修复
        if target_file:
            target_name = target_file.split('/')[-1].replace('.md', '')
            
            # 在其他分支中搜索
            for existing_file in self.all_files:
                if existing_file.startswith(branch):
                    continue
                    
                existing_name = existing_file.split('/')[-1].replace('.md', '')
                
                if target_name == existing_name or self.similar_names(target_name, existing_name):
                    # 计算跨分支相对路径
                    current_branch = broken["file"].split('/')[0]
                    target_branch = existing_file.split('/')[0]
                    
                    # 构建相对路径
                    rel_path = "../" * (len(broken["file"].split('/')) - 1)
                    new_target = rel_path + existing_file
                    
                    if anchor:
                        # 检查锚点
                        if anchor in self.all_anchors[existing_file]:
                            new_target += f"#{anchor}"
                        else:
                            similar_anchor = self.find_similar_anchor(anchor, self.all_anchors[existing_file])
                            if similar_anchor:
                                new_target += f"#{similar_anchor}"
                            else:
                                # 不添加锚点
                                pass
                                
                    return {"new_target": new_target, "type": "cross_branch_fix"}
                    
        # 策略3: 锚点修复
        if anchor and target_file:
            # 找到实际存在的文件
            actual_file = None
            for f in self.all_files:
                if f.endswith(target_file.split('/')[-1]):
                    actual_file = f
                    break
                    
            if actual_file:
                similar_anchor = self.find_similar_anchor(anchor, self.all_anchors[actual_file])
                if similar_anchor:
                    new_target = target_file + f"#{similar_anchor}" if target_file else f"#{similar_anchor}"
                    return {"new_target": new_target, "type": "anchor_correction"}
                    
        return None
    
    def similar_names(self, name1, name2):
        """检查两个名称是否相似"""
        # 移除常见后缀和分隔符
        def normalize(n):
            n = n.lower()
            n = re.sub(r'[-_\s]+', '', n)
            n = re.sub(r'\d+', '', n)
            n = re.sub(r'深度版|增强版|扩展版|国际标准版|基础|入门', '', n)
            return n
            
        n1, n2 = normalize(name1), normalize(name2)
        
        # 编辑距离或包含关系
        if n1 == n2:
            return True
        if len(n1) > 3 and len(n2) > 3:
            if n1 in n2 or n2 in n1:
                return True
                
        return False
    
    def find_similar_anchor(self, anchor, available_anchors):
        """找到相似的锚点"""
        anchor_normalized = anchor.lower().replace('-', '').replace('_', '')
        
        for avail in available_anchors:
            avail_normalized = avail.lower().replace('-', '').replace('_', '')
            if anchor_normalized == avail_normalized:
                return avail
            if anchor_normalized in avail_normalized or avail_normalized in anchor_normalized:
                if len(anchor_normalized) > 5:
                    return avail
                    
        return None
    
    def apply_fixes(self, file_rel_path, fixes):
        """应用修复到文件"""
        file_path = DOCS_DIR / file_rel_path
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            original_content = content
            
            for fix in fixes:
                # 转义正则特殊字符
                old_target = fix["original"]
                new_target = fix["new_target"]
                link_text = fix["link_text"]
                
                # 构建替换模式
                pattern = f'\\[{re.escape(link_text)}\\]\\({re.escape(old_target)}\\)'
                replacement = f'[{link_text}]({new_target})'
                
                content = re.sub(pattern, replacement, content)
                
            if content != original_content:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(content)
                print(f"  已修复: {file_rel_path} ({len(fixes)} 处)")
                
        except Exception as e:
            print(f"  错误: 无法修复 {file_rel_path}: {e}")

    def generate_report(self):
        """生成修复报告"""
        print("\n" + "=" * 60)
        print("步骤4: 生成报告...")
        print("=" * 60)
        
        report_lines = []
        report_lines.append("# FormalMath核心分支断链修复报告")
        report_lines.append("")
        report_lines.append(f"**生成时间**: 2026年4月")
        report_lines.append(f"**扫描范围**: docs/01-基础数学, docs/02-代数结构, docs/03-分析学, docs/04-几何与拓扑")
        report_lines.append("")
        
        # 统计摘要
        report_lines.append("## 修复统计摘要")
        report_lines.append("")
        total_broken = sum(s["broken"] for s in self.stats.values())
        total_fixed = sum(s["fixed"] for s in self.stats.values())
        
        report_lines.append(f"- **总断链数**: {total_broken}")
        report_lines.append(f"- **成功修复**: {total_fixed}")
        report_lines.append(f"- **修复率**: {(total_fixed/total_broken*100) if total_broken > 0 else 0:.1f}%")
        report_lines.append("")
        
        # 分支统计
        report_lines.append("### 各分支断链统计")
        report_lines.append("")
        report_lines.append("| 分支 | 断链数 | 修复数 | 修复率 | 内部链接 | 跨分支 | 锚点问题 |")
        report_lines.append("|------|--------|--------|--------|----------|--------|----------|")
        
        for branch in TARGET_BRANCHES:
            s = self.stats[branch]
            rate = (s["fixed"]/s["broken"]*100) if s["broken"] > 0 else 0
            report_lines.append(
                f"| {branch} | {s['broken']} | {s['fixed']} | {rate:.1f}% | "
                f"{s['by_type']['internal']} | {s['by_type']['cross_branch']} | {s['by_type']['anchor']} |"
            )
        report_lines.append("")
        
        # 修复详情
        if self.fixed_links:
            report_lines.append("## 修复详情")
            report_lines.append("")
            
            current_branch = None
            for fixed in self.fixed_links:
                if fixed["branch"] != current_branch:
                    current_branch = fixed["branch"]
                    report_lines.append(f"### {current_branch}")
                    report_lines.append("")
                    
                report_lines.append(f"**文件**: `{fixed['file']}`")
                report_lines.append(f"- 链接文本: {fixed['link_text']}")
                report_lines.append(f"- 原链接: `{fixed['link_target']}`")
                report_lines.append(f"- 修复后: `{fixed['fix']['new_target']}`")
                report_lines.append(f"- 修复类型: {fixed['fix']['type']}")
                report_lines.append("")
                
        # 未修复的断链
        unfixed = [b for b in self.broken_links if not any(f['file'] == b['file'] and f['link_target'] == b['link_target'] for f in self.fixed_links)]
        if unfixed:
            report_lines.append("## 未修复的断链（需人工处理）")
            report_lines.append("")
            
            current_branch = None
            for broken in unfixed:
                if broken["branch"] != current_branch:
                    current_branch = broken["branch"]
                    report_lines.append(f"### {current_branch}")
                    report_lines.append("")
                    
                report_lines.append(f"**文件**: `{broken['file']}`")
                report_lines.append(f"- 链接文本: {broken['link_text']}")
                report_lines.append(f"- 断链: `{broken['link_target']}`")
                report_lines.append(f"- 类型: {broken['type']}")
                report_lines.append("")
                
        # 修复策略说明
        report_lines.append("## 修复策略说明")
        report_lines.append("")
        report_lines.append("### 修复类型定义")
        report_lines.append("")
        report_lines.append("| 修复类型 | 说明 |")
        report_lines.append("|----------|------|")
        report_lines.append("| correct_path | 修正为正确的相对路径 |")
        report_lines.append("| correct_path_and_anchor | 修正路径和锚点 |")
        report_lines.append("| correct_path_remove_anchor | 修正路径，移除无效锚点 |")
        report_lines.append("| fuzzy_match | 通过模糊匹配找到相似文件 |")
        report_lines.append("| cross_branch_fix | 修复跨分支链接路径 |")
        report_lines.append("| anchor_correction | 修正锚点ID |")
        report_lines.append("")
        
        report_lines.append("### 修复规则")
        report_lines.append("")
        report_lines.append("1. **内部链接**: 在同一分支内，修正为正确的相对路径")
        report_lines.append("2. **跨分支链接**: 使用`../`导航到正确分支")
        report_lines.append("3. **锚点问题**: ")
        report_lines.append("   - 尝试找到相似的标题锚点")
        report_lines.append("   - 若无法匹配，则移除锚点保留文件链接")
        report_lines.append("")
        
        # 写入报告
        report_path = PROJECT_ROOT / "00-核心分支断链修复报告.md"
        with open(report_path, 'w', encoding='utf-8') as f:
            f.write('\n'.join(report_lines))
            
        print(f"报告已生成: {report_path}")
        return report_path

    def run(self):
        """执行完整流程"""
        print("=" * 60)
        print("FormalMath核心分支断链修复工具")
        print("=" * 60)
        
        self.scan_all_files()
        self.check_all_links()
        self.try_fix_links()
        report_path = self.generate_report()
        
        print("\n" + "=" * 60)
        print("修复完成!")
        print(f"统计: 断链 {sum(s['broken'] for s in self.stats.values())}, "
              f"修复 {sum(s['fixed'] for s in self.stats.values())}")
        print(f"报告: {report_path}")
        print("=" * 60)


if __name__ == "__main__":
    checker = LinkChecker()
    checker.run()
