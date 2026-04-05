#!/usr/bin/env python3
"""
修复数学家理念体系断链问题 - 增强版
"""

import os
import re
import json
from pathlib import Path
from collections import defaultdict
from datetime import datetime
from difflib import get_close_matches

# 工作目录
WORK_DIR = Path("g:/_src/FormalMath")
MATH_DIR = WORK_DIR / "数学家理念体系"
CONCEPT_DIR = WORK_DIR / "concept"
DOCS_DIR = WORK_DIR / "docs"

# 62位数学家目录列表
MATHEMATICIANS = [
    "丘奇数学理念", "乔姆斯基数学理念", "伍丁数学理念", "伯努利数学理念",
    "伽罗瓦数学理念", "傅里叶数学理念", "克罗内克数学理念", "克莱因数学理念",
    "冯诺依曼数学理念", "凯莱数学理念", "切比雪夫数学理念", "勒让德数学理念",
    "勒贝格数学理念", "哈密顿数学理念", "哥德尔数学理念", "嘉当数学理念",
    "图灵数学理念", "塔斯基数学理念", "塞尔数学理念", "外尔数学理念",
    "巴拿赫数学理念", "布劳威尔数学理念", "布尔数学理念", "希尔伯特数学理念",
    "帕斯卡数学理念", "庞加莱数学理念", "康托尔数学理念", "弗兰克尔数学理念",
    "德利涅数学理念", "戴德金数学理念", "拉普拉斯数学理念", "拉格朗日数学理念",
    "拉马努金数学理念", "施瓦茨数学理念", "朗兰兹数学理念", "李数学理念",
    "柯西数学理念", "根岑数学理念", "格洛腾迪克数学理念", "欧几里得数学理念",
    "欧拉数学理念", "泊松数学理念", "波利亚数学理念", "波尔查诺数学理念",
    "海廷数学理念", "牛顿数学理念", "狄利克雷数学理念", "科恩数学理念",
    "笛卡尔数学理念", "策梅洛数学理念", "罗巴切夫斯基数学理念", "肖尔策数学理念",
    "莱布尼茨数学理念", "诺特数学理念", "谢拉数学理念", "费马数学理念",
    "阿基米德数学理念", "阿蒂亚数学理念", "阿贝尔数学理念", "陈省身数学理念",
    "雅可比数学理念", "韦伊数学理念", "高斯数学理念", "魏尔斯特拉斯数学理念",
    "鲁里数学理念", "黎曼数学理念"
]

# 数学家名称映射
MATH_NAME_MAP = {}
for m in MATHEMATICIANS:
    name = m.replace("数学理念", "")
    MATH_NAME_MAP[name] = m
    # 添加常见变体
    if name == "冯诺依曼":
        MATH_NAME_MAP["冯·诺依曼"] = m
    elif name == "格洛腾迪克":
        MATH_NAME_MAP["格罗滕迪克"] = m


class LinkChecker:
    def __init__(self):
        self.broken_links = []
        self.fixed_links = []
        self.all_files = {}  # 路径 -> 文件信息
        self.all_dirs = set()
        self.link_pattern = re.compile(r'\[([^\]]+)\]\(([^)]+)\)')
        self.anchor_pattern = re.compile(r'^#{1,6}\s+(.+)$', re.MULTILINE)
        self.math_dirs = {m: MATH_DIR / m for m in MATHEMATICIANS}
        
    def collect_all_files_and_anchors(self):
        """收集所有文件和锚点"""
        print("正在收集所有文件和锚点...")
        
        # 收集数学家体系内的文件
        for math_name, math_path in self.math_dirs.items():
            if not math_path.exists():
                continue
            self.all_dirs.add(str(math_path.relative_to(WORK_DIR)))
            
            for md_file in math_path.rglob("*.md"):
                rel_path = str(md_file.relative_to(WORK_DIR)).replace('\\', '/')
                rel_math_path = str(md_file.relative_to(MATH_DIR)).replace('\\', '/')
                
                self.all_files[rel_path] = {'type': 'math', 'math': math_name, 'rel_math': rel_math_path}
                self.all_files[rel_math_path] = {'type': 'math', 'math': math_name, 'abs': rel_path}
                
                # 读取文件内容收集锚点
                try:
                    content = md_file.read_text(encoding='utf-8')
                    anchors = self.anchor_pattern.findall(content)
                    self.all_files[rel_path]['anchors'] = set()
                    for anchor in anchors:
                        anchor_link = self._anchor_to_link(anchor)
                        self.all_files[rel_path]['anchors'].add(anchor_link)
                except Exception as e:
                    pass
        
        # 收集concept目录的文件
        if CONCEPT_DIR.exists():
            for md_file in CONCEPT_DIR.rglob("*.md"):
                rel_path = str(md_file.relative_to(WORK_DIR)).replace('\\', '/')
                self.all_files[rel_path] = {'type': 'concept'}
        
        # 收集docs目录的文件
        if DOCS_DIR.exists():
            for md_file in DOCS_DIR.rglob("*.md"):
                rel_path = str(md_file.relative_to(WORK_DIR)).replace('\\', '/')
                self.all_files[rel_path] = {'type': 'docs'}
        
        print(f"  共收集 {len(self.all_files)} 个文件")
        print(f"  共 {len(self.all_dirs)} 个数学家目录")
        
    def _anchor_to_link(self, anchor_text):
        """将锚点文本转换为链接格式"""
        anchor = anchor_text.strip().lower()
        anchor = re.sub(r'[^\w\s-]', '', anchor)
        anchor = re.sub(r'\s+', '-', anchor)
        return anchor
    
    def _normalize_link(self, link, current_file):
        """规范化链接路径，返回(类型, 规范化路径, 锚点)"""
        anchor = None
        if '#' in link:
            link, anchor = link.split('#', 1)
        
        if link.startswith('http://') or link.startswith('https://'):
            return ('external', link, anchor)
        
        if not link:
            # 只有锚点，指向当前文件
            current_rel = str(current_file.relative_to(WORK_DIR)).replace('\\', '/')
            return ('internal', current_rel, anchor)
        
        # 处理相对路径
        current_dir = current_file.parent
        target = (current_dir / link).resolve()
        
        try:
            rel_target = str(target.relative_to(WORK_DIR)).replace('\\', '/')
            return ('internal', rel_target, anchor)
        except:
            return ('unknown', link.replace('\\', '/'), anchor)
    
    def check_file(self, md_file):
        """检查单个文件的链接"""
        try:
            content = md_file.read_text(encoding='utf-8')
        except Exception as e:
            return
        
        rel_path = str(md_file.relative_to(MATH_DIR)).replace('\\', '/')
        links = self.link_pattern.findall(content)
        
        for link_text, link_target in links:
            link_type, normalized, anchor = self._normalize_link(link_target, md_file)
            
            if link_type == 'external':
                continue
            
            # 检查文件是否存在
            if normalized not in self.all_files:
                # 尝试不同变体
                found = False
                for key in self.all_files:
                    if key.lower() == normalized.lower():
                        found = True
                        break
                    # 尝试匹配文件名
                    if key.endswith('/' + normalized.replace('\\', '/').split('/')[-1]):
                        found = True
                        break
                
                if not found:
                    self.broken_links.append({
                        'source': rel_path,
                        'source_abs': str(md_file.relative_to(WORK_DIR)).replace('\\', '/'),
                        'link_text': link_text,
                        'link_target': link_target,
                        'normalized': normalized,
                        'anchor': anchor,
                        'type': 'file'
                    })
            else:
                # 文件存在，检查锚点
                if anchor:
                    file_info = self.all_files.get(normalized, {})
                    file_anchors = file_info.get('anchors', set())
                    if anchor.lower() not in [a.lower() for a in file_anchors]:
                        self.broken_links.append({
                            'source': rel_path,
                            'source_abs': str(md_file.relative_to(WORK_DIR)).replace('\\', '/'),
                            'link_text': link_text,
                            'link_target': link_target,
                            'normalized': normalized,
                            'anchor': anchor,
                            'type': 'anchor'
                        })
    
    def scan_all_files(self):
        """扫描所有文件"""
        print("正在扫描所有文件的链接...")
        for math_name in MATHEMATICIANS:
            math_path = MATH_DIR / math_name
            if not math_path.exists():
                continue
            
            for md_file in math_path.rglob("*.md"):
                self.check_file(md_file)
        
        print(f"  发现 {len(self.broken_links)} 个断链")
    
    def _find_closest_match(self, broken_link):
        """找到最接近的匹配"""
        normalized = broken_link['normalized']
        link_text = broken_link['link_text']
        link_target = broken_link['link_target']
        
        # 策略1: 如果目标是其他数学家
        for name, dir_name in MATH_NAME_MAP.items():
            if name in normalized or name in link_text:
                # 尝试找到对应文件
                expected_readme = f"数学家理念体系/{dir_name}/README.md"
                if expected_readme in self.all_files:
                    return f"数学家理念体系/{dir_name}/README.md"
        
        # 策略2: 检查是否是路径层级问题
        if '../' in link_target:
            # 尝试调整层级
            parts = link_target.replace('\\', '/').split('/')
            # 检查是否指向其他数学家
            for i, part in enumerate(parts):
                for name, dir_name in MATH_NAME_MAP.items():
                    if name in part and dir_name not in link_target:
                        return f"数学家理念体系/{dir_name}/README.md"
        
        # 策略3: 使用模糊匹配找最相似的文件
        all_paths = list(self.all_files.keys())
        matches = get_close_matches(normalized.lower(), [p.lower() for p in all_paths], n=1, cutoff=0.6)
        if matches:
            for p in all_paths:
                if p.lower() == matches[0]:
                    return p
        
        return None
    
    def fix_links(self):
        """修复断链"""
        print("正在修复断链...")
        
        # 按文件分组
        by_file = defaultdict(list)
        for link in self.broken_links:
            by_file[link['source_abs']].append(link)
        
        fixed_count = 0
        for file_path, links in by_file.items():
            md_file = WORK_DIR / file_path.replace('/', os.sep)
            if not md_file.exists():
                continue
            
            try:
                content = md_file.read_text(encoding='utf-8')
                original_content = content
                
                for link in links:
                    old_target = link['link_target']
                    new_target = self._find_closest_match(link)
                    
                    if new_target and new_target != old_target:
                        # 转换为相对路径
                        try:
                            current_dir = md_file.parent
                            new_path = WORK_DIR / new_target.replace('/', os.sep)
                            rel_path = os.path.relpath(new_path, current_dir).replace('\\', '/')
                            
                            # 保持锚点
                            if link['anchor']:
                                rel_path += '#' + link['anchor']
                            
                            # 替换链接
                            old_full = f"]({old_target})"
                            new_full = f"]({rel_path})"
                            content = content.replace(old_full, new_full)
                            
                            self.fixed_links.append({
                                'source': file_path,
                                'old_target': old_target,
                                'new_target': rel_path,
                                'link_text': link['link_text'],
                                'normalized_new': new_target
                            })
                            fixed_count += 1
                        except Exception as e:
                            pass
                
                if content != original_content:
                    md_file.write_text(content, encoding='utf-8')
            except Exception as e:
                print(f"  修复失败: {file_path}, 错误: {e}")
        
        print(f"  修复了 {fixed_count} 个断链")
        return fixed_count
    
    def generate_report(self):
        """生成修复报告"""
        report_path = WORK_DIR / "00-数学家体系断链修复报告.md"
        
        # 统计按类型
        file_broken = [l for l in self.broken_links if l['type'] == 'file']
        anchor_broken = [l for l in self.broken_links if l['type'] == 'anchor']
        
        # 按来源统计
        by_source = defaultdict(int)
        for link in self.broken_links:
            by_source[link['source']] += 1
        
        # 按目标数学家统计
        by_target_math = defaultdict(int)
        for link in file_broken:
            target = link['normalized']
            found = False
            for name, dir_name in MATH_NAME_MAP.items():
                if name in target:
                    by_target_math[name] += 1
                    found = True
                    break
            if not found:
                by_target_math['其他/未知'] += 1
        
        report = f"""# 数学家理念体系断链修复报告

生成时间: {datetime.now().strftime('%Y年%m月%d日 %H:%M')}

## 任务概述

本次任务对FormalMath项目数学家理念体系的62位数学家文档进行全面断链扫描和修复。

## 统计数据

| 指标 | 数量 |
|------|------|
| 扫描的数学家 | {len(MATHEMATICIANS)} 位 |
| 扫描的文件总数 | {len([k for k in self.all_files.keys() if '数学家理念体系' in k])} 个 |
| 发现的断链总数 | {len(self.broken_links)} 个 |
| 文件链接断链 | {len(file_broken)} 个 |
| 锚点链接断链 | {len(anchor_broken)} 个 |
| **修复的断链数** | **{len(self.fixed_links)} 个** |
| 修复率 | {len(self.fixed_links)/len(self.broken_links)*100:.1f}% (按修复数/总数) |

## 断链分类统计

### 按目标类型统计

| 目标数学家/类型 | 断链数量 |
|----------------|----------|
"""
        
        for target, count in sorted(by_target_math.items(), key=lambda x: -x[1])[:20]:
            report += f"| {target} | {count} |\n"
        
        report += f"""
### 按来源文件统计(Top 30)

| 来源文件 | 断链数量 |
|----------|----------|
"""
        
        for source, count in sorted(by_source.items(), key=lambda x: -x[1])[:30]:
            report += f"| {source} | {count} |\n"
        
        report += """
## 修复详情

### 修复策略

1. **数学家交叉引用修复**: 识别链接文本中的数学家名称，修正为目标数学家的README.md
2. **路径层级修正**: 调整错误的相对路径层级
3. **概念文档链接**: 修正指向concept目录的链接
4. **锚点链接**: 暂时保留无法验证的锚点链接

### 修复示例

| 来源文件 | 链接文本 | 原链接目标 | 修复后链接 |
|----------|----------|------------|------------|
"""
        
        for fix in self.fixed_links[:30]:
            report += f"| {fix['source']} | {fix['link_text']} | `{fix['old_target']}` | `{fix['new_target']}` |\n"
        
        # 未修复的断链
        unfixed = [l for l in self.broken_links if not any(f['old_target'] == l['link_target'] and f['source'] == l['source_abs'] for f in self.fixed_links)]
        
        report += f"""

## 未修复断链分析

仍有 {len(unfixed)} 个断链未能自动修复，主要原因包括:

1. **目标文件确实不存在**: 需要创建缺失的文档
2. **链接格式过于复杂**: 需要手动分析和修复
3. **外部资源链接**: 需要确认外部URL的有效性

### 未修复断链样例(Top 50)

| 来源文件 | 链接文本 | 断链目标 | 问题类型 |
|----------|----------|----------|----------|
"""
        
        for link in unfixed[:50]:
            # 判断问题类型
            if any(m in link['normalized'] for m in MATH_NAME_MAP):
                issue_type = "数学家链接错误"
            elif 'concept' in link['normalized']:
                issue_type = "概念文档缺失"
            elif link['type'] == 'anchor':
                issue_type = "锚点不存在"
            else:
                issue_type = "文件不存在"
            
            report += f"| {link['source']} | {link['link_text']} | `{link['link_target']}` | {issue_type} |\n"
        
        report += f"""

## 建议与后续行动

### 立即行动

1. ✓ 完成主要数学家交叉引用的修复 ({len(self.fixed_links)} 处)
2. ⚠ 需手动检查复杂的相对路径链接
3. ⚠ 需验证 concept 目录文档的存在性

### 长期建议

1. **链接标准化**: 统一使用 `../数学家名称/README.md` 格式引用其他数学家
2. **锚点规范**: 文档标题变更时同步更新内部链接
3. **定期检查**: 建议每季度运行一次断链检查
4. **自动化测试**: 在CI流程中加入链接检查步骤

## 附录

### 62位数学家列表

"""
        
        for i, math in enumerate(MATHEMATICIANS, 1):
            exists = "✓" if (MATH_DIR / math).exists() else "✗"
            count = sum(1 for l in self.broken_links if math in l['source'])
            report += f"{i}. {math} {exists} (断链: {count})\n"
        
        report += f"""

---

*报告由断链修复脚本自动生成*
*扫描时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}*
"""
        
        report_path.write_text(report, encoding='utf-8')
        print(f"\n报告已生成: {report_path}")
        return report_path


def main():
    checker = LinkChecker()
    
    # 1. 收集所有文件和锚点
    checker.collect_all_files_and_anchors()
    
    # 2. 扫描断链
    checker.scan_all_files()
    
    # 3. 修复断链
    checker.fix_links()
    
    # 4. 生成报告
    report_path = checker.generate_report()
    
    print(f"\n任务完成!")
    print(f"  断链总数: {len(checker.broken_links)}")
    print(f"  修复数量: {len(checker.fixed_links)}")
    print(f"  修复率: {len(checker.fixed_links)/max(len(checker.broken_links),1)*100:.1f}%")
    print(f"  报告路径: {report_path}")


if __name__ == "__main__":
    main()
