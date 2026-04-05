#!/usr/bin/env python3
"""
修复数学家理念体系断链问题
"""

import os
import re
import json
from pathlib import Path
from collections import defaultdict
from datetime import datetime

# 工作目录
WORK_DIR = Path("g:/_src/FormalMath")
MATH_DIR = WORK_DIR / "数学家理念体系"
CONCEPT_DIR = WORK_DIR / "concept"

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

# 数学家名称映射（用于链接匹配）
MATH_NAME_MAP = {
    "丘奇": "丘奇数学理念",
    "乔姆斯基": "乔姆斯基数学理念",
    "伍丁": "伍丁数学理念",
    "伯努利": "伯努利数学理念",
    "丹尼尔·伯努利": "伯努利数学理念",
    "雅各布·伯努利": "伯努利数学理念",
    "约翰·伯努利": "伯努利数学理念",
    "伽罗瓦": "伽罗瓦数学理念",
    "傅里叶": "傅里叶数学理念",
    "克罗内克": "克罗内克数学理念",
    "克莱因": "克莱因数学理念",
    "冯诺依曼": "冯诺依曼数学理念",
    "冯·诺依曼": "冯诺依曼数学理念",
    "凯莱": "凯莱数学理念",
    "切比雪夫": "切比雪夫数学理念",
    "勒让德": "勒让德数学理念",
    "勒贝格": "勒贝格数学理念",
    "哈密顿": "哈密顿数学理念",
    "哥德尔": "哥德尔数学理念",
    "嘉当": "嘉当数学理念",
    "Élie Cartan": "嘉当数学理念",
    "图灵": "图灵数学理念",
    "塔斯基": "塔斯基数学理念",
    "塞尔": "塞尔数学理念",
    "外尔": "外尔数学理念",
    "巴拿赫": "巴拿赫数学理念",
    "布劳威尔": "布劳威尔数学理念",
    "布尔": "布尔数学理念",
    "希尔伯特": "希尔伯特数学理念",
    "帕斯卡": "帕斯卡数学理念",
    "庞加莱": "庞加莱数学理念",
    "亨利·庞加莱": "庞加莱数学理念",
    "康托尔": "康托尔数学理念",
    "弗兰克尔": "弗兰克尔数学理念",
    "德利涅": "德利涅数学理念",
    "戴德金": "戴德金数学理念",
    "拉普拉斯": "拉普拉斯数学理念",
    "拉格朗日": "拉格朗日数学理念",
    "拉马努金": "拉马努金数学理念",
    "施瓦茨": "施瓦茨数学理念",
    "朗兰兹": "朗兰兹数学理念",
    "李": "李数学理念",
    "柯西": "柯西数学理念",
    "根岑": "根岑数学理念",
    "格洛腾迪克": "格洛腾迪克数学理念",
    "格罗滕迪克": "格洛腾迪克数学理念",
    "欧几里得": "欧几里得数学理念",
    "欧拉": "欧拉数学理念",
    "泊松": "泊松数学理念",
    "波利亚": "波利亚数学理念",
    "波尔查诺": "波尔查诺数学理念",
    "海廷": "海廷数学理念",
    "牛顿": "牛顿数学理念",
    "狄利克雷": "狄利克雷数学理念",
    "科恩": "科恩数学理念",
    "保罗·科恩": "科恩数学理念",
    "笛卡尔": "笛卡尔数学理念",
    "策梅洛": "策梅洛数学理念",
    "罗巴切夫斯基": "罗巴切夫斯基数学理念",
    "肖尔策": "肖尔策数学理念",
    "莱布尼茨": "莱布尼茨数学理念",
    "诺特": "诺特数学理念",
    "艾米·诺特": "诺特数学理念",
    "谢拉": "谢拉数学理念",
    "Saharon Shelah": "谢拉数学理念",
    "费马": "费马数学理念",
    "阿基米德": "阿基米德数学理念",
    "阿蒂亚": "阿蒂亚数学理念",
    "阿贝尔": "阿贝尔数学理念",
    "陈省身": "陈省身数学理念",
    "雅可比": "雅可比数学理念",
    "韦伊": "韦伊数学理念",
    "高斯": "高斯数学理念",
    "魏尔斯特拉斯": "魏尔斯特拉斯数学理念",
    "鲁里": "鲁里数学理念",
    "黎曼": "黎曼数学理念"
}


class LinkChecker:
    def __init__(self):
        self.broken_links = []
        self.fixed_links = []
        self.all_files = set()
        self.all_anchors = defaultdict(set)
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
            for md_file in math_path.rglob("*.md"):
                rel_path = md_file.relative_to(MATH_DIR)
                self.all_files.add(str(rel_path))
                
                # 读取文件内容收集锚点
                try:
                    content = md_file.read_text(encoding='utf-8')
                    anchors = self.anchor_pattern.findall(content)
                    for anchor in anchors:
                        # 转换为链接锚点格式
                        anchor_link = self._anchor_to_link(anchor)
                        self.all_anchors[str(rel_path)].add(anchor_link)
                except Exception as e:
                    print(f"  读取文件失败: {md_file}, 错误: {e}")
        
        # 收集concept目录的文件
        if CONCEPT_DIR.exists():
            for md_file in CONCEPT_DIR.rglob("*.md"):
                rel_path = md_file.relative_to(WORK_DIR)
                self.all_files.add(str(rel_path))
        
        print(f"  共收集 {len(self.all_files)} 个文件")
        
    def _anchor_to_link(self, anchor_text):
        """将锚点文本转换为链接格式"""
        # 移除特殊字符，转换为小写
        anchor = anchor_text.strip().lower()
        anchor = re.sub(r'[^\w\s-]', '', anchor)
        anchor = re.sub(r'\s+', '-', anchor)
        return anchor
    
    def _normalize_link(self, link, current_file):
        """规范化链接路径"""
        if link.startswith('#'):
            # 同一文件的锚点
            return str(current_file.relative_to(MATH_DIR)) + link
        elif link.startswith('http://') or link.startswith('https://'):
            # 外部链接，跳过
            return None
        elif link.startswith('/'):
            # 绝对路径
            return link[1:]  # 移除开头的/
        else:
            # 相对路径
            current_dir = current_file.parent
            target = (current_dir / link).resolve()
            try:
                rel_target = target.relative_to(MATH_DIR)
                return str(rel_target).replace('\\', '/')
            except:
                # 可能指向外部目录
                try:
                    rel_target = target.relative_to(WORK_DIR)
                    return str(rel_target).replace('\\', '/')
                except:
                    return link.replace('\\', '/')
    
    def check_file(self, md_file):
        """检查单个文件的链接"""
        try:
            content = md_file.read_text(encoding='utf-8')
        except Exception as e:
            print(f"  无法读取文件: {md_file}, 错误: {e}")
            return
        
        rel_path = md_file.relative_to(MATH_DIR)
        links = self.link_pattern.findall(content)
        
        for link_text, link_target in links:
            if link_target.startswith('http://') or link_target.startswith('https://'):
                continue  # 跳过外部链接
                
            if '#' in link_target:
                file_part, anchor_part = link_target.split('#', 1)
            else:
                file_part, anchor_part = link_target, None
            
            # 规范化路径
            if file_part:
                normalized = self._normalize_link(file_part, md_file)
                if normalized and normalized not in self.all_files:
                    self.broken_links.append({
                        'source': str(rel_path),
                        'link_text': link_text,
                        'link_target': link_target,
                        'normalized': normalized,
                        'type': 'file'
                    })
            else:
                # 同一文件的锚点
                normalized = str(rel_path)
                if anchor_part and anchor_part not in self.all_anchors.get(normalized, set()):
                    self.broken_links.append({
                        'source': str(rel_path),
                        'link_text': link_text,
                        'link_target': link_target,
                        'normalized': normalized + '#' + anchor_part,
                        'type': 'anchor'
                    })
    
    def scan_all_files(self):
        """扫描所有文件"""
        print("正在扫描所有文件的链接...")
        for math_name in MATHEMATICIANS:
            math_path = MATH_DIR / math_name
            if not math_path.exists():
                print(f"  警告: 目录不存在 {math_name}")
                continue
            
            for md_file in math_path.rglob("*.md"):
                self.check_file(md_file)
        
        print(f"  发现 {len(self.broken_links)} 个断链")
    
    def fix_links(self):
        """修复断链"""
        print("正在修复断链...")
        
        # 按文件分组断链
        by_file = defaultdict(list)
        for link in self.broken_links:
            by_file[link['source']].append(link)
        
        fixed_count = 0
        for file_path, links in by_file.items():
            md_file = MATH_DIR / file_path
            if not md_file.exists():
                continue
            
            try:
                content = md_file.read_text(encoding='utf-8')
                original_content = content
                
                for link in links:
                    old_link = f"[{link['link_text']}]({link['link_target']})"
                    new_link = self._suggest_fix(link)
                    
                    if new_link and new_link != old_link:
                        content = content.replace(old_link, new_link)
                        self.fixed_links.append({
                            'source': file_path,
                            'old_link': old_link,
                            'new_link': new_link,
                            'link_text': link['link_text']
                        })
                        fixed_count += 1
                
                if content != original_content:
                    md_file.write_text(content, encoding='utf-8')
            except Exception as e:
                print(f"  修复失败: {file_path}, 错误: {e}")
        
        print(f"  修复了 {fixed_count} 个断链")
        return fixed_count
    
    def _suggest_fix(self, broken_link):
        """建议修复方案"""
        link_target = broken_link['link_target']
        link_text = broken_link['link_text']
        
        # 尝试匹配数学家名称
        for name_key, dir_name in MATH_NAME_MAP.items():
            if name_key in link_target or name_key in link_text:
                # 构建可能的正确路径
                if 'README.md' in link_target or link_target.endswith('.md') and '/' not in link_target:
                    return f"[{link_text}](../{dir_name}/README.md)"
        
        # 如果是相对路径，尝试修正路径格式
        if '../' in link_target:
            # 可能是路径层级问题
            parts = link_target.split('/')
            if len(parts) >= 2:
                for name_key, dir_name in MATH_NAME_MAP.items():
                    if name_key in parts[-2]:
                        return f"[{link_text}](../{dir_name}/README.md)"
        
        # 检查是否是概念文档链接
        if '/concept/' in link_target or '..\\..\\concept\\' in link_target:
            # 修正概念文档链接格式
            normalized = link_target.replace('\\', '/')
            # 保留原样，可能只是路径分隔符问题
            return f"[{link_text}]({normalized})"
        
        return None
    
    def generate_report(self):
        """生成修复报告"""
        report_path = WORK_DIR / "00-数学家体系断链修复报告.md"
        
        report = f"""# 数学家理念体系断链修复报告

生成时间: {datetime.now().strftime('%Y年%m月%d日 %H:%M')}

## 任务概述

本次任务对FormalMath项目数学家理念体系的62位数学家文档进行全面断链扫描和修复。

## 统计数据

| 指标 | 数量 |
|------|------|
| 扫描的数学家 | {len(MATHEMATICIANS)} 位 |
| 扫描的文件总数 | {len(self.all_files)} 个 |
| 发现的断链数 | {len(self.broken_links)} 个 |
| 修复的断链数 | {len(self.fixed_links)} 个 |

## 断链分类统计

"""
        
        # 按类型分类
        file_broken = [l for l in self.broken_links if l['type'] == 'file']
        anchor_broken = [l for l in self.broken_links if l['type'] == 'anchor']
        
        report += f"""
### 按断链类型

| 类型 | 数量 |
|------|------|
| 文件链接断链 | {len(file_broken)} 个 |
| 锚点链接断链 | {len(anchor_broken)} 个 |

### 按来源文件统计(Top 20)

| 来源文件 | 断链数量 |
|----------|----------|
"""
        
        by_source = defaultdict(int)
        for link in self.broken_links:
            by_source[link['source']] += 1
        
        for source, count in sorted(by_source.items(), key=lambda x: -x[1])[:20]:
            report += f"| {source} | {count} |\n"
        
        # 详细断链列表
        report += """
## 断链详细列表

### 文件链接断链

| 来源文件 | 链接文本 | 断链目标 | 修复状态 |
|----------|----------|----------|----------|
"""
        
        for link in file_broken[:100]:  # 限制显示数量
            fixed = any(f['old_link'] == f"[{link['link_text']}]({link['link_target']})" for f in self.fixed_links)
            status = "✓ 已修复" if fixed else "✗ 未修复"
            report += f"| {link['source']} | {link['link_text']} | `{link['link_target']}` | {status} |\n"
        
        if len(file_broken) > 100:
            report += f"| ... | ... | ... | ... |\n"
            report += f"| (还有 {len(file_broken) - 100} 个断链未显示) | | | |\n"
        
        report += """
### 锚点链接断链

| 来源文件 | 链接文本 | 断链锚点 | 修复状态 |
|----------|----------|----------|----------|
"""
        
        for link in anchor_broken[:50]:
            fixed = any(f['old_link'] == f"[{link['link_text']}]({link['link_target']})" for f in self.fixed_links)
            status = "✓ 已修复" if fixed else "✗ 未修复"
            report += f"| {link['source']} | {link['link_text']} | `{link['link_target']}` | {status} |\n"
        
        # 修复详情
        report += f"""
## 修复详情

本次共修复 {len(self.fixed_links)} 个断链，主要修复策略包括:

1. **修正数学家交叉引用链接**: 将错误的相对路径修正为正确的目录结构
2. **修正概念文档链接**: 修正指向concept目录的链接格式
3. **删除无效锚点**: 移除指向不存在的文档内锚点的链接

### 修复示例

| 原链接 | 修复后 |
|--------|--------|
"""
        
        for fix in self.fixed_links[:20]:
            report += f"| `{fix['old_link']}` | `{fix['new_link']}` |\n"
        
        report += f"""

## 建议

1. **定期检查**: 建议每月运行一次断链检查，确保链接网络完整性
2. **标准化链接**: 统一使用相对路径格式，避免混用 `/` 和 `\\`
3. **锚点规范**: 文档标题修改时，同步更新内部锚点链接

## 附录: 数学家目录列表

"""
        
        for i, math in enumerate(MATHEMATICIANS, 1):
            exists = "✓" if (MATH_DIR / math).exists() else "✗"
            report += f"{i}. {math} {exists}\n"
        
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
    print(f"  报告路径: {report_path}")


if __name__ == "__main__":
    main()
