#!/usr/bin/env python3
"""
扫描FormalMath项目中的所有Markdown文件，识别纯占位符内容
"""
import os
import re
from datetime import datetime
from pathlib import Path

# 定义纯占位符模式
PLACEHOLDER_PATTERNS = [
    r'^\s*待补充\s*$',
    r'^\s*TODO\s*$',
    r'^\s* todo\s*$',
    r'^\s*Todo\s*$',
    r'^\s*建设中\s*$',
    r'^\s*WIP\s*$',
    r'^\s*wip\s*$',
    r'^\s*Work in Progress\s*$',
    r'^\s*Coming Soon\s*$',
    r'^\s*coming soon\s*$',
    r'^\s*即将上线\s*$',
    r'^\s*敬请期待\s*$',
    r'^\s*TBD\s*$',
    r'^\s*tbd\s*$',
]

# Frontmatter 正则
FRONTMATTER_PATTERN = re.compile(r'^---\s*\n(.*?)\n---\s*\n', re.DOTALL)

def has_only_frontmatter(content):
    """检查是否只有Frontmatter，没有正文"""
    match = FRONTMATTER_PATTERN.match(content)
    if not match:
        return False
    # 获取Frontmatter后的内容
    remaining = content[match.end():]
    # 去除空白后检查是否为空
    remaining = remaining.strip()
    return len(remaining) == 0 or remaining in ['', '\n', '\r\n']

def has_only_title(content):
    """检查是否只有标题，没有实质内容"""
    lines = content.strip().split('\n')
    # 过滤空行
    lines = [l.strip() for l in lines if l.strip()]
    
    if not lines:
        return False
    
    # 检查是否只有标题行（以#开头）
    title_count = 0
    content_count = 0
    for line in lines:
        if line.startswith('#'):
            title_count += 1
        else:
            # 非标题行，检查是否有实质内容
            if len(line) > 3 and not line.startswith('-') and not line.startswith('*'):
                content_count += 1
    
    # 如果只有标题，没有实质内容
    return title_count > 0 and content_count == 0

def is_pure_placeholder(filepath):
    """检查文件是否为纯占位符"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        print(f"Error reading {filepath}: {e}")
        return False, "read_error", str(e)
    
    content_stripped = content.strip()
    
    # 空文件
    if not content_stripped:
        return True, "empty", "文件为空"
    
    # 检查纯占位符文本
    for pattern in PLACEHOLDER_PATTERNS:
        if re.match(pattern, content_stripped, re.IGNORECASE):
            return True, "placeholder_text", f"匹配模式: {pattern}"
    
    # 只有Frontmatter
    if has_only_frontmatter(content):
        return True, "only_frontmatter", "只有Frontmatter，没有正文"
    
    # 只有标题
    if has_only_title(content):
        return True, "only_titles", "只有标题，没有实质内容"
    
    return False, "has_content", "包含实质内容"

def get_file_age_days(filepath):
    """获取文件的最后修改时间（天数）"""
    try:
        stat = os.stat(filepath)
        mtime = datetime.fromtimestamp(stat.st_mtime)
        age = (datetime.now() - mtime).days
        return age
    except Exception as e:
        return -1

def main():
    root_dir = Path('.')
    md_files = list(root_dir.rglob('*.md'))
    
    print(f"找到 {len(md_files)} 个Markdown文件")
    
    placeholder_files = []
    
    for md_file in md_files:
        filepath = str(md_file)
        is_placeholder, placeholder_type, reason = is_pure_placeholder(filepath)
        
        if is_placeholder:
            age_days = get_file_age_days(filepath)
            placeholder_files.append({
                'filepath': filepath,
                'type': placeholder_type,
                'reason': reason,
                'age_days': age_days
            })
    
    # 分类统计
    to_delete = []
    to_replace = []
    
    for pf in placeholder_files:
        if pf['age_days'] > 30:
            to_delete.append(pf)
        else:
            to_replace.append(pf)
    
    # 输出报告
    print("\n" + "="*80)
    print("纯占位符文件扫描报告")
    print("="*80)
    
    print(f"\n总计扫描: {len(md_files)} 个Markdown文件")
    print(f"发现纯占位符: {len(placeholder_files)} 个")
    
    print(f"\n【应删除】（超过30天）: {len(to_delete)} 个")
    for pf in to_delete:
        print(f"  - {pf['filepath']}")
        print(f"    类型: {pf['type']}, 理由: {pf['reason']}, 年龄: {pf['age_days']}天")
    
    print(f"\n【需替换为说明文档】: {len(to_replace)} 个")
    for pf in to_replace:
        print(f"  - {pf['filepath']}")
        print(f"    类型: {pf['type']}, 理由: {pf['reason']}, 年龄: {pf['age_days']}天")
    
    # 生成Markdown报告
    report_content = generate_report(md_files, placeholder_files, to_delete, to_replace)
    
    with open('00-占位符清理报告.md', 'w', encoding='utf-8') as f:
        f.write(report_content)
    
    print("\n" + "="*80)
    print("报告已保存到: 00-占位符清理报告.md")

def generate_report(all_files, placeholder_files, to_delete, to_replace):
    """生成Markdown格式的报告"""
    now = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    
    report = f"""# FormalMath项目纯占位符清理报告

**生成时间**: {now}

## 执行摘要

| 指标 | 数量 |
|------|------|
| 扫描文件总数 | {len(all_files)} |
| 纯占位符文件 | {len(placeholder_files)} |
| 建议删除（>30天） | {len(to_delete)} |
| 建议替换为说明 | {len(to_replace)} |

## 详细清单

### 一、建议删除的纯占位符文件（超过30天）

共 **{len(to_delete)}** 个文件：

"""
    
    if to_delete:
        for pf in to_delete:
            report += f"""#### {pf['filepath']}

- **文件路径**: `{pf['filepath']}`
- **占位符类型**: {pf['type']}
- **具体原因**: {pf['reason']}
- **文件年龄**: {pf['age_days']}天

"""
    else:
        report += "无\n\n"
    
    report += f"""### 二、建议替换为说明文档的文件

共 **{len(to_replace)}** 个文件：

"""
    
    if to_replace:
        for pf in to_replace:
            report += f"""#### {pf['filepath']}

- **文件路径**: `{pf['filepath']}`
- **占位符类型**: {pf['type']}
- **具体原因**: {pf['reason']}
- **文件年龄**: {pf['age_days']}天

"""
    else:
        report += "无\n\n"
    
    report += """## 占位符类型说明

| 类型 | 说明 |
|------|------|
| empty | 完全空文件 |
| placeholder_text | 只有占位符文本（如"待补充"、"TODO"等） |
| only_frontmatter | 只有Frontmatter元数据，没有正文内容 |
| only_titles | 只有标题行，没有实质内容段落 |

## 处理建议

### 删除确认

以下文件建议**直接删除**：
- 纯占位符内容
- 创建超过30天
- 无历史价值

### 替换为说明文档

以下文件建议**保留并替换为说明文档**：
- 位于重要目录结构中的占位符
- 需要保留文件位置作为占位
- 应替换为说明该位置用途的文档

## 执行命令参考

```bash
# 删除确认后的文件
"""
    
    for pf in to_delete:
        report += f"""rm \"{pf['filepath']}\""" + "\n"
    
    report += """```

---
*报告由占位符扫描脚本自动生成*
"""
    
    return report

if __name__ == '__main__':
    main()
