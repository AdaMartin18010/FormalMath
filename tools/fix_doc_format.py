#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath文档格式修复脚本
功能：
1. 修复标题层级跳跃问题
2. 修复缺少YAML元数据的问题
3. 修复缺少H1标题的问题
4. 修复代码块未闭合问题
"""

import os
import re
import sys
import yaml
from pathlib import Path
from datetime import datetime
from collections import defaultdict

# 配置
DOCS_DIR = Path(r"g:\_src\FormalMath\docs")
REPORT_FILE = Path(r"g:\_src\FormalMath\docs\00-文档格式修复报告.md")
LOG_FILE = Path(r"g:\_src\FormalMath\tools\fix_doc_format.log")

# 统计信息
STATS = {
    'total_files': 0,
    'fixed_files': 0,
    'skipped_files': 0,
    'errors': [],
    'fixes': defaultdict(int),
    'file_fixes': [],
}

# 忽略的目录
IGNORE_DIRS = {
    '.git', '__pycache__', 'node_modules', 'venv', '.venv',
    '00-归档', '99-归档文档', '归档'
}


def log_message(msg, level="INFO"):
    """记录日志"""
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    log_line = f"[{timestamp}] [{level}] {msg}\n"
    with open(LOG_FILE, 'a', encoding='utf-8') as f:
        f.write(log_line)


def has_yaml_header(content):
    """检查是否有YAML元数据头"""
    return content.startswith('---') and '\n---' in content[3:]


def add_yaml_header(content):
    """添加YAML元数据头"""
    yaml_header = """---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

"""
    return yaml_header + content


def fix_heading_levels(content):
    """修复标题层级跳跃问题"""
    fixes = []
    lines = content.split('\n')
    new_lines = []
    
    prev_level = 0
    for i, line in enumerate(lines):
        # 跳过YAML头
        if i == 0 and line.strip() == '---':
            # 找到YAML结束
            new_lines.append(line)
            for j in range(i + 1, len(lines)):
                new_lines.append(lines[j])
                if lines[j].strip() == '---':
                    i = j + 1
                    break
            continue
        
        heading_match = re.match(r'^(#{1,6})\s+(.+)$', line)
        if heading_match:
            level = len(heading_match.group(1))
            text = heading_match.group(2)
            
            # 检查层级跳跃
            if prev_level > 0 and level > prev_level + 1:
                # 修复：将跳跃的标题降低一级
                new_level = prev_level + 1
                new_heading = '#' * new_level + ' ' + text
                fixes.append(f"修复标题层级: H{level} -> H{new_level}: {text[:50]}")
                new_lines.append(new_heading)
                prev_level = new_level
                continue
            
            prev_level = level
        
        new_lines.append(line)
    
    return '\n'.join(new_lines), fixes


def fix_missing_h1(content, filepath):
    """修复缺少H1标题的问题"""
    fixes = []
    
    # 移除YAML头后的内容
    content_without_yaml = content
    if content.startswith('---'):
        end_match = re.search(r'\n---\s*\n', content[3:])
        if end_match:
            yaml_end = 3 + end_match.end()
            content_without_yaml = content[yaml_end:]
    
    # 检查是否有H1标题
    if not re.search(r'^# [^#]', content_without_yaml, re.MULTILINE):
        # 从文件名生成标题
        filename = Path(filepath).stem
        # 移除常见的后缀
        title = filename.replace('-', ' ').replace('_', ' ')
        
        # 在YAML头后添加H1标题
        if content.startswith('---'):
            end_match = re.search(r'\n---\s*\n', content[3:])
            if end_match:
                yaml_end = 3 + end_match.end()
                content = content[:yaml_end] + f"# {title}\n\n" + content[yaml_end:]
        else:
            content = f"# {title}\n\n" + content
        
        fixes.append(f"添加H1标题: {title}")
    
    return content, fixes


def fix_code_blocks(content):
    """修复未闭合的代码块"""
    fixes = []
    
    # 计算代码块标记数量
    code_block_count = content.count('```')
    
    if code_block_count % 2 != 0:
        # 添加闭合标记
        content = content.rstrip() + '\n```\n'
        fixes.append("添加代码块闭合标记")
    
    return content, fixes


def fix_yaml_header(content):
    """修复YAML元数据头"""
    fixes = []
    
    if not has_yaml_header(content):
        content = add_yaml_header(content)
        fixes.append("添加YAML元数据头")
    
    return content, fixes


def should_process_file(filepath):
    """判断是否应该处理该文件"""
    for ignore_dir in IGNORE_DIRS:
        if ignore_dir in str(filepath):
            return False
    
    if not filepath.endswith('.md'):
        return False
    
    return True


def process_file(filepath):
    """处理单个文件"""
    fixes = []
    
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        original_content = content
        
        # 1. 修复YAML元数据头
        content, yaml_fixes = fix_yaml_header(content)
        fixes.extend(yaml_fixes)
        
        # 2. 修复缺少H1标题
        content, h1_fixes = fix_missing_h1(content, filepath)
        fixes.extend(h1_fixes)
        
        # 3. 修复标题层级跳跃
        content, heading_fixes = fix_heading_levels(content)
        fixes.extend(heading_fixes)
        
        # 4. 修复代码块
        content, code_fixes = fix_code_blocks(content)
        fixes.extend(code_fixes)
        
        # 只有在有变化时才写入
        if content != original_content:
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(content)
            return {'file': filepath, 'fixes': fixes, 'success': True}
        else:
            return {'file': filepath, 'fixes': [], 'success': True, 'skipped': True}
        
    except Exception as e:
        return {'file': filepath, 'fixes': [], 'success': False, 'error': str(e)}


def get_all_md_files():
    """获取所有需要处理的Markdown文件"""
    md_files = []
    for root, dirs, files in os.walk(DOCS_DIR):
        # 过滤忽略的目录
        dirs[:] = [d for d in dirs if d not in IGNORE_DIRS]
        
        for file in files:
            if file.endswith('.md'):
                filepath = os.path.join(root, file)
                md_files.append(filepath)
    
    return md_files


def generate_report():
    """生成修复报告"""
    report = f"""---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# FormalMath文档格式修复报告

**生成时间**: {datetime.now().strftime("%Y年%m月%d日 %H:%M:%S")}

---

## 一、修复概况

| 指标 | 数值 |
|------|------|
| 总文件数 | {STATS['total_files']} |
| 修复文件数 | {STATS['fixed_files']} |
| 跳过文件数 | {STATS['skipped_files']} |
| 错误数 | {len(STATS['errors'])} |

---

## 二、修复统计

| 修复类型 | 次数 |
|----------|------|
"""
    
    for fix_type, count in sorted(STATS['fixes'].items(), key=lambda x: -x[1]):
        report += f"| {fix_type} | {count} |\n"
    
    report += """
---

## 三、文件修复详情

"""
    
    for file_fix in STATS['file_fixes'][:100]:
        report += f"### {file_fix['file']}\n\n"
        for fix in file_fix['fixes'][:10]:
            report += f"- {fix}\n"
        report += "\n"
    
    if len(STATS['file_fixes']) > 100:
        report += f"\n... 还有 {len(STATS['file_fixes']) - 100} 个文件修复未显示\n"
    
    report += """
---

## 四、错误记录

"""
    
    if STATS['errors']:
        for error in STATS['errors'][:50]:
            report += f"- {error}\n"
    else:
        report += "无错误记录\n"
    
    report += f"""

---

**报告生成**: ✅ 完成
**最后更新**: {datetime.now().strftime("%Y年%m月%d日")}
"""
    
    with open(REPORT_FILE, 'w', encoding='utf-8') as f:
        f.write(report)
    
    log_message(f"修复报告已生成: {REPORT_FILE}")


def main():
    """主函数"""
    print("=" * 60)
    print("FormalMath文档格式修复工具")
    print("=" * 60)
    
    # 清空日志文件
    with open(LOG_FILE, 'w', encoding='utf-8') as f:
        f.write(f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] 开始修复\n")
    
    # 获取所有文件
    print("\n📁 扫描文档目录...")
    md_files = get_all_md_files()
    STATS['total_files'] = len(md_files)
    print(f"   找到 {len(md_files)} 个Markdown文件")
    
    # 处理文件
    print("\n🔧 开始修复文档...")
    fixed = 0
    skipped = 0
    errors = 0
    
    for i, filepath in enumerate(md_files, 1):
        if i % 100 == 0:
            print(f"   已处理 {i}/{len(md_files)} 个文件...")
        
        result = process_file(filepath)
        
        if result['success']:
            if result.get('skipped'):
                skipped += 1
            else:
                fixed += 1
                STATS['file_fixes'].append({
                    'file': filepath,
                    'fixes': result['fixes']
                })
                for fix in result['fixes']:
                    STATS['fixes'][fix] += 1
        else:
            errors += 1
            STATS['errors'].append(f"{filepath}: {result.get('error', 'Unknown error')}")
    
    STATS['fixed_files'] = fixed
    STATS['skipped_files'] = skipped
    
    print(f"\n✅ 修复完成:")
    print(f"   - 已修复: {fixed} 个文件")
    print(f"   - 已跳过: {skipped} 个文件")
    print(f"   - 错误: {errors} 个")
    
    # 生成报告
    print("\n📝 生成修复报告...")
    generate_report()
    
    print(f"\n📄 报告位置: {REPORT_FILE}")
    print(f"📝 日志位置: {LOG_FILE}")
    print("\n" + "=" * 60)


if __name__ == '__main__':
    main()
