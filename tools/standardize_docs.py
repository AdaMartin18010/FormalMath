#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath文档格式标准化脚本
功能：
1. 统一文档结构（YAML元数据、标题层级、目录）
2. 规范Markdown格式（列表、表格、代码块）
3. 修复常见格式问题
4. 生成标准化报告
"""

import os
import re
import sys
import yaml
import hashlib
from pathlib import Path
from datetime import datetime
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor, as_completed
import multiprocessing

# 配置
DOCS_DIR = Path(r"g:\_src\FormalMath\docs")
REPORT_FILE = Path(r"g:\_src\FormalMath\docs\00-文档格式标准化报告.md")
LOG_FILE = Path(r"g:\_src\FormalMath\tools\standardize_docs.log")

# 格式规则
RULES = {
    # YAML元数据模板
    'yaml_template': """---
msc_primary: "{msc_primary}"
msc_secondary: {msc_secondary}
---

""",
    'default_msc_primary': "00A99",
    'default_msc_secondary': "['00-XX']",
    
    # 章节标题模式
    'chapter_pattern': r'^##\s*第[一二三四五六七八九十]+章',
    'numbered_chapter_pattern': r'^##\s*\d+\.\s*',
    'chinese_number_pattern': r'^##\s*[一二三四五六七八九十]+[、\.\s]',
    
    # 分隔线
    'separator': '\n---\n',
    
    # 文档尾部模板
    'footer_template': """
---

**文档状态**: {status}
**最后更新**: {date}
""",
}

# 统计信息
STATS = {
    'total_files': 0,
    'processed_files': 0,
    'skipped_files': 0,
    'errors': [],
    'changes': defaultdict(int),
    'file_changes': [],
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
    if level == "ERROR":
        print(f"❌ {msg}", file=sys.stderr)
    elif level == "WARNING":
        print(f"⚠️ {msg}")


def has_yaml_header(content):
    """检查是否有YAML元数据头"""
    return content.startswith('---') and '\n---' in content[3:]


def extract_yaml_header(content):
    """提取YAML元数据"""
    if not content.startswith('---'):
        return None, content
    
    end_match = re.search(r'\n---\s*\n', content[3:])
    if not end_match:
        return None, content
    
    yaml_end = 3 + end_match.end()
    yaml_content = content[3:yaml_end-5].strip()
    remaining_content = content[yaml_end:]
    
    try:
        yaml_data = yaml.safe_load(yaml_content) if yaml_content else {}
        return yaml_data, remaining_content
    except yaml.YAMLError:
        return None, content


def add_yaml_header(content, msc_primary=None, msc_secondary=None):
    """添加YAML元数据头"""
    if has_yaml_header(content):
        return content
    
    primary = msc_primary or RULES['default_msc_primary']
    secondary = msc_secondary or RULES['default_msc_secondary']
    
    if isinstance(secondary, list):
        secondary = str(secondary).replace("'", '"')
    
    yaml_header = RULES['yaml_template'].format(
        msc_primary=primary,
        msc_secondary=secondary
    )
    
    return yaml_header + content.lstrip()


def normalize_title(content):
    """规范化标题"""
    changes = []
    
    # 确保一级标题在最前面（YAML之后）
    lines = content.split('\n')
    yaml_end = 0
    if lines and lines[0].strip() == '---':
        for i, line in enumerate(lines[1:], 1):
            if line.strip() == '---':
                yaml_end = i + 1
                break
    
    # 找到第一个非空行
    first_content_idx = yaml_end
    while first_content_idx < len(lines) and not lines[first_content_idx].strip():
        first_content_idx += 1
    
    if first_content_idx >= len(lines):
        return content, changes
    
    # 检查是否有H1标题
    if not lines[first_content_idx].startswith('# '):
        # 尝试找到文档名称作为标题
        # 或者添加默认标题
        pass
    
    return '\n'.join(lines), changes


def normalize_headings(content):
    """规范化章节标题"""
    changes = []
    lines = content.split('\n')
    new_lines = []
    
    for line in lines:
        original = line
        # 将 "## 第一章" 转换为 "## 一、"
        line = re.sub(r'^(##)\s*第([一二三四五六七八九十]+)章\s*[：:]?\s*', r'## \2、', line)
        # 将 "## 1. 标题" 转换为 "## 一、标题" (主章节)
        # 保留 "## 1.1" 格式用于子章节
        if re.match(r'^##\s*\d+\.\s+[^\d]', line):
            num = int(re.match(r'^##\s*(\d+)\.', line).group(1))
            chinese_nums = ['', '一', '二', '三', '四', '五', '六', '七', '八', '九', '十']
            if 1 <= num <= 10:
                line = re.sub(r'^##\s*\d+\.\s*', f'## {chinese_nums[num]}、', line)
        
        if original != line:
            changes.append(f"标题规范化: {original} -> {line}")
        new_lines.append(line)
    
    return '\n'.join(new_lines), changes


def normalize_separators(content):
    """规范化分隔线"""
    changes = []
    # 将 *** 或 ___ 替换为 ---
    content = re.sub(r'\n\*{3,}\s*\n', '\n---\n', content)
    content = re.sub(r'\n_{3,}\s*\n', '\n---\n', content)
    return content, changes


def normalize_code_blocks(content):
    """规范化代码块"""
    changes = []
    # 确保代码块前后有空行
    content = re.sub(r'([^\n])\n```', r'\1\n\n```', content)
    content = re.sub(r'```\n([^\n])', r'```\n\n\1', content)
    return content, changes


def normalize_tables(content):
    """规范化表格"""
    changes = []
    # 确保表格前后有空行
    lines = content.split('\n')
    new_lines = []
    i = 0
    while i < len(lines):
        line = lines[i]
        # 检测表格行
        if '|' in line and i > 0:
            # 检查是否是表格开始
            is_table_start = False
            if not '|' in lines[i-1] and line.strip().startswith('|'):
                is_table_start = True
            if is_table_start and new_lines and new_lines[-1].strip():
                new_lines.append('')
        
        new_lines.append(line)
        
        # 检查表格结束
        if '|' in line and i < len(lines) - 1:
            if not '|' in lines[i+1] and lines[i+1].strip():
                new_lines.append('')
        
        i += 1
    
    return '\n'.join(new_lines), changes


def normalize_lists(content):
    """规范化列表"""
    changes = []
    # 确保列表前后有空行
    lines = content.split('\n')
    new_lines = []
    
    for i, line in enumerate(lines):
        # 无序列表
        if re.match(r'^\s*[-*+]\s', line):
            if i > 0 and lines[i-1].strip() and not lines[i-1].strip().endswith(':'):
                # 检查前一行是否也是列表项
                if not re.match(r'^\s*[-*+]\s', lines[i-1]) and not re.match(r'^\s*\d+\.', lines[i-1]):
                    pass  # new_lines.append('')  # 可能过度添加空行，暂不启用
        new_lines.append(line)
    
    return '\n'.join(new_lines), changes


def add_document_footer(content, status="✅ 完成"):
    """添加文档尾部信息"""
    changes = []
    
    # 检查是否已有文档状态
    if '**文档状态**:' in content or '**文档状态**：' in content:
        return content, changes
    
    date_str = datetime.now().strftime("%Y年%m月%d日")
    footer = RULES['footer_template'].format(status=status, date=date_str)
    
    # 移除末尾的空白行
    content = content.rstrip()
    
    # 检查最后是否有分隔线
    if not content.endswith('---'):
        content += '\n\n---'
    
    content += footer
    changes.append("添加文档尾部信息")
    
    return content, changes


def should_process_file(filepath):
    """判断是否应该处理该文件"""
    # 检查是否在忽略目录中
    for ignore_dir in IGNORE_DIRS:
        if ignore_dir in str(filepath):
            return False
    
    # 只处理 .md 文件
    if not filepath.endswith('.md'):
        return False
    
    return True


def process_file(filepath):
    """处理单个文件"""
    changes = []
    
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        original_content = content
        
        # 1. 添加YAML元数据（如果没有）
        if not has_yaml_header(content):
            content = add_yaml_header(content)
            changes.append("添加YAML元数据")
        
        # 2. 规范化标题
        content, title_changes = normalize_title(content)
        changes.extend(title_changes)
        
        # 3. 规范化章节标题
        content, heading_changes = normalize_headings(content)
        changes.extend(heading_changes)
        
        # 4. 规范化分隔线
        content, sep_changes = normalize_separators(content)
        changes.extend(sep_changes)
        
        # 5. 规范化代码块
        content, code_changes = normalize_code_blocks(content)
        changes.extend(code_changes)
        
        # 6. 规范化表格
        content, table_changes = normalize_tables(content)
        changes.extend(table_changes)
        
        # 7. 规范化列表
        content, list_changes = normalize_lists(content)
        changes.extend(list_changes)
        
        # 8. 添加文档尾部（可选，可能影响太大）
        # content, footer_changes = add_document_footer(content)
        # changes.extend(footer_changes)
        
        # 只有在有变化时才写入
        if content != original_content:
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(content)
            return {'file': filepath, 'changes': changes, 'success': True}
        else:
            return {'file': filepath, 'changes': [], 'success': True, 'skipped': True}
        
    except Exception as e:
        return {'file': filepath, 'changes': [], 'success': False, 'error': str(e)}


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
    """生成标准化报告"""
    report = f"""---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# FormalMath文档格式标准化报告

**生成时间**: {datetime.now().strftime("%Y年%m月%d日 %H:%M:%S")}

---

## 一、处理概况

| 指标 | 数值 |
|------|------|
| 总文件数 | {STATS['total_files']} |
| 处理文件数 | {STATS['processed_files']} |
| 跳过文件数 | {STATS['skipped_files']} |
| 错误数 | {len(STATS['errors'])} |

---

## 二、修改统计

| 修改类型 | 次数 |
|----------|------|
"""
    
    for change_type, count in sorted(STATS['changes'].items(), key=lambda x: -x[1]):
        report += f"| {change_type} | {count} |\n"
    
    report += """
---

## 三、文件变更详情

"""
    
    for file_change in STATS['file_changes'][:100]:  # 只显示前100个
        report += f"### {file_change['file']}\n\n"
        for change in file_change['changes'][:10]:  # 每文件最多10条
            report += f"- {change}\n"
        report += "\n"
    
    if len(STATS['file_changes']) > 100:
        report += f"\n... 还有 {len(STATS['file_changes']) - 100} 个文件变更未显示\n"
    
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
    
    log_message(f"报告已生成: {REPORT_FILE}")


def main():
    """主函数"""
    print("=" * 60)
    print("FormalMath文档格式标准化工具")
    print("=" * 60)
    
    # 清空日志文件
    with open(LOG_FILE, 'w', encoding='utf-8') as f:
        f.write(f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] 开始处理\n")
    
    # 获取所有文件
    print("\n📁 扫描文档目录...")
    md_files = get_all_md_files()
    STATS['total_files'] = len(md_files)
    print(f"   找到 {len(md_files)} 个Markdown文件")
    
    # 处理文件
    print("\n🔧 开始处理文档...")
    processed = 0
    skipped = 0
    errors = 0
    
    # 使用单线程处理以避免文件锁定问题
    for i, filepath in enumerate(md_files, 1):
        if i % 100 == 0:
            print(f"   已处理 {i}/{len(md_files)} 个文件...")
        
        result = process_file(filepath)
        
        if result['success']:
            if result.get('skipped'):
                skipped += 1
            else:
                processed += 1
                STATS['file_changes'].append({
                    'file': filepath,
                    'changes': result['changes']
                })
                for change in result['changes']:
                    STATS['changes'][change] += 1
        else:
            errors += 1
            STATS['errors'].append(f"{filepath}: {result.get('error', 'Unknown error')}")
    
    STATS['processed_files'] = processed
    STATS['skipped_files'] = skipped
    
    print(f"\n✅ 处理完成:")
    print(f"   - 已修改: {processed} 个文件")
    print(f"   - 已跳过: {skipped} 个文件")
    print(f"   - 错误: {errors} 个")
    
    # 生成报告
    print("\n📝 生成报告...")
    generate_report()
    
    print(f"\n📄 报告位置: {REPORT_FILE}")
    print(f"📝 日志位置: {LOG_FILE}")
    print("\n" + "=" * 60)


if __name__ == '__main__':
    main()
