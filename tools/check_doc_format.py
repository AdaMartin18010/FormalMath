#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath文档格式检查脚本
功能：
1. 检查YAML元数据完整性
2. 检查标题层级规范性
3. 检查目录完整性
4. 检查链接有效性
5. 生成检查报告
"""

import os
import re
import sys
import yaml
from pathlib import Path
from datetime import datetime
from collections import defaultdict
from urllib.parse import urlparse

# 配置
DOCS_DIR = Path(r"g:\_src\FormalMath\docs")
REPORT_FILE = Path(r"g:\_src\FormalMath\docs\00-文档格式检查报告.md")
LOG_FILE = Path(r"g:\_src\FormalMath\tools\check_doc_format.log")

# 检查规则
CHECK_RULES = {
    'require_yaml': True,
    'require_title': True,
    'require_toc': False,  # 可选，不强制
    'max_heading_level': 5,
    'require_footer': False,  # 可选，不强制
}

# 统计信息
STATS = {
    'total_files': 0,
    'passed_files': 0,
    'warning_files': 0,
    'error_files': 0,
    'checks': {
        'yaml_valid': 0,
        'yaml_invalid': 0,
        'yaml_missing': 0,
        'title_valid': 0,
        'title_missing': 0,
        'heading_valid': 0,
        'heading_invalid': 0,
        'separator_valid': 0,
        'separator_invalid': 0,
    },
    'errors': [],
    'warnings': [],
    'file_results': [],
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


def check_yaml_header(content, filepath):
    """检查YAML元数据头"""
    errors = []
    warnings = []
    
    if not content.startswith('---'):
        errors.append("缺少YAML元数据头")
        STATS['checks']['yaml_missing'] += 1
        return {'valid': False, 'errors': errors, 'warnings': warnings, 'data': None}
    
    # 找到YAML结束标记
    end_match = re.search(r'\n---\s*\n', content[3:])
    if not end_match:
        errors.append("YAML元数据格式错误：缺少结束标记")
        STATS['checks']['yaml_invalid'] += 1
        return {'valid': False, 'errors': errors, 'warnings': warnings, 'data': None}
    
    yaml_end = 3 + end_match.end()
    yaml_content = content[3:yaml_end-5].strip()
    
    try:
        yaml_data = yaml.safe_load(yaml_content) if yaml_content else {}
        
        # 检查必需字段
        if 'msc_primary' not in yaml_data:
            warnings.append("YAML中缺少 msc_primary 字段")
        
        STATS['checks']['yaml_valid'] += 1
        return {'valid': True, 'errors': errors, 'warnings': warnings, 'data': yaml_data}
    
    except yaml.YAMLError as e:
        errors.append(f"YAML解析错误: {str(e)}")
        STATS['checks']['yaml_invalid'] += 1
        return {'valid': False, 'errors': errors, 'warnings': warnings, 'data': None}


def check_title(content, filepath):
    """检查文档标题"""
    errors = []
    warnings = []
    
    # 移除YAML头后的内容
    if content.startswith('---'):
        end_match = re.search(r'\n---\s*\n', content[3:])
        if end_match:
            yaml_end = 3 + end_match.end()
            content = content[yaml_end:]
    
    # 查找H1标题
    h1_match = re.search(r'^# (.+)$', content, re.MULTILINE)
    if not h1_match:
        errors.append("缺少H1标题（文档标题）")
        STATS['checks']['title_missing'] += 1
        return {'valid': False, 'errors': errors, 'warnings': warnings}
    
    title = h1_match.group(1).strip()
    if len(title) < 2:
        warnings.append(f"标题过短: '{title}'")
    if len(title) > 100:
        warnings.append(f"标题过长: '{title[:50]}...'")
    
    STATS['checks']['title_valid'] += 1
    return {'valid': True, 'errors': errors, 'warnings': warnings, 'title': title}


def check_headings(content, filepath):
    """检查标题层级"""
    errors = []
    warnings = []
    
    headings = re.findall(r'^(#{1,6})\s+(.+)$', content, re.MULTILINE)
    
    if not headings:
        warnings.append("文档没有章节标题")
        return {'valid': True, 'errors': errors, 'warnings': warnings}
    
    # 检查层级跳跃
    prev_level = 1
    for level, text in headings:
        level_num = len(level)
        if level_num > CHECK_RULES['max_heading_level']:
            warnings.append(f"标题层级过深: {'#' * level_num} {text}")
        
        if level_num > prev_level + 1:
            errors.append(f"标题层级跳跃: 从H{prev_level}跳到H{level_num} - {text}")
        
        prev_level = level_num
    
    # 检查中文数字编号
    h2_pattern = re.compile(r'^##\s+[一二三四五六七八九十]+[、\.\s]')
    h2_headings = [h for h in headings if h[0] == '##']
    chinese_number_count = sum(1 for _, text in h2_headings if h2_pattern.match(f'## {text}'))
    
    if h2_headings and chinese_number_count < len(h2_headings) * 0.5:
        warnings.append(f"H2标题中仅有 {chinese_number_count}/{len(h2_headings)} 使用中文数字编号")
    
    if errors:
        STATS['checks']['heading_invalid'] += 1
    else:
        STATS['checks']['heading_valid'] += 1
    
    return {'valid': len(errors) == 0, 'errors': errors, 'warnings': warnings}


def check_separators(content, filepath):
    """检查分隔线使用"""
    errors = []
    warnings = []
    
    # 检查是否使用 *** 或 ___
    if re.search(r'\n\*{3,}\s*\n', content):
        warnings.append("使用了 *** 分隔线（建议使用 ---）")
    if re.search(r'\n_{3,}\s*\n', content):
        warnings.append("使用了 ___ 分隔线（建议使用 ---）")
    
    if not warnings:
        STATS['checks']['separator_valid'] += 1
    else:
        STATS['checks']['separator_invalid'] += 1
    
    return {'valid': True, 'errors': errors, 'warnings': warnings}


def check_links(content, filepath):
    """检查链接有效性"""
    errors = []
    warnings = []
    
    # 查找Markdown链接 [text](url)
    md_links = re.findall(r'\[([^\]]+)\]\(([^)]+)\)', content)
    
    for text, url in md_links:
        # 检查内部链接
        if not url.startswith(('http://', 'https://', 'mailto:')):
            # 解析相对路径
            if url.startswith('/'):
                # 绝对路径（相对于项目根）
                target_path = DOCS_DIR.parent / url.lstrip('/')
            else:
                # 相对路径
                target_path = Path(filepath).parent / url
            
            # 移除锚点
            target_path = Path(str(target_path).split('#')[0])
            
            if not target_path.exists():
                # 可能是锚点链接
                if '#' in url and url.startswith('#'):
                    continue  # 忽略文档内锚点
                warnings.append(f"内部链接可能无效: [{text}]({url})")
    
    return {'valid': len(errors) == 0, 'errors': errors, 'warnings': warnings}


def check_tables(content, filepath):
    """检查表格格式"""
    errors = []
    warnings = []
    
    # 查找表格
    table_lines = []
    lines = content.split('\n')
    for i, line in enumerate(lines):
        if '|' in line:
            table_lines.append((i, line))
    
    # 检查表格格式
    i = 0
    while i < len(table_lines):
        line_num, line = table_lines[i]
        
        # 检查是否是表格开始
        if '|' in line:
            # 查找表头分隔行
            if i + 1 < len(table_lines) and table_lines[i + 1][0] == line_num + 1:
                next_line = table_lines[i + 1][1]
                if re.match(r'^[\s|:\-]+$', next_line):
                    # 是表格
                    pass
            else:
                warnings.append(f"第{line_num + 1}行: 表格可能缺少表头分隔行")
        
        i += 1
    
    return {'valid': len(errors) == 0, 'errors': errors, 'warnings': warnings}


def check_code_blocks(content, filepath):
    """检查代码块格式"""
    errors = []
    warnings = []
    
    # 查找代码块
    code_blocks = re.findall(r'```(\w*)\n', content)
    
    for lang in code_blocks:
        if not lang:
            warnings.append("发现未指定语言的代码块")
    
    # 检查未闭合的代码块
    open_blocks = content.count('```') % 2
    if open_blocks != 0:
        errors.append("代码块未正确闭合")
    
    return {'valid': len(errors) == 0, 'errors': errors, 'warnings': warnings}


def check_file(filepath):
    """检查单个文件"""
    result = {
        'file': filepath,
        'passed': True,
        'errors': [],
        'warnings': [],
        'checks': {}
    }
    
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        result['passed'] = False
        result['errors'].append(f"无法读取文件: {str(e)}")
        return result
    
    # 执行各项检查
    checks = [
        ('yaml', check_yaml_header),
        ('title', check_title),
        ('headings', check_headings),
        ('separators', check_separators),
        ('links', check_links),
        ('tables', check_tables),
        ('code_blocks', check_code_blocks),
    ]
    
    for check_name, check_func in checks:
        check_result = check_func(content, filepath)
        result['checks'][check_name] = check_result
        result['errors'].extend(check_result.get('errors', []))
        result['warnings'].extend(check_result.get('warnings', []))
    
    result['passed'] = len(result['errors']) == 0
    return result


def get_all_md_files():
    """获取所有需要检查的Markdown文件"""
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
    """生成检查报告"""
    report = f"""---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# FormalMath文档格式检查报告

**生成时间**: {datetime.now().strftime("%Y年%m月%d日 %H:%M:%S")}

---

## 一、检查概况

| 指标 | 数值 |
|------|------|
| 总文件数 | {STATS['total_files']} |
| 通过文件数 | {STATS['passed_files']} ✅ |
| 警告文件数 | {STATS['warning_files']} ⚠️ |
| 错误文件数 | {STATS['error_files']} ❌ |

---

## 二、详细检查统计

### 2.1 YAML元数据

| 状态 | 数量 |
|------|------|
| 有效 | {STATS['checks']['yaml_valid']} ✅ |
| 无效 | {STATS['checks']['yaml_invalid']} ❌ |
| 缺失 | {STATS['checks']['yaml_missing']} ⚠️ |

### 2.2 文档标题

| 状态 | 数量 |
|------|------|
| 有效 | {STATS['checks']['title_valid']} ✅ |
| 缺失 | {STATS['checks']['title_missing']} ❌ |

### 2.3 标题层级

| 状态 | 数量 |
|------|------|
| 有效 | {STATS['checks']['heading_valid']} ✅ |
| 无效 | {STATS['checks']['heading_invalid']} ❌ |

### 2.4 分隔线

| 状态 | 数量 |
|------|------|
| 有效 | {STATS['checks']['separator_valid']} ✅ |
| 无效 | {STATS['checks']['separator_invalid']} ⚠️ |

---

## 三、问题文件列表

### 3.1 错误文件

"""
    
    # 收集错误文件
    error_files = [r for r in STATS['file_results'] if r['errors']]
    if error_files:
        for r in error_files[:50]:
            report += f"#### {r['file']}\n\n"
            for error in r['errors']:
                report += f"- ❌ {error}\n"
            report += "\n"
        if len(error_files) > 50:
            report += f"\n... 还有 {len(error_files) - 50} 个错误文件未显示\n"
    else:
        report += "无错误文件\n"
    
    report += "\n### 3.2 警告文件\n\n"
    
    # 收集警告文件
    warning_files = [r for r in STATS['file_results'] if r['warnings'] and not r['errors']]
    if warning_files:
        for r in warning_files[:30]:
            report += f"#### {r['file']}\n\n"
            for warning in r['warnings'][:5]:
                report += f"- ⚠️ {warning}\n"
            report += "\n"
        if len(warning_files) > 30:
            report += f"\n... 还有 {len(warning_files) - 30} 个警告文件未显示\n"
    else:
        report += "无警告文件\n"
    
    report += f"""

---

## 四、检查规则说明

| 规则 | 说明 | 级别 |
|------|------|------|
| YAML元数据 | 必须包含有效的YAML头，包含msc_primary字段 | 必需 |
| 文档标题 | 必须包含H1标题（# 标题） | 必需 |
| 标题层级 | 不应跳过层级（如H1直接跳到H3） | 必需 |
| 分隔线 | 建议使用 --- 而非 *** 或 ___ | 建议 |
| 内部链接 | 链接的文件应存在 | 建议 |
| 代码块 | 应指定语言类型 | 建议 |

---

**报告生成**: ✅ 完成
**最后更新**: {datetime.now().strftime("%Y年%m月%d日")}
"""
    
    with open(REPORT_FILE, 'w', encoding='utf-8') as f:
        f.write(report)
    
    log_message(f"检查报告已生成: {REPORT_FILE}")


def main():
    """主函数"""
    print("=" * 60)
    print("FormalMath文档格式检查工具")
    print("=" * 60)
    
    # 清空日志文件
    with open(LOG_FILE, 'w', encoding='utf-8') as f:
        f.write(f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] 开始检查\n")
    
    # 获取所有文件
    print("\n📁 扫描文档目录...")
    md_files = get_all_md_files()
    STATS['total_files'] = len(md_files)
    print(f"   找到 {len(md_files)} 个Markdown文件")
    
    # 检查文件
    print("\n🔍 开始检查文档...")
    for i, filepath in enumerate(md_files, 1):
        if i % 100 == 0:
            print(f"   已检查 {i}/{len(md_files)} 个文件...")
        
        result = check_file(filepath)
        STATS['file_results'].append(result)
        
        if result['errors']:
            STATS['error_files'] += 1
        elif result['warnings']:
            STATS['warning_files'] += 1
        else:
            STATS['passed_files'] += 1
    
    print(f"\n✅ 检查完成:")
    print(f"   - 通过: {STATS['passed_files']} 个文件")
    print(f"   - 警告: {STATS['warning_files']} 个文件")
    print(f"   - 错误: {STATS['error_files']} 个文件")
    
    # 生成报告
    print("\n📝 生成检查报告...")
    generate_report()
    
    print(f"\n📄 报告位置: {REPORT_FILE}")
    print(f"📝 日志位置: {LOG_FILE}")
    print("\n" + "=" * 60)


if __name__ == '__main__':
    main()
