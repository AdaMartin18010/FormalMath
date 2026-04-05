#!/usr/bin/env python3
"""
FormalMath项目Frontmatter标准化工具
扫描所有Markdown文档，检查并标准化Frontmatter格式
"""

import os
import re
import yaml
import json
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Tuple, Optional, Any

# 必需字段
REQUIRED_FIELDS = ['title', 'msc_primary', 'processed_at']

# 可选字段
OPTIONAL_FIELDS = ['msc_secondary', 'version', 'author', 'tags', 'category']

# 有效的MSC编码格式 (5位数字或字母组合)
MSC_PATTERN = re.compile(r'^\d{2}[A-Z]\d{2}$')

# ISO 8601日期格式
ISO_DATE_FORMAT = '%Y-%m-%d'

def find_all_markdown_files(root_dir: str) -> List[str]:
    """递归查找所有Markdown文件"""
    md_files = []
    for dirpath, dirnames, filenames in os.walk(root_dir):
        # 跳过.git和node_modules等目录
        dirnames[:] = [d for d in dirnames if d not in ['.git', 'node_modules', '__pycache__', '.venv', 'venv']]
        for filename in filenames:
            if filename.endswith('.md'):
                md_files.append(os.path.join(dirpath, filename))
    return md_files

def extract_frontmatter(content: str) -> Tuple[Optional[str], str]:
    """提取YAML frontmatter，返回(frontmatter, 剩余内容)"""
    if not content.startswith('---'):
        return None, content
    
    # 查找第二个---
    match = re.search(r'^---\s*\n(.*?)\n---\s*\n', content, re.DOTALL)
    if not match:
        return None, content
    
    frontmatter = match.group(1)
    remaining = content[match.end():]
    return frontmatter, remaining

def parse_frontmatter(frontmatter_str: str) -> Tuple[Optional[Dict], List[str]]:
    """解析YAML frontmatter，返回(数据, 错误列表)"""
    errors = []
    try:
        data = yaml.safe_load(frontmatter_str)
        if data is None:
            data = {}
        return data, errors
    except yaml.YAMLError as e:
        errors.append(f"YAML解析错误: {e}")
        return None, errors

def validate_msc_code(code: Any, field_name: str) -> Tuple[bool, List[str]]:
    """验证MSC编码格式"""
    errors = []
    
    if code is None:
        return True, []  # 可选字段可以为空
    
    if isinstance(code, str):
        codes = [code]
    elif isinstance(code, list):
        codes = code
    elif isinstance(code, int):
        # 数字格式需要转换为字符串
        return False, [f"{field_name}: MSC编码应为字符串格式，当前为数字: {code}"]
    else:
        return False, [f"{field_name}: 不支持的MSC编码类型: {type(code)}"]
    
    for c in codes:
        if not isinstance(c, str):
            errors.append(f"{field_name}: MSC编码应为字符串，当前为: {type(c)}")
            continue
        # 清理可能的引号
        c_clean = c.strip().strip('"\'')
        if not MSC_PATTERN.match(c_clean):
            errors.append(f"{field_name}: 无效的MSC编码格式 '{c}'，应为XXYXX格式（如03E99）")
    
    return len(errors) == 0, errors

def validate_date_format(date_val: Any, field_name: str) -> Tuple[bool, List[str]]:
    """验证日期格式是否为ISO 8601"""
    errors = []
    
    if date_val is None:
        return False, [f"{field_name}: 缺少必需字段"]
    
    # 处理datetime对象
    if isinstance(date_val, datetime):
        return True, []
    
    if not isinstance(date_val, str):
        return False, [f"{field_name}: 日期应为字符串格式，当前为: {type(date_val)}"]
    
    # 尝试解析ISO格式
    date_str = date_val.strip().strip('"\'')
    
    # 支持多种日期格式
    formats = [
        '%Y-%m-%d',
        '%Y-%m-%d %H:%M:%S',
        '%Y-%m-%dT%H:%M:%S',
        '%Y年%m月%d日',
        '%Y/%m/%d',
    ]
    
    for fmt in formats:
        try:
            datetime.strptime(date_str, fmt)
            return True, []
        except ValueError:
            continue
    
    errors.append(f"{field_name}: 无法识别的日期格式 '{date_val}'，建议使用YYYY-MM-DD格式")
    return False, errors

def check_frontmatter(filepath: str, content: str) -> Dict:
    """检查单个文件的frontmatter，返回检查结果"""
    result = {
        'filepath': filepath,
        'has_frontmatter': False,
        'frontmatter_raw': None,
        'data': None,
        'errors': [],
        'warnings': [],
        'missing_fields': [],
        'needs_update': False
    }
    
    frontmatter_str, remaining = extract_frontmatter(content)
    
    if frontmatter_str is None:
        result['errors'].append("缺少Frontmatter")
        result['missing_fields'] = REQUIRED_FIELDS
        result['needs_update'] = True
        return result
    
    result['has_frontmatter'] = True
    result['frontmatter_raw'] = frontmatter_str
    
    # 解析YAML
    data, parse_errors = parse_frontmatter(frontmatter_str)
    if data is None:
        result['errors'].extend(parse_errors)
        result['needs_update'] = True
        return result
    
    result['data'] = data
    
    # 检查必需字段
    for field in REQUIRED_FIELDS:
        if field not in data or data[field] is None:
            result['missing_fields'].append(field)
            result['needs_update'] = True
    
    # 验证title
    if 'title' in data and data['title']:
        if not isinstance(data['title'], str):
            result['errors'].append(f"title: 应为字符串类型，当前为: {type(data['title'])}")
            result['needs_update'] = True
    elif 'title' not in data or not data['title']:
        # 尝试从文件内容提取标题
        title_match = re.search(r'^#\s+(.+)$', remaining, re.MULTILINE)
        if title_match:
            result['warnings'].append(f"title: 可以从内容中提取: '{title_match.group(1)[:50]}...'")
        result['needs_update'] = True
    
    # 验证msc_primary
    if 'msc_primary' in data:
        valid, errors = validate_msc_code(data['msc_primary'], 'msc_primary')
        if not valid:
            result['errors'].extend(errors)
            result['needs_update'] = True
    
    # 验证msc_secondary
    if 'msc_secondary' in data:
        valid, errors = validate_msc_code(data['msc_secondary'], 'msc_secondary')
        if not valid:
            result['errors'].extend(errors)
            result['needs_update'] = True
    
    # 验证processed_at
    if 'processed_at' in data:
        valid, errors = validate_date_format(data['processed_at'], 'processed_at')
        if not valid:
            result['errors'].extend(errors)
            result['needs_update'] = True
    
    # 检查未知字段
    all_valid_fields = REQUIRED_FIELDS + OPTIONAL_FIELDS
    for field in data.keys():
        if field not in all_valid_fields:
            result['warnings'].append(f"未知字段: {field}")
    
    return result

def standardize_frontmatter(result: Dict, content: str) -> Tuple[str, Dict]:
    """标准化frontmatter，返回(新内容, 修改信息)"""
    modifications = {
        'added_fields': [],
        'modified_fields': [],
        'extracted_title': False
    }
    
    frontmatter_str, remaining = extract_frontmatter(content)
    data = result['data'] or {}
    
    # 提取标题（如果需要）
    if 'title' not in data or not data['title']:
        title_match = re.search(r'^#\s+(.+)$', remaining, re.MULTILINE)
        if title_match:
            data['title'] = title_match.group(1).strip()
            modifications['added_fields'].append('title')
            modifications['extracted_title'] = True
        else:
            # 使用文件名作为标题
            filename = os.path.basename(result['filepath']).replace('.md', '')
            data['title'] = filename
            modifications['added_fields'].append('title')
    
    # 标准化title（移除前后空格）
    if isinstance(data.get('title'), str):
        data['title'] = data['title'].strip()
    
    # 标准化msc_primary
    if 'msc_primary' in data:
        if isinstance(data['msc_primary'], int):
            data['msc_primary'] = str(data['msc_primary']).zfill(5)
            modifications['modified_fields'].append('msc_primary')
        elif isinstance(data['msc_primary'], str):
            # 确保引号格式一致（YAML不需要显式引号）
            data['msc_primary'] = data['msc_primary'].strip().strip('"\'')
    else:
        # 默认MSC编码
        data['msc_primary'] = '00A99'  # 一般数学
        modifications['added_fields'].append('msc_primary')
    
    # 标准化msc_secondary
    if 'msc_secondary' in data:
        if isinstance(data['msc_secondary'], (int, str)):
            data['msc_secondary'] = [str(data['msc_secondary'])]
            modifications['modified_fields'].append('msc_secondary')
        elif isinstance(data['msc_secondary'], list):
            # 确保所有元素都是字符串
            data['msc_secondary'] = [
                str(item).strip().strip('"\'') for item in data['msc_secondary']
            ]
    
    # 标准化processed_at
    if 'processed_at' not in data or not data['processed_at']:
        data['processed_at'] = datetime.now().strftime(ISO_DATE_FORMAT)
        modifications['added_fields'].append('processed_at')
    elif isinstance(data['processed_at'], str):
        # 尝试解析并转换为标准格式
        date_str = data['processed_at'].strip().strip('"\'')
        formats = [
            '%Y-%m-%d',
            '%Y-%m-%d %H:%M:%S',
            '%Y-%m-%dT%H:%M:%S',
            '%Y年%m月%d日',
            '%Y/%m/%d',
        ]
        for fmt in formats:
            try:
                dt = datetime.strptime(date_str, fmt)
                data['processed_at'] = dt.strftime(ISO_DATE_FORMAT)
                if fmt != '%Y-%m-%d':
                    modifications['modified_fields'].append('processed_at')
                break
            except ValueError:
                continue
    
    # 生成标准化的YAML frontmatter
    # 使用default_flow_style=False来确保正确的YAML格式
    yaml_content = yaml.dump(data, allow_unicode=True, sort_keys=False, default_flow_style=False)
    new_frontmatter = f"---\n{yaml_content}---\n"
    
    # 组合新内容
    if frontmatter_str is not None:
        new_content = new_frontmatter + remaining
    else:
        new_content = new_frontmatter + content
    
    return new_content, modifications

def main():
    """主函数"""
    root_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    
    print(f"扫描目录: {root_dir}")
    print("=" * 60)
    
    # 查找所有Markdown文件
    md_files = find_all_markdown_files(root_dir)
    print(f"找到 {len(md_files)} 个Markdown文件")
    print()
    
    # 检查结果统计
    stats = {
        'total': len(md_files),
        'has_frontmatter': 0,
        'no_frontmatter': 0,
        'needs_update': 0,
        'errors': 0,
        'warnings': 0,
        'fixed': 0
    }
    
    detailed_results = []
    
    for filepath in md_files:
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 检查frontmatter
            result = check_frontmatter(filepath, content)
            
            if result['has_frontmatter']:
                stats['has_frontmatter'] += 1
            else:
                stats['no_frontmatter'] += 1
            
            if result['needs_update']:
                stats['needs_update'] += 1
            
            stats['errors'] += len(result['errors'])
            stats['warnings'] += len(result['warnings'])
            
            # 如果需要更新，进行标准化
            if result['needs_update']:
                new_content, modifications = standardize_frontmatter(result, content)
                
                # 写回文件
                with open(filepath, 'w', encoding='utf-8') as f:
                    f.write(new_content)
                
                result['modifications'] = modifications
                stats['fixed'] += 1
            
            detailed_results.append(result)
            
        except Exception as e:
            print(f"处理文件 {filepath} 时出错: {e}")
            stats['errors'] += 1
    
    # 生成报告
    report_lines = []
    report_lines.append("# FormalMath项目Frontmatter标准化报告")
    report_lines.append("")
    report_lines.append(f"**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    report_lines.append("")
    report_lines.append("## 统计摘要")
    report_lines.append("")
    report_lines.append(f"- **总文件数**: {stats['total']}")
    report_lines.append(f"- **有Frontmatter**: {stats['has_frontmatter']}")
    report_lines.append(f"- **无Frontmatter**: {stats['no_frontmatter']}")
    report_lines.append(f"- **需要更新**: {stats['needs_update']}")
    report_lines.append(f"- **已修复**: {stats['fixed']}")
    report_lines.append(f"- **错误总数**: {stats['errors']}")
    report_lines.append(f"- **警告总数**: {stats['warnings']}")
    report_lines.append("")
    
    # 详细问题列表
    report_lines.append("## 详细问题列表")
    report_lines.append("")
    
    problem_files = [r for r in detailed_results if r['errors'] or r['warnings'] or r.get('modifications')]
    
    if problem_files:
        for result in problem_files[:100]:  # 限制显示数量
            rel_path = os.path.relpath(result['filepath'], root_dir)
            report_lines.append(f"### {rel_path}")
            report_lines.append("")
            
            if result['errors']:
                report_lines.append("**错误**:")
                for error in result['errors']:
                    report_lines.append(f"- ❌ {error}")
                report_lines.append("")
            
            if result['warnings']:
                report_lines.append("**警告**:")
                for warning in result['warnings']:
                    report_lines.append(f"- ⚠️ {warning}")
                report_lines.append("")
            
            if result.get('modifications'):
                mods = result['modifications']
                if mods['added_fields']:
                    report_lines.append(f"**新增字段**: {', '.join(mods['added_fields'])}")
                if mods['modified_fields']:
                    report_lines.append(f"**修改字段**: {', '.join(mods['modified_fields'])}")
                if mods.get('extracted_title'):
                    report_lines.append("**标题来源**: 从文档内容自动提取")
                report_lines.append("")
            
            report_lines.append("---")
            report_lines.append("")
        
        if len(problem_files) > 100:
            report_lines.append(f"*... 还有 {len(problem_files) - 100} 个文件的问题未显示 ...*")
            report_lines.append("")
    else:
        report_lines.append("✅ 所有文件Frontmatter格式正确，无需修改。")
        report_lines.append("")
    
    # 标准化规范说明
    report_lines.append("## 标准化规范")
    report_lines.append("")
    report_lines.append("### 必需字段")
    report_lines.append("")
    report_lines.append("| 字段 | 类型 | 说明 |")
    report_lines.append("|------|------|------|")
    report_lines.append("| `title` | string | 文档标题 |")
    report_lines.append("| `msc_primary` | string | 主要MSC分类编码（格式：XXYXX，如03E99） |")
    report_lines.append("| `processed_at` | string | 处理日期（ISO 8601格式：YYYY-MM-DD） |")
    report_lines.append("")
    report_lines.append("### 可选字段")
    report_lines.append("")
    report_lines.append("| 字段 | 类型 | 说明 |")
    report_lines.append("|------|------|------|")
    report_lines.append("| `msc_secondary` | array[string] | 次要MSC分类编码列表 |")
    report_lines.append("| `version` | string | 文档版本 |")
    report_lines.append("| `author` | string | 作者 |")
    report_lines.append("| `tags` | array[string] | 标签列表 |")
    report_lines.append("| `category` | string | 分类 |")
    report_lines.append("")
    report_lines.append("### Frontmatter示例")
    report_lines.append("")
    report_lines.append("```yaml")
    report_lines.append("---")
    report_lines.append("title: 集合 (Set)")
    report_lines.append("msc_primary: 03E99")
    report_lines.append("msc_secondary:")
    report_lines.append("  - 00A05")
    report_lines.append("processed_at: '2026-04-05'")
    report_lines.append("---")
    report_lines.append("```")
    report_lines.append("")
    
    # 写入报告文件
    report_path = os.path.join(root_dir, '00-Frontmatter标准化报告.md')
    with open(report_path, 'w', encoding='utf-8') as f:
        f.write('\n'.join(report_lines))
    
    print(f"\n报告已生成: {report_path}")
    print(f"\n统计:")
    print(f"  - 总文件数: {stats['total']}")
    print(f"  - 有Frontmatter: {stats['has_frontmatter']}")
    print(f"  - 无Frontmatter: {stats['no_frontmatter']}")
    print(f"  - 需要更新: {stats['needs_update']}")
    print(f"  - 已修复: {stats['fixed']}")
    print(f"  - 错误: {stats['errors']}")
    print(f"  - 警告: {stats['warnings']}")

if __name__ == '__main__':
    main()
