import os
import re
from datetime import datetime

dir_path = 'docs/05-拓扑学'
files = [f for f in os.listdir(dir_path) if f.endswith('.md')]
files.sort()

fixed_count = 0
processed_date = '2026-04-05'

def extract_title(content):
    """从文档内容中提取标题"""
    # 查找第一个一级标题
    match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
    if match:
        title = match.group(1).strip()
        # 移除主题编号等额外信息
        title = re.sub(r'\s*/\s*.+$', '', title)  # 移除英文部分
        title = re.sub(r'\s*\([^)]+\)\s*$', '', title)  # 移除括号内容
        title = title.strip()
        return title
    return None

def fix_frontmatter(filepath, filename):
    """修复Frontmatter"""
    global fixed_count
    
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 检查是否已经有完整格式
    has_title = 'title:' in content[:500]
    has_processed = 'processed_at:' in content[:500]
    
    if has_title and has_processed:
        return False  # 已经完整，不需要修复
    
    # 提取标题
    title = extract_title(content)
    if not title:
        # 使用文件名作为标题
        title = filename.replace('.md', '').replace('-', ' ')
    
    # 提取现有的MSC信息
    msc_primary_match = re.search(r'msc_primary:\s*["\']?([^"\'\n]+)["\']?', content)
    msc_secondary_match = re.search(r'msc_secondary:\s*\n((?:-\s*[^\n]+\n?)+)', content)
    
    msc_primary = msc_primary_match.group(1).strip() if msc_primary_match else '54-XX'
    
    msc_secondary = []
    if msc_secondary_match:
        secondary_text = msc_secondary_match.group(1)
        for line in secondary_text.strip().split('\n'):
            line = line.strip()
            if line.startswith('- '):
                msc_secondary.append(line[2:].strip())
    
    # 构建新的Frontmatter
    new_frontmatter = f'---\n'
    new_frontmatter += f'title: "{title}"\n'
    new_frontmatter += f'msc_primary: "{msc_primary}"\n'
    new_frontmatter += f'msc_secondary: {msc_secondary}\n'
    new_frontmatter += f'processed_at: \'{processed_date}\'\n'
    new_frontmatter += f'---\n'
    
    # 替换旧的Frontmatter
    old_frontmatch = re.match(r'^---\s*\n.*?---\s*\n', content, re.DOTALL)
    if old_frontmatch:
        new_content = new_frontmatter + content[old_frontmatch.end():]
    else:
        # 没有Frontmatter，添加到开头
        new_content = new_frontmatter + '\n' + content
    
    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(new_content)
    
    fixed_count += 1
    return True

print('=== 开始修复MSC Frontmatter ===')
print()

for fname in files:
    fpath = os.path.join(dir_path, fname)
    if fix_frontmatter(fpath, fname):
        print(f'已修复: {fname}')

print()
print(f'=== 修复完成 ===')
print(f'修复文件数: {fixed_count}')
print(f'处理日期: {processed_date}')
