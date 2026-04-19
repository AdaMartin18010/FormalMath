import os
import re

base = r'G:\_src\FormalMath\docs'

# Directory to MSC heuristic mapping
DIR_MAP = {
    '01-基础数学': '00', '02-代数结构': '20', '03-分析学': '26',
    '04-几何与拓扑': '51', '05-数论': '11', '06-概率论与统计': '60',
    '07-数理逻辑': '03', '08-计算数学': '65', '09-形式化证明': '03',
    '10-应用数学': '00', '11-数学应用': '00', '11-高级数学': '00',
    '11-数学物理': '00', '12-学术资源': '01', '13-代数几何': '14',
    '数学家': '01', 'project': '00', '工具': '00',
    'supplement': '00', '04-习题与练习': '00', '00-合并内容': '00',
    '00-数学史': '01', '00-表征实例库': '00', '03-学习指南': '00',
    '06-实例与案例分析': '00', '00-习题示例反例库': '00',
    '07-反例与辨析': '00', '00-交叉引用网络': '00',
}

def guess_msc(path):
    rel = os.path.relpath(path, base)
    parts = rel.split(os.sep)
    for part in parts:
        if part in DIR_MAP:
            return DIR_MAP[part]
    return '00'

def guess_title(path):
    name = os.path.splitext(os.path.basename(path))[0]
    # Remove leading numbering like "01-"
    name = re.sub(r'^\d+[-_.]', '', name)
    name = name.replace('-', ' ').replace('_', ' ')
    return name.strip()

count = 0
for root, dirs, files in os.walk(base):
    for f in files:
        if not f.endswith('.md'):
            continue
        path = os.path.join(root, f)
        with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
            content = fh.read()
        if content.strip().startswith('---'):
            continue
        
        title = guess_title(path)
        msc = guess_msc(path)
        fm = f"""---
title: "{title}"
msc_primary: "{msc}"
---

"""
        new_content = fm + content
        with open(path, 'w', encoding='utf-8') as fh:
            fh.write(new_content)
        count += 1
        if count % 50 == 0:
            print(f'Processed {count}...')

print(f'Total added front matter: {count}')
