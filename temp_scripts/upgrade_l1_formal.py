import os, re

math_docs = [
    r'G:\_src\FormalMath\docs\00-知识层次体系\L1-形式化定义层\04-分析学基础\01-极限epsilon-delta定义.md',
    r'G:\_src\FormalMath\docs\00-知识层次体系\L1-形式化定义层\03-代数结构\04-群定义.md',
    r'G:\_src\FormalMath\docs\00-知识层次体系\L1-形式化定义层\06-逻辑基础\01-命题逻辑.md',
    r'G:\_src\FormalMath\docs\00-知识层次体系\L1-形式化定义层\04-分析学基础\04-连续性定义.md',
    r'G:\_src\FormalMath\docs\00-知识层次体系\L1-形式化定义层\03-代数结构\16-向量空间.md',
    r'G:\_src\FormalMath\docs\00-知识层次体系\L1-形式化定义层\05-拓扑学基础\01-拓扑空间.md',
    r'G:\_src\FormalMath\docs\00-知识层次体系\L1-形式化定义层\02-数系构造\01-Peano公理.md',
    r'G:\_src\FormalMath\docs\00-知识层次体系\L1-形式化定义层\01-集合论基础\01-集合与元素.md',
    r'G:\_src\FormalMath\docs\00-知识层次体系\L1-形式化定义层\02-数系构造\07-实数构造.md',
    r'G:\_src\FormalMath\docs\00-知识层次体系\L1-形式化定义层\04-分析学基础\06-导数定义.md',
]

course_map = {
    '极限epsilon-delta定义': 'MIT 18.100A',
    '连续性定义': 'MIT 18.100A',
    '导数定义': 'MIT 18.100A',
    '群定义': 'MIT 18.701',
    '向量空间': 'MIT 18.06',
    '拓扑空间': 'Harvard 232br',
    '命题逻辑': 'MIT 18.100A',
    'Peano公理': 'MIT 18.100A',
    '实数构造': 'MIT 18.100A',
    '集合与元素': 'MIT 18.100A',
}

msc_map = {
    '极限epsilon-delta定义': '26',
    '连续性定义': '26',
    '导数定义': '26',
    '群定义': '20',
    '向量空间': '15',
    '拓扑空间': '54',
    '命题逻辑': '03',
    'Peano公理': '03',
    '实数构造': '26',
    '集合与元素': '03',
}

for path in math_docs:
    if not os.path.exists(path):
        print(f'MISSING: {path}')
        continue
    with open(path, 'r', encoding='utf-8') as f:
        content = f.read()
    base_name = os.path.splitext(os.path.basename(path))[0]
    course = course_map.get(base_name, '00')
    msc = msc_map.get(base_name, '00')
    if not content.strip().startswith('---'):
        fm = f'''---
title: "{base_name}"
level: silver
msc_primary: "{msc}"
course: {course}
review_status: draft
---

'''
        new_content = fm + content
    else:
        new_content = re.sub(r'^level:\s*\S+', 'level: silver', content, flags=re.MULTILINE)
        if 'msc_primary:' not in new_content:
            end = new_content.find('---', 3)
            if end != -1:
                new_content = new_content[:end] + f'msc_primary: "{msc}"\n' + new_content[end:]
        if 'course:' not in new_content and 'target_courses:' not in new_content:
            end = new_content.find('---', 3)
            if end != -1:
                new_content = new_content[:end] + f'course: {course}\n' + new_content[end:]
    if new_content != content:
        with open(path, 'w', encoding='utf-8') as f:
            f.write(new_content)
        print(f'UPGRADED: {base_name}')
    else:
        print(f'NO CHANGE: {base_name}')

print('Done.')
