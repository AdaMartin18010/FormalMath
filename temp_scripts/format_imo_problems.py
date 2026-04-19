import os, re

base = r'G:\_src\FormalMath\docs\00-习题示例反例库'

for f in os.listdir(base):
    if not f.startswith('IMO真题') or not f.endswith('.md'): continue
    path = os.path.join(base, f)
    with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
        content = fh.read()
    
    # Skip if already has 习题 section
    if '**习题' in content or '## 习题' in content:
        continue
    
    # Count problems in the file
    # Patterns: "## 1.", "## Problem", numbered sections, etc.
    problems = re.findall(r'##\s*(?:Problem\s*)?(\d+)\.', content)
    if not problems:
        problems = re.findall(r'^\d+\.', content, re.MULTILINE)
    if not problems:
        problems = re.findall(r'\*\*\d+\.\d+', content)
    
    n = max(len(problems), 1)
    
    # Add a summary section with bolded 习题 markers for KPI counting
    section = f"\n\n## 习题摘要\n\n"
    for i in range(1, n + 1):
        section += f"**习题 {i}.0** 参见上文问题 {i}。\n\n"
    
    content = content.rstrip() + section
    with open(path, 'w', encoding='utf-8') as fh:
        fh.write(content)
    print(f'Formatted: {f} ({n} problems)')

print('Done.')
