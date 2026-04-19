import os, re
from collections import defaultdict

base = r'G:\_src\FormalMath\docs'
courses = defaultdict(lambda: {'docs':0, 'thms':0, 'exs':0, 'lean':0, 'files':[]})
silver_count = 0
thm_total = 0
ex_total = 0
lean_total = 0

for root, dirs, files in os.walk(base):
    for f in files:
        if not f.endswith('.md'): continue
        path = os.path.join(root, f)
        with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
            content = fh.read()
        if not content.strip().startswith('---'): continue
        
        m = re.search(r'^level:\s*(.+)$', content, re.MULTILINE)
        if not m or 'silver' not in m.group(1).lower():
            continue
        silver_count += 1
        
        thms = len(re.findall(r'\*\*定理\s+\d+\.\d+', content))
        exs = len(re.findall(r'\*\*习题\s+\d+\.\d+', content))
        lean = len(re.findall(r'Lean4|lean4|\.lean', content))
        thm_total += thms
        ex_total += exs
        lean_total += lean
        
        cm = re.search(r'course:\s*(.+)', content)
        tm = re.search(r'target_courses:\s*\[(.*?)\]', content, re.DOTALL)
        course = None
        if cm:
            course = cm.group(1).strip().strip('"\'')
        elif tm:
            course = tm.group(1).strip().strip('"\'').split(',')[0].strip().strip('"\'')
        
        if course:
            courses[course]['docs'] += 1
            courses[course]['thms'] += thms
            courses[course]['exs'] += exs
            courses[course]['lean'] += lean
            courses[course]['files'].append(os.path.relpath(path, base))

print(f'Silver docs: {silver_count}')
print(f'Theorems: {thm_total}')
print(f'Exercises: {ex_total}')
print(f'Lean4 refs: {lean_total}')
print()
for c, data in sorted(courses.items(), key=lambda x: -x[1]['docs']):
    print(f'{c}: docs={data["docs"]}, thms={data["thms"]}, exs={data["exs"]}, lean={data["lean"]}')
