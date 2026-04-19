import os, re

base = r'G:\_src\FormalMath\docs'

# Core course docs that are high quality and should be "completed"
completed_candidates = []
for root, _, files in os.walk(base):
    for f in files:
        if not f.endswith('.md'): continue
        path = os.path.join(root, f)
        with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
            content = fh.read()
        if 'silver' not in content.lower(): continue
        # Check if it has exercises and references
        has_ex = '**习题' in content or '习题' in content
        has_refs = '参考文献' in content or 'references' in content.lower()
        # Core course docs in specific dirs
        rel = os.path.relpath(path, base)
        is_core = any(d in rel for d in [
            '00-银层核心课程\\MIT-18.02-多元微积分',
            '00-银层核心课程\\MIT-18.06-线性代数',
            '00-银层核心课程\\MIT-18.100A-实分析',
            '00-银层核心课程\\MIT-18.701-抽象代数',
            '03-分析学\\01-实分析\\MIT-18.100A',
        ])
        if is_core and has_ex:
            completed_candidates.append(path)

# Add review_status: draft to missing ones
fixed_draft = 0
fixed_completed = 0

for root, _, files in os.walk(base):
    for f in files:
        if not f.endswith('.md'): continue
        path = os.path.join(root, f)
        with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
            content = fh.read()
        if 'silver' not in content.lower(): continue
        if not content.strip().startswith('---'): continue
        
        if 'review_status:' in content:
            continue  # already has status
        
        end = content.find('---', 3)
        if end == -1: continue
        
        if path in completed_candidates:
            new_content = content[:end] + 'review_status: completed\n' + content[end:]
            fixed_completed += 1
        else:
            new_content = content[:end] + 'review_status: draft\n' + content[end:]
            fixed_draft += 1
        
        with open(path, 'w', encoding='utf-8') as fh:
            fh.write(new_content)

print(f'Added review_status: completed to {fixed_completed} docs')
print(f'Added review_status: draft to {fixed_draft} docs')
