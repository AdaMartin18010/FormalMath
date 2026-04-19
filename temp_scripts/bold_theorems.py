import os, re

base = r'G:\_src\FormalMath\docs'
fixed = 0

for root, dirs, files in os.walk(base):
    for f in files:
        if not f.endswith('.md'): continue
        path = os.path.join(root, f)
        with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
            content = fh.read()
        
        # Only bold unbolded theorem patterns: not preceded by ** or # or already bolded
        # Pattern: 定理 followed by digits and dots, not already wrapped in **
        new_content = re.sub(
            r'(?<!\*\*)(?<!# )(?<!#)(定理\s+\d+(?:\.\d+)+)',
            r'**\1**',
            content
        )
        
        if new_content != content:
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write(new_content)
            fixed += 1
            if fixed <= 5:
                print(f'Bolded theorems in: {os.path.relpath(path, base)}')

print(f'Total files with bolded theorems: {fixed}')
