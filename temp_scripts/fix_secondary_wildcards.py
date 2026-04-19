import os, re

base = r'G:\_src\FormalMath\docs'
fixed = 0
for root, dirs, files in os.walk(base):
    for f in files:
        if not f.endswith('.md'): continue
        path = os.path.join(root, f)
        with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
            content = fh.read()
        if not content.strip().startswith('---'): continue
        # Replace xx/XX wildcards in msc_secondary blocks
        new_content = re.sub(r'\"(\d{2}[A-Z]?)xx\"', r'\"\1-00\"', content, flags=re.IGNORECASE)
        new_content = re.sub(r'\"(\d{2}-)XX\"', r'\"\1-00\"', new_content, flags=re.IGNORECASE)
        if new_content != content:
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write(new_content)
            fixed += 1
            if fixed <= 5:
                print(f'Fixed: {os.path.relpath(path, base)}')

print(f'Total secondary wildcard fixes: {fixed}')
