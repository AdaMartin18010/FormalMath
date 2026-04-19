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
        
        new_content = content
        # Pattern 1: YAML list items: "- 03Bxx" -> "- 03B00"
        new_content = re.sub(r'(^\s+-\s+)(\d{2}[A-Z]?)xx', r'\1\2-00', new_content, flags=re.MULTILINE | re.IGNORECASE)
        # Pattern 2: inside brackets: ['14Fxx'] -> ['14F00']
        new_content = re.sub(r"'(\d{2}[A-Z]?)xx'", r"'\1-00'", new_content, flags=re.IGNORECASE)
        new_content = re.sub(r"'(\d{2}-)XX'", r"'\1-00'", new_content, flags=re.IGNORECASE)
        # Pattern 3: comma-separated in a string line: "51-XX, 53-XX"
        new_content = re.sub(r'(\d{2}-)XX', r'\1-00', new_content, flags=re.IGNORECASE)
        # Pattern 4: standalone xx after digits: 03Exx -> 03E-00
        new_content = re.sub(r'(\d{2}[A-Z])xx\b', r'\1-00', new_content, flags=re.IGNORECASE)
        
        if new_content != content:
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write(new_content)
            fixed += 1
            if fixed <= 5:
                print(f'Fixed: {os.path.relpath(path, base)}')

print(f'Total fixes: {fixed}')
