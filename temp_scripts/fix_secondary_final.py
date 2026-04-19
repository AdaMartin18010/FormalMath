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
        # Fix double dash: 55--00 -> 55-00
        new_content = re.sub(r'(\d{2})--00', r'\1-00', new_content)
        # Fix letter-dash-00: 03E-00 -> 03E00, 14F-00 -> 14F00
        new_content = re.sub(r'(\d{2}[A-Z])-00', r'\100', new_content)
        # Fix stray quote before code: "03E00 -> "03E00 (actually keep quote)
        new_content = re.sub(r'"([\dA-Z-]+)\s*$', r'"\1"', new_content, flags=re.MULTILINE)
        # Fix missing closing quote in lists: "03E00 -> "03E00"
        new_content = re.sub(r'"(\d{2}[A-Z]?\d{2})\b(?!"|\')', r'"\1"', new_content)
        new_content = re.sub(r"'(\d{2}[A-Z]?\d{2})\b(?!\"|\')", r"'\1'", new_content)
        
        if new_content != content:
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write(new_content)
            fixed += 1

print(f'Total fixes: {fixed}')
