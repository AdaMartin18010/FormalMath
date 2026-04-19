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
        end = new_content.find('---', 3)
        if end == -1: continue
        
        fm = new_content[3:end]
        rest = new_content[end:]
        
        # Fix escaped quotes with extra quotes: \"53-00"" -> "53-00"
        fm = re.sub(r'\\"([\dA-Z-]+)""', r'"\1"', fm)
        # Fix escaped quotes: \"53-00\" -> "53-00"
        fm = re.sub(r'\\"([\dA-Z-]+)\\"', r'"\1"', fm)
        # Fix orphaned list items (line starting with - but no key above in frontmatter)
        # This is tricky; we'll fix specific cases: standalone - XX-YY lines
        fm = re.sub(r'\n\n\s+-\s+\d{2}-\d{2}\s*\n', '\n', fm)
        # Fix broken dates: "2026"-04-08" -> "2026-04-08"
        fm = re.sub(r'"(\d{4})"-([^"\n]+)"', r'"\1-\2"', fm)
        fm = re.sub(r"'(\d{4})'-([^'\n]+)'", r"'\1-\2'", fm)
        # Remove @ symbols
        fm = re.sub(r'"@"', '', fm)
        fm = re.sub(r"'@'", '', fm)
        fm = re.sub(r'^\s+-\s+@\s*$', '', fm, flags=re.MULTILINE)
        # Clean empty brackets and trailing commas in lists
        fm = re.sub(r'\[\s*,\s*\]', '[]', fm)
        fm = re.sub(r'\[\s*\]', '', fm)
        # Clean consecutive blank lines
        fm = re.sub(r'\n{3,}', '\n\n', fm)
        
        new_content = '---' + fm + rest
        
        if new_content != content:
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write(new_content)
            fixed += 1

print(f'Total fixes: {fixed}')
