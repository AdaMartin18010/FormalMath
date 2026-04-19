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
        # Aggressive @ removal in frontmatter area
        end = new_content.find('---', 3)
        if end != -1:
            fm = new_content[3:end]
            rest = new_content[end:]
            # Remove @ entries from lists
            fm = re.sub(r'^\s+-\s+@\s*$', '', fm, flags=re.MULTILINE)
            fm = re.sub(r"'@'", '', fm)
            fm = re.sub(r'"@"', '', fm)
            # Remove empty list items
            fm = re.sub(r'\[\s*,', '[', fm)
            fm = re.sub(r',\s*\]', ']', fm)
            fm = re.sub(r'\[\s*\]', '', fm)
            # Fix missing closing quotes on MSC-like codes
            fm = re.sub(r'"(\d{2}-00)\b(?!"|\')', r'"\1"', fm)
            # Remove lines that only contain empty msc_secondary
            fm = re.sub(r'^msc_secondary:\s*$', '', fm, flags=re.MULTILINE)
            # Clean blank lines
            fm = re.sub(r'\n{3,}', '\n\n', fm)
            new_content = '---' + fm + rest
        
        if new_content != content:
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write(new_content)
            fixed += 1

print(f'Total fixes: {fixed}')
