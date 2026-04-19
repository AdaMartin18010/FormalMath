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
        # Remove YAML list items that are just '- @'
        new_content = re.sub(r'^\s+-\s+@\s*$', '', new_content, flags=re.MULTILINE)
        # Remove @ from bracket lists: ['@', '14A15'] -> ['14A15']
        new_content = re.sub(r"'@',\s*", '', new_content)
        new_content = re.sub(r",\s*'@'", '', new_content)
        new_content = re.sub(r'"@",\s*', '', new_content)
        new_content = re.sub(r',\s*"@"', '', new_content)
        # Remove empty msc_secondary lines or lines with just [''] or [""]
        new_content = re.sub(r'^msc_secondary:\s*\[\s*\]\s*$', '', new_content, flags=re.MULTILINE)
        new_content = re.sub(r'^msc_secondary:\s*\[\s*\',\s*"\s*\]\s*$', '', new_content, flags=re.MULTILINE)
        # Clean up duplicate msc_secondary keys if one becomes empty
        # Fix missing closing quotes like "55-00 -> "55-00"
        new_content = re.sub(r'"(\d{2}-00)\s*$', r'"\1"', new_content, flags=re.MULTILINE)
        # Clean consecutive blank lines in frontmatter
        new_content = re.sub(r'\n{3,}', '\n\n', new_content)
        
        if new_content != content:
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write(new_content)
            fixed += 1

print(f'Total fixes: {fixed}')
