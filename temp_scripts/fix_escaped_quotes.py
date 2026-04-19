import os

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
        # Fix specific escaped-quote patterns
        new_content = new_content.replace(r'[\"@\", \"@\", \"@\"]', '')
        new_content = new_content.replace(r'[\"@\", \"@\"]', '')
        new_content = new_content.replace(r'[\"@\"]', '')
        # Fix \"XX-YY"" patterns by replacing the exact substring
        # We need to be careful to match exactly
        if r'\"' in new_content:
            # Generic fix: \"text"" -> "text"
            import re
            new_content = re.sub(r'\\"([^"\n]+)""', r'"\1"', new_content)
            new_content = re.sub(r'\\"([^"\n]+)\\"', r'"\1"', new_content)
        
        if new_content != content:
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write(new_content)
            fixed += 1
            print(f'Fixed: {os.path.relpath(path, base)}')

print(f'Total fixes: {fixed}')
