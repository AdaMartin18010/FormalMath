import os, re

# Fix remaining wildcards: XXAxx -> XX, XX-XX -> XX
wildcard_primary = re.compile(r'^([0-9]{2})([A-Z]xx|-XX)$')
fixed = 0
skipped = 0

for root, dirs, files in os.walk('G:/_src/FormalMath'):
    if any(x in root for x in ['node_modules','.git','00-归档','99-归档','__pycache__']):
        continue
    for f in files:
        if not f.endswith('.md'): continue
        path = os.path.join(root, f)
        try:
            with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
                content = fh.read()
        except: continue
        fm_match = re.match(r'^(---\s*\n)(.*?)(\n---\s*\n)', content, re.DOTALL)
        if not fm_match: continue
        prefix = fm_match.group(1)
        block = fm_match.group(2)
        suffix = fm_match.group(3)
        rest = content[fm_match.end():]
        
        m = re.search(r'msc_primary:\s*(["\']?[^"\'\s\r\n]+["\']?)', block)
        if not m: continue
        primary_raw = m.group(1)
        primary = primary_raw.strip().strip('"').strip("'")
        
        wm = wildcard_primary.match(primary)
        if not wm:
            skipped += 1
            continue
        
        correct = wm.group(1)
        new_block = block.replace(f'msc_primary: {primary_raw}', f'msc_primary: {correct}')
        sec_match = re.search(r'msc_secondary:\s*\n((?:\s*-\s*["\']?[^"\'\s\r\n]+["\']?\s*\n)+)', block)
        if sec_match:
            existing = re.findall(r'-\s*["\']?([^"\'\s\r\n]+)["\']?', sec_match.group(1))
            if primary not in existing:
                new_secs = [primary] + existing
                new_sec_lines = '\n'.join([f'  - {s}' for s in new_secs])
                new_block = new_block.replace(f'msc_secondary:\n{sec_match.group(1)}', f'msc_secondary:\n{new_sec_lines}\n')
        else:
            new_block = new_block.replace(f'msc_primary: {correct}', f'msc_primary: {correct}\nmsc_secondary:\n  - {primary}')
        
        new_content = prefix + new_block + suffix + rest
        try:
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write(new_content)
            fixed += 1
        except:
            pass

print(f"Wildcard MSC fix: fixed={fixed}, skipped={skipped}")
