import os, re

# Patterns for invalid codes that can be auto-fixed
# XX-01, XX-02 etc (not valid MSC, only -03 is valid historical)
dash_pattern = re.compile(r'^([0-9]{2})-(0[12]|[0-9]{2})$')
# XX-XX with uppercase XX (like 14-XX)
dash_xx_pattern = re.compile(r'^([0-9]{2})-XX$')

fixed_count = 0
skipped_count = 0

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
        
        correct = None
        dm = dash_pattern.match(primary)
        if dm:
            correct = dm.group(1)
        else:
            dx = dash_xx_pattern.match(primary)
            if dx:
                correct = dx.group(1)
        
        if not correct:
            skipped_count += 1
            continue
        
        # Reconstruct
        new_block = block.replace(f'msc_primary: {primary_raw}', f'msc_primary: {correct}')
        # Also add old to secondary if not present
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
            fixed_count += 1
        except:
            pass

print(f"Invalid MSC fix complete:")
print(f"  Fixed: {fixed_count}")
print(f"  Skipped (still invalid): {skipped_count}")
