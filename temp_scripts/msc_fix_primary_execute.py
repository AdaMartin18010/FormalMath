import os, re

strict_primary = re.compile(r'^([0-9]{2})(-03)?$')
subcode_pattern = re.compile(r'^([0-9]{2})([A-Z][0-9]{2,3})$')

fixed_count = 0
skipped_count = 0
error_count = 0

for root, dirs, files in os.walk('G:/_src/FormalMath'):
    if any(x in root for x in ['node_modules','.git','00-归档','99-归档','__pycache__']):
        continue
    for f in files:
        if not f.endswith('.md'): continue
        path = os.path.join(root, f)
        try:
            with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
                content = fh.read()
        except Exception as e:
            error_count += 1
            continue
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
        
        if strict_primary.match(primary):
            continue
        
        sm = subcode_pattern.match(primary)
        if not sm:
            skipped_count += 1
            continue
        
        correct_primary = sm.group(1)
        sec_match = re.search(r'msc_secondary:\s*\n((?:\s*-\s*["\']?[^"\'\s\r\n]+["\']?\s*\n)+)', block)
        if sec_match:
            old_secondary_block = sec_match.group(1)
            existing_secs = re.findall(r'-\s*["\']?([^"\'\s\r\n]+)["\']?', old_secondary_block)
        else:
            existing_secs = []
        
        new_secs = existing_secs.copy()
        if primary not in new_secs:
            new_secs.insert(0, primary)
        
        # Reconstruct front matter
        new_block = block.replace(f'msc_primary: {primary_raw}', f'msc_primary: {correct_primary}')
        new_sec_lines = '\n'.join([f'  - {s}' for s in new_secs])
        if sec_match:
            new_block = new_block.replace(f'msc_secondary:\n{sec_match.group(1)}', f'msc_secondary:\n{new_sec_lines}\n')
        else:
            new_block = new_block.replace(f'msc_primary: {correct_primary}', f'msc_primary: {correct_primary}\nmsc_secondary:\n{new_sec_lines}')
        
        new_content = prefix + new_block + suffix + rest
        
        try:
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write(new_content)
            fixed_count += 1
        except Exception as e:
            error_count += 1

print(f"MSC Primary Fix Execution Complete")
print(f"==================================")
print(f"Fixed: {fixed_count}")
print(f"Skipped (truly invalid): {skipped_count}")
print(f"Errors: {error_count}")
