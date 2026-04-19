import os, re

strict_primary = re.compile(r'^([0-9]{2})(-03)?$')
subcode_pattern = re.compile(r'^([0-9]{2})([A-Z][0-9]{2,3})$')

fixes = []
skipped = []

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
        
        if strict_primary.match(primary):
            continue  # Already correct
        
        sm = subcode_pattern.match(primary)
        if not sm:
            skipped.append((path, primary))
            continue
        
        correct_primary = sm.group(1)
        old_secondary_block = ""
        sec_match = re.search(r'msc_secondary:\s*\n((?:\s*-\s*["\']?[^"\'\s\r\n]+["\']?\s*\n)+)', block)
        if sec_match:
            old_secondary_block = sec_match.group(1)
            existing_secs = re.findall(r'-\s*["\']?([^"\'\s\r\n]+)["\']?', old_secondary_block)
        else:
            existing_secs = []
        
        # Build new secondary list
        new_secs = existing_secs.copy()
        if primary not in new_secs:
            new_secs.insert(0, primary)
        
        # Reconstruct front matter
        new_block = block.replace(f'msc_primary: {primary_raw}', f'msc_primary: {correct_primary}')
        new_sec_lines = '\n'.join([f'  - {s}' for s in new_secs])
        if sec_match:
            new_block = new_block.replace(f'msc_secondary:\n{sec_match.group(1)}', f'msc_secondary:\n{new_sec_lines}\n')
        else:
            # Insert msc_secondary after msc_primary line
            new_block = new_block.replace(f'msc_primary: {correct_primary}', f'msc_primary: {correct_primary}\nmsc_secondary:\n{new_sec_lines}')
        
        new_content = prefix + new_block + suffix + rest
        fixes.append((path, primary, correct_primary, existing_secs, new_secs))

print(f"Planned fixes: {len(fixes)}")
print(f"Skipped (truly invalid): {len(skipped)}")
print(f"\nFirst 10 fixes:")
for path, old, new, old_secs, new_secs in fixes[:10]:
    print(f"  {old} -> {new}")
    print(f"    secondary: {old_secs} -> {new_secs}")
    print(f"    file: {os.path.basename(path)}")

# Write fix log
with open('G:/_src/FormalMath/temp_scripts/msc_fix_plan_20260420.log', 'w', encoding='utf-8') as f:
    f.write(f"MSC Primary Fix Plan\n")
    f.write(f"====================\n")
    f.write(f"Total fixes planned: {len(fixes)}\n")
    f.write(f"Skipped (truly invalid): {len(skipped)}\n\n")
    f.write("Fixes:\n")
    for path, old, new, old_secs, new_secs in fixes:
        f.write(f"{path}\n")
        f.write(f"  msc_primary: {old} -> {new}\n")
        f.write(f"  msc_secondary: {old_secs} -> {new_secs}\n\n")
    f.write("Skipped:\n")
    for path, val in skipped:
        f.write(f"{path}: {val}\n")
