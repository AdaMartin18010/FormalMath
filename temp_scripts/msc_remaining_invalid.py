import os, re

strict = re.compile(r'^([0-9]{2})(-03)?$')
invalid = []
for root, dirs, files in os.walk('G:/_src/FormalMath'):
    if any(x in root for x in ['node_modules','.git','00-归档','99-归档','__pycache__']):
        continue
    for f in files:
        if not f.endswith('.md'): continue
        path = os.path.join(root, f)
        try:
            with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
                content = fh.read(2000)
        except: continue
        m = re.search(r'msc_primary:\s*["\']?([^"\'\s\r\n]+)["\']?', content)
        if not m: continue
        val = m.group(1).strip()
        if not strict.match(val):
            invalid.append((path, val))

print(f'Remaining invalid msc_primary count: {len(invalid)}')
print('Top 30:')
for path, val in invalid[:30]:
    print(f'  {val:<15} {os.path.basename(path)}')

with open('G:/_src/FormalMath/temp_scripts/msc_remaining_invalid_list.log', 'w', encoding='utf-8') as f:
    f.write(f'Remaining Invalid MSC Primary Codes\n')
    f.write(f'====================================\n')
    f.write(f'Total: {len(invalid)}\n\n')
    for path, val in invalid:
        f.write(f'{val:<15} {path}\n')
