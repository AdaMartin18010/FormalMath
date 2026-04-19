import os, re
from collections import Counter

msc_pattern = re.compile(r'^(0\d|[1-9][0-7])([A-Z]\d{2,3})?$')
invalid_primaries = Counter()
invalid_secondaries = Counter()

for root, dirs, files in os.walk('G:/_src/FormalMath'):
    if any(x in root for x in ['node_modules','.git','00-归档','99-归档','__pycache__']):
        continue
    for f in files:
        if not f.endswith('.md'): continue
        path = os.path.join(root, f)
        try:
            with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
                content = fh.read(5000)
        except: continue
        fm_match = re.match(r'---\s*\n(.*?)\n---', content, re.DOTALL)
        if not fm_match: continue
        block = fm_match.group(1)
        m = re.search(r'msc_primary:\s*["\']?([^"\'\s\r\n]+)["\']?', block)
        if m:
            primary = m.group(1).strip()
            if not msc_pattern.match(primary):
                invalid_primaries[primary] += 1
        secs = re.findall(r'msc_secondary:\s*\n((?:\s*-\s*["\']?[^"\'\s\r\n]+["\']?\s*\n)+)', block)
        if secs:
            items = re.findall(r'-\s*["\']?([^"\'\s\r\n]+)["\']?', secs[0])
            for s in items:
                if not msc_pattern.match(s):
                    invalid_secondaries[s] += 1

print('Top 20 invalid msc_primary values:')
for k, v in invalid_primaries.most_common(20):
    print(f'  {k}: {v}')
print('\nTop 20 invalid msc_secondary values:')
for k, v in invalid_secondaries.most_common(20):
    print(f'  {k}: {v}')
