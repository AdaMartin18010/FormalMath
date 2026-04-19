import os, re
from collections import Counter

# MSC2020 format: 00-97 for main, XXAxx or XXAxxx for sub
msc_pattern = re.compile(r'^([0-9]{2})([A-Z][0-9]{2,3})?$')
# Also accept internal format like 11-03 (two digits-dash-two digits) as "needs normalization"
internal_pattern = re.compile(r'^([0-9]{2})-([0-9]{2})$')

stats = {'total':0,'with_primary':0,'missing_primary':0,'invalid_primary':0,'invalid_secondary':0,
         'valid_primary':0,'internal_format':0,'valid_secondary':0,'errors':[],'warnings':[]}
invalid_primaries = Counter()
invalid_secondaries = Counter()

for root, dirs, files in os.walk('G:/_src/FormalMath'):
    if any(x in root for x in ['node_modules','.git','00-归档','99-归档','__pycache__']):
        continue
    for f in files:
        if not f.endswith('.md'): continue
        path = os.path.join(root, f)
        stats['total'] += 1
        try:
            with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
                content = fh.read(5000)
        except: continue
        fm_match = re.match(r'---\s*\n(.*?)\n---', content, re.DOTALL)
        if not fm_match:
            stats['missing_primary'] += 1
            stats['warnings'].append(f'{path}: 缺少front matter')
            continue
        block = fm_match.group(1)
        m = re.search(r'msc_primary:\s*["\']?([^"\'\s\r\n]+)["\']?', block)
        if m:
            primary = m.group(1).strip()
        else:
            stats['missing_primary'] += 1
            stats['warnings'].append(f'{path}: 缺少 msc_primary')
            continue
        stats['with_primary'] += 1
        if msc_pattern.match(primary):
            stats['valid_primary'] += 1
        elif internal_pattern.match(primary):
            stats['internal_format'] += 1
        else:
            stats['invalid_primary'] += 1
            invalid_primaries[primary] += 1
            stats['errors'].append(f'{path}: msc_primary 格式非法: {primary}')
        secs = re.findall(r'msc_secondary:\s*\n((?:\s*-\s*["\']?[^"\'\s\r\n]+["\']?\s*\n)+)', block)
        if secs:
            items = re.findall(r'-\s*["\']?([^"\'\s\r\n]+)["\']?', secs[0])
            for s in items:
                if msc_pattern.match(s):
                    stats['valid_secondary'] += 1
                else:
                    stats['invalid_secondary'] += 1
                    invalid_secondaries[s] += 1
                    stats['errors'].append(f'{path}: msc_secondary 格式非法: {s}')

print(f"统计: 总文档={stats['total']}")
print(f"  含msc_primary={stats['with_primary']} ({stats['with_primary']/max(stats['total'],1)*100:.1f}%)")
print(f"  缺msc_primary={stats['missing_primary']} ({stats['missing_primary']/max(stats['total'],1)*100:.1f}%)")
print(f"  合法主编码={stats['valid_primary']}")
print(f"  内部格式(XX-XX)={stats['internal_format']}")
print(f"  非法主编码={stats['invalid_primary']}")
print(f"  合法次编码={stats['valid_secondary']}")
print(f"  非法次编码={stats['invalid_secondary']}")
print(f"\nTop 20 invalid msc_primary:")
for k, v in invalid_primaries.most_common(20):
    print(f'  {k}: {v}')
print(f"\nTop 20 invalid msc_secondary:")
for k, v in invalid_secondaries.most_common(20):
    print(f'  {k}: {v}')

with open('G:/_src/FormalMath/temp_scripts/msc_scan_baseline_v2_20260420.log', 'w', encoding='utf-8') as f:
    f.write(f"MSC Scan Baseline Report v2\n")
    f.write(f"===========================\n")
    f.write(f"Total docs: {stats['total']}\n")
    f.write(f"With msc_primary: {stats['with_primary']} ({stats['with_primary']/max(stats['total'],1)*100:.1f}%)\n")
    f.write(f"Missing msc_primary: {stats['missing_primary']}\n")
    f.write(f"Valid primary: {stats['valid_primary']}\n")
    f.write(f"Internal format (XX-XX): {stats['internal_format']}\n")
    f.write(f"Invalid primary: {stats['invalid_primary']}\n")
    f.write(f"Valid secondary: {stats['valid_secondary']}\n")
    f.write(f"Invalid secondary: {stats['invalid_secondary']}\n")
