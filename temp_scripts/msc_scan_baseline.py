import os, re

msc_pattern = re.compile(r'^(0\d|[1-9][0-7])([A-Z]\d{2,3})?$')
stats = {'total':0,'with_primary':0,'missing_primary':0,'invalid_primary':0,'invalid_secondary':0,'errors':[],'warnings':[]}

for root, dirs, files in os.walk('G:/_src/FormalMath'):
    if any(x in root for x in ['node_modules','.git','00-归档','99-归档','__pycache__']):
        continue
    for f in files:
        if not f.endswith('.md'):
            continue
        path = os.path.join(root, f)
        stats['total'] += 1
        try:
            with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
                content = fh.read(5000)
        except Exception as e:
            continue
        fm_match = re.match(r'---\s*\n(.*?)\n---', content, re.DOTALL)
        if not fm_match:
            stats['missing_primary'] += 1
            stats['warnings'].append(f'{path}: 缺少front matter')
            continue
        block = fm_match.group(1)
        primary = None
        m = re.search(r'msc_primary:\s*["\']?([^"\'\s\r\n]+)["\']?', block)
        if m:
            primary = m.group(1).strip()
        if not primary:
            stats['missing_primary'] += 1
            stats['warnings'].append(f'{path}: 缺少 msc_primary')
            continue
        stats['with_primary'] += 1
        if not msc_pattern.match(primary):
            stats['invalid_primary'] += 1
            stats['errors'].append(f'{path}: msc_primary 格式非法: {primary}')
        secs = re.findall(r'msc_secondary:\s*\n((?:\s*-\s*["\']?[^"\'\s\r\n]+["\']?\s*\n)+)', block)
        if secs:
            items = re.findall(r'-\s*["\']?([^"\'\s\r\n]+)["\']?', secs[0])
            for s in items:
                if not msc_pattern.match(s):
                    stats['invalid_secondary'] += 1
                    stats['errors'].append(f'{path}: msc_secondary 格式非法: {s}')

print(f"统计: 总文档={stats['total']} 含msc_primary={stats['with_primary']} 缺msc_primary={stats['missing_primary']} 主编码非法={stats['invalid_primary']} 次编码非法={stats['invalid_secondary']}")
print(f"覆盖率: {stats['with_primary']/max(stats['total'],1)*100:.2f}%")
print(f"错误数: {len(stats['errors'])}")
print(f"警告数: {len(stats['warnings'])}")

# Write detailed log
with open('G:/_src/FormalMath/temp_scripts/msc_scan_baseline_20260420.log', 'w', encoding='utf-8') as f:
    f.write(f"MSC Scan Baseline Report\n")
    f.write(f"========================\n")
    f.write(f"Total docs: {stats['total']}\n")
    f.write(f"With msc_primary: {stats['with_primary']}\n")
    f.write(f"Missing msc_primary: {stats['missing_primary']}\n")
    f.write(f"Invalid primary: {stats['invalid_primary']}\n")
    f.write(f"Invalid secondary: {stats['invalid_secondary']}\n")
    f.write(f"Coverage: {stats['with_primary']/max(stats['total'],1)*100:.2f}%\n\n")
    f.write("Errors:\n")
    for e in stats['errors']:
        f.write(f"  {e}\n")
    f.write("\nWarnings (first 100):\n")
    for w in stats['warnings'][:100]:
        f.write(f"  {w}\n")
