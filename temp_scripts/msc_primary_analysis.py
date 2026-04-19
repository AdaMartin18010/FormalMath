import os, re
from collections import Counter

# Strict MSC2020 primary codes (two digits, or XX-03 for historical)
strict_primary = re.compile(r'^([0-9]{2})(-03)?$')
# What people are actually using in msc_primary
actual_pattern = re.compile(r'^([0-9]{2})([A-Z][0-9]{2,3})?$')

stats = Counter()
primary_values = Counter()
fixable = []

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
        if not m: continue
        primary = m.group(1).strip()
        primary_values[primary] += 1
        if strict_primary.match(primary):
            stats['already_correct'] += 1
        elif actual_pattern.match(primary):
            stats['wrong_format_but_valid_msc'] += 1
            # Extract first two digits as potential correct primary
            correct_primary = primary[:2]
            fixable.append((path, primary, correct_primary))
        else:
            stats['truly_invalid'] += 1

print(f"msc_primary value analysis:")
print(f"  Already correct (XX or XX-03): {stats['already_correct']}")
print(f"  Wrong format but valid MSC subcode used as primary: {stats['wrong_format_but_valid_msc']}")
print(f"  Truly invalid: {stats['truly_invalid']}")
print(f"\nTop 30 msc_primary values:")
for k, v in primary_values.most_common(30):
    status = "OK" if strict_primary.match(k) else ("FIXABLE" if actual_pattern.match(k) else "INVALID")
    print(f"  {k:<12} {v:>6}  [{status}]")

print(f"\nFixable examples (first 10):")
for path, old, new in fixable[:10]:
    print(f"  {old} -> {new}  |  {path}")
