import os, re
from collections import Counter

base = r'G:\_src\FormalMath\docs'
statuses = Counter()
for root, _, files in os.walk(base):
    for f in files:
        if not f.endswith('.md'): continue
        path = os.path.join(root, f)
        with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
            content = fh.read()
        if 'silver' not in content.lower(): continue
        m = re.search(r'review_status:\s*(\S+)', content)
        if m:
            statuses[m.group(1).strip().strip('"\'')] += 1
        else:
            statuses['missing'] += 1

print('Review status distribution:')
for s, c in statuses.most_common():
    print(f'  {s}: {c}')
