#!/usr/bin/env python3
"""最终统计脚本"""
import os
import yaml
import re

stats = {
    'total': 0,
    'has_frontmatter': 0,
    'no_frontmatter': 0,
    'valid_frontmatter': 0,
    'invalid_frontmatter': 0,
    'field_stats': {
        'title': 0,
        'msc_primary': 0,
        'msc_secondary': 0,
        'processed_at': 0
    }
}

for dirpath, dirnames, filenames in os.walk('.'):
    if '.git' in dirpath or 'node_modules' in dirpath or '__pycache__' in dirpath:
        continue
    for f in filenames:
        if f.endswith('.md'):
            stats['total'] += 1
            filepath = os.path.join(dirpath, f)
            try:
                with open(filepath, 'r', encoding='utf-8') as file:
                    content = file.read()
                    if content.startswith('---'):
                        stats['has_frontmatter'] += 1
                        match = re.search(r'^---\s*\n(.*?)\n---', content, re.DOTALL)
                        if match:
                            try:
                                data = yaml.safe_load(match.group(1))
                                if data:
                                    valid = True
                                    for field in ['title', 'msc_primary', 'processed_at']:
                                        if field in data and data[field]:
                                            stats['field_stats'][field] += 1
                                        else:
                                            valid = False
                                    if 'msc_secondary' in data and data['msc_secondary']:
                                        stats['field_stats']['msc_secondary'] += 1
                                    if valid:
                                        stats['valid_frontmatter'] += 1
                                    else:
                                        stats['invalid_frontmatter'] += 1
                            except Exception as e:
                                stats['invalid_frontmatter'] += 1
                    else:
                        stats['no_frontmatter'] += 1
            except Exception as e:
                pass

print('=== 最终统计 ===')
print(f'Total files: {stats["total"]}')
print(f'Has Frontmatter: {stats["has_frontmatter"]}')
print(f'No Frontmatter: {stats["no_frontmatter"]}')
print(f'Valid Frontmatter: {stats["valid_frontmatter"]}')
print(f'Invalid Frontmatter: {stats["invalid_frontmatter"]}')
print()
print('Field coverage:')
for field, count in stats['field_stats'].items():
    pct = count/stats['total']*100 if stats['total'] > 0 else 0
    print(f'  {field}: {count} ({pct:.1f}%)')
