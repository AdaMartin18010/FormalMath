import os
import re
import json
from collections import defaultdict

def generate_stats(root_dir):
    stats = {
        'silver_docs': 0,
        'courses': defaultdict(int),
        'domains': defaultdict(int),
        'theorems': 0,
        'exercises': 0,
        'lean4_refs': 0,
        'review_status': defaultdict(int),
        'msc_codes': defaultdict(int)
    }
    
    for dirpath, dirnames, filenames in os.walk(root_dir):
        if '00-归档' in dirpath:
            continue
        for fname in filenames:
            if not fname.endswith('.md'):
                continue
            fpath = os.path.join(dirpath, fname)
            with open(fpath, 'r', encoding='utf-8') as f:
                content = f.read()
            
            if 'level: silver' not in content and 'level: "silver"' not in content:
                continue
            
            stats['silver_docs'] += 1
            
            # Course
            m = re.search(r'course:\s*"?([^"\n]+?)"?\s*$', content, re.M)
            if m:
                stats['courses'][m.group(1).strip()] += 1
            
            # Review status
            m = re.search(r'review_status:\s*"?(\w+)"?', content)
            if m:
                stats['review_status'][m.group(1)] += 1
            
            # MSC
            m = re.search(r'msc_primary:\s*"?(\d+)"?', content)
            if m:
                stats['msc_codes'][m.group(1)] += 1
            
            # Theorems
            stats['theorems'] += len(re.findall(r'\*\*定理\s*\d*\.?\*\*', content))
            
            # Exercises
            stats['exercises'] += len(re.findall(r'\*\*习题\s*\d*\.?\*\*', content))
            
            # Lean4
            stats['lean4_refs'] += len(re.findall(r'`lean', content))
            stats['lean4_refs'] += len(re.findall(r'\bmathlib\b', content, re.I))
    
    return stats

if __name__ == '__main__':
    s = generate_stats('docs')
    print(json.dumps(s, indent=2, ensure_ascii=False))