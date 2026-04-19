import os
import re
from datetime import datetime

def generate_project_report(root_dir):
    stats = {
        'total_md': 0,
        'silver_docs': 0,
        'mathematical_reviewed': 0,
        'completed': 0,
        'courses': {},
        'theorems': 0,
        'exercises': 0,
        'lean_refs': 0,
        'lean_files': 0
    }
    
    # Count markdown files
    for dirpath, dirnames, filenames in os.walk(root_dir):
        if '00-归档' in dirpath:
            continue
        for fname in filenames:
            if fname.endswith('.md'):
                stats['total_md'] += 1
                fpath = os.path.join(dirpath, fname)
                with open(fpath, 'r', encoding='utf-8') as f:
                    content = f.read()
                
                if 'level: silver' in content or 'level: "silver"' in content:
                    stats['silver_docs'] += 1
                    
                    if 'mathematical_reviewed' in content:
                        stats['mathematical_reviewed'] += 1
                    elif 'completed' in content:
                        stats['completed'] += 1
                    
                    m = re.search(r'course:\s*"?([^"\n]+?)"?\s*$', content, re.M)
                    if m:
                        c = m.group(1).strip()
                        stats['courses'][c] = stats['courses'].get(c, 0) + 1
                    
                    stats['theorems'] += len(re.findall(r'\*\*定理\s*\d*\.?\*\*', content))
                    stats['exercises'] += len(re.findall(r'\*\*习题\s*\d*\.?\*\*', content))
                    stats['lean_refs'] += len(re.findall(r'`lean', content))
    
    # Count Lean4 files
    lean_dir = os.path.join(root_dir, 'docs', '09-形式化证明', 'Lean4', 'FormalMathLean4')
    if os.path.exists(lean_dir):
        stats['lean_files'] = len([f for f in os.listdir(lean_dir) if f.endswith('.lean')])
    
    return stats

if __name__ == '__main__':
    s = generate_project_report('.')
    print(f"FormalMath Project Report - {datetime.now().strftime('%Y-%m-%d')}")
    print(f"=" * 50)
    print(f"Total Markdown files: {s['total_md']}")
    print(f"Silver docs: {s['silver_docs']}")
    print(f"Mathematical reviewed: {s['mathematical_reviewed']}")
    print(f"Completed: {s['completed']}")
    print(f"Theorems: {s['theorems']}")
    print(f"Exercises: {s['exercises']}")
    print(f"Lean4 refs: {s['lean_refs']}")
    print(f"Lean4 files: {s['lean_files']}")
    print(f"Courses: {len(s['courses'])}")
    print(f"=" * 50)
    print("Course distribution:")
    for c, n in sorted(s['courses'].items(), key=lambda x: -x[1]):
        print(f"  {c}: {n}")