import os, re

base = r'G:\_src\FormalMath\docs'

# Map course to silver doc paths
course_docs = {}
for root, _, files in os.walk(base):
    for f in files:
        if not f.endswith('.md'): continue
        path = os.path.join(root, f)
        with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
            content = fh.read()
        if 'silver' not in content.lower(): continue
        rel = os.path.relpath(path, base)
        # Detect course
        m = re.search(r'course:\s*(.+)', content)
        tm = re.search(r'target_courses:\s*\[(.*?)\]', content, re.DOTALL)
        course = None
        if m:
            course = m.group(1).strip().strip('"\'')
        elif tm:
            course = tm.group(1).strip().strip('"\'').split(',')[0].strip().strip('"\'')
        if course and course not in ['', 'project']:
            if course not in course_docs:
                course_docs[course] = []
            course_docs[course].append((rel, f))

# Add cross-reference blocks
for course, docs in course_docs.items():
    if len(docs) < 2:
        continue
    # Build related docs list (exclude self)
    for rel, fname in docs:
        path = os.path.join(base, rel)
        with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
            content = fh.read()
        if '## 相关文档' in content:
            continue
        others = [d for d in docs if d[0] != rel][:5]
        if not others:
            continue
        links = []
        for orel, oname in others:
            # Compute relative link from rel to orel
            rel_dir = os.path.dirname(rel)
            target = os.path.relpath(orel, rel_dir) if rel_dir else orel
            title = os.path.splitext(oname)[0]
            links.append(f'- [{title}]({target})')
        block = '\n\n## 相关文档\n\n' + '\n'.join(links) + '\n'
        # Insert before 参考文献 if exists, else at end
        if '参考文献' in content:
            content = content.replace('参考文献', block.lstrip() + '\n参考文献')
        else:
            content = content.rstrip() + block
        with open(path, 'w', encoding='utf-8') as fh:
            fh.write(content)
        print(f'Added cross-refs: {rel} ({len(others)} links)')

print('Done.')
