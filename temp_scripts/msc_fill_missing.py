import os, re

# Map directory prefixes to MSC primary codes
path_to_msc = {
    'docs/01-基础数学': '00A05',
    'docs/02-代数结构': '08A99',
    'docs/03-分析学': '26A99',
    'docs/04-几何与拓扑': '51A99',
    'docs/05-数论': '11A99',
    'docs/06-概率论与统计': '60A99',
    'docs/07-数理逻辑': '03A99',
    'docs/08-计算数学': '65A99',
    'docs/09-形式化证明': '68V20',
    'docs/10-应用数学': '00A71',
    'docs/11-高级数学': '00A05',
    'docs/12-代数拓扑': '55A99',
    'docs/13-代数几何': '14A99',
    'docs/15-同调代数': '18G99',
    '数学家理念体系': '01A99',
    'concept': '00A05',
    'project': '00A99',
    'tools': '00A99',
    'scripts': '00A99',
    'deploy': '00A99',
    'tests': '97U50',
    'ref': '00A99',
    'research': '00A99',
    'output': '00A99',
    'k8s': '00A99',
    ' FormalMath-Interactive': '00A99',
    ' FormalMath-Enhanced': '00A99',
}

filled = 0
skipped = 0

for root, dirs, files in os.walk('G:/_src/FormalMath'):
    if any(x in root for x in ['node_modules','.git','00-归档','99-归档','__pycache__']):
        continue
    for f in files:
        if not f.endswith('.md'): continue
        path = os.path.join(root, f)
        rel = os.path.relpath(path, 'G:/_src/FormalMath').replace('\\', '/')
        
        try:
            with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
                content = fh.read()
        except: continue
        
        fm_match = re.match(r'^(---\s*\n)(.*?)(\n---\s*\n)', content, re.DOTALL)
        if not fm_match:
            # No front matter at all - skip for now
            skipped += 1
            continue
        
        block = fm_match.group(1) + fm_match.group(2) + fm_match.group(3)
        if 'msc_primary:' in block:
            continue  # Already has msc_primary
        
        # Determine MSC code from path
        msc = '00A99'
        for prefix, code in path_to_msc.items():
            if rel.startswith(prefix):
                msc = code
                break
        
        # Insert msc_primary after title (or at beginning of block)
        new_block = fm_match.group(2)
        if 'title:' in new_block:
            # Insert after title line
            title_match = re.search(r'(title:\s*[^\r\n]+)(\r?\n)', new_block)
            if title_match:
                new_block = new_block[:title_match.end()] + f'msc_primary: {msc}\n' + new_block[title_match.end():]
            else:
                new_block = f'msc_primary: {msc}\n' + new_block
        else:
            new_block = f'msc_primary: {msc}\n' + new_block
        
        new_content = fm_match.group(1) + new_block + fm_match.group(3) + content[fm_match.end():]
        
        try:
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write(new_content)
            filled += 1
        except:
            pass

print(f"MSC fill missing complete: filled={filled}, skipped={skipped}")
