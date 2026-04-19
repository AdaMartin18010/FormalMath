import os
import re

dirs = [
    'docs/01-基础数学',
    'docs/02-代数结构',
    'docs/03-分析学',
    'docs/04-几何与拓扑',
    'docs/05-数论',
    'docs/06-概率论与统计',
    'docs/07-数理逻辑',
    'docs/08-计算数学',
]

results = []

for d in dirs:
    if not os.path.exists(d):
        continue
    for root, _, files in os.walk(d):
        for f in files:
            if not f.endswith('.md'):
                continue
            path = os.path.join(root, f)
            try:
                with open(path, 'r', encoding='utf-8') as file:
                    content = file.read()
            except Exception as e:
                continue
            
            text = content
            if text.startswith('---'):
                parts = text.split('---', 2)
                if len(parts) >= 3:
                    text = parts[2]
            
            text_clean = re.sub(r'!\[.*?\]\(.*?\)', '', text)
            text_clean = re.sub(r'\[.*?\]\(.*?\)', '', text_clean)
            text_clean = re.sub(r'[#*`_~>|\-\n\r\t]', '', text_clean)
            text_clean = re.sub(r'\$+.*?\$+', '', text_clean)
            text_clean = re.sub(r'\s+', '', text_clean)
            char_count = len(text_clean)
            
            has_latex = bool(re.search(r'\$\$.+?\$\$', content, re.DOTALL)) or bool(re.search(r'[^\$]\$[^\$]+\$[^\$]', content))
            has_theorem = bool(re.search(r'##?#?\s*(定理|Theorem|命题|Proposition|引理|Lemma|推论|Corollary)', content, re.I))
            has_proof = bool(re.search(r'##?#?\s*(证明|Proof)', content, re.I))
            has_example = bool(re.search(r'##?#?\s*(例子|Example|示例|例题)', content, re.I))
            
            is_empty = char_count < 500 or (not has_theorem and not has_proof and not has_example)
            
            if is_empty:
                results.append({
                    'path': path,
                    'chars': char_count,
                    'latex': has_latex,
                    'theorem': has_theorem,
                    'proof': has_proof,
                    'example': has_example
                })

results.sort(key=lambda x: x['chars'])

print(f'Total empty/light files: {len(results)}')
print()
for r in results:
    flags = []
    if r['latex']: flags.append('L')
    if r['theorem']: flags.append('T')
    if r['proof']: flags.append('P')
    if r['example']: flags.append('E')
    flag_str = ','.join(flags) if flags else 'none'
    print(f"{r['chars']:5d} [{flag_str}] | {r['path']}")
