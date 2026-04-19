import os, re

def check_md(path):
    with open(path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 去掉frontmatter计算字数
    clean = re.sub(r'^---\s*\n.*?---\s*\n', '', content, flags=re.DOTALL)
    chars = len(clean.strip())
    
    # 检查数学内容
    has_formula = bool(re.search(r'\$\$?[\s\S]*?\$\$', clean)) or bool(re.search(r'\\begin\{equation|align|theorem|proof|lemma|proposition', clean))
    has_theorem = bool(re.search(r'(?:定理|theorem|命题|proposition|引理|lemma|定义|definition|证明|proof)', clean, re.I))
    has_example = bool(re.search(r'(?:例子|example|示例)', clean, re.I))
    
    return {
        'path': path,
        'chars': chars,
        'has_formula': has_formula,
        'has_theorem': has_theorem,
        'has_example': has_example,
        'needs_rewrite': chars < 500 or not (has_formula or has_theorem or has_example)
    }

# visualizations
viz_files = []
for root, dirs, files in os.walk('docs/visualizations'):
    for f in files:
        if f.endswith('.md'):
            viz_files.append(os.path.join(root, f))

results_viz = [check_md(f) for f in viz_files]
results_viz = sorted([r for r in results_viz if r['needs_rewrite']], key=lambda x: x['chars'])

print('=== VISUALIZATIONS ===')
print(f"Total need rewrite: {len(results_viz)}")
for r in results_viz[:30]:
    print(f"{r['chars']:5d} | {r['path']}")

# concept
con_files = []
for root, dirs, files in os.walk('concept'):
    for f in files:
        if f.endswith('.md'):
            con_files.append(os.path.join(root, f))

results_con = [check_md(f) for f in con_files]
results_con = sorted([r for r in results_con if r['needs_rewrite']], key=lambda x: x['chars'])

print('\n=== CONCEPT ===')
print(f"Total need rewrite: {len(results_con)}")
for r in results_con[:30]:
    print(f"{r['chars']:5d} | {r['path']}")
