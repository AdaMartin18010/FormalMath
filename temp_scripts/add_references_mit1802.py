import os

docs_dir = r'G:\_src\FormalMath\docs\00-银层核心课程\MIT-18.02-多元微积分'

refs_block = '''
---
**参考文献**

1. Strang, G. *Calculus*. Wellesley-Cambridge Press, 1991.
2. Stewart, J. *Multivariable Calculus*. Cengage Learning, 2015.
3. Colley, S. J. *Vector Calculus*. Pearson, 2012.
'''

for f in os.listdir(docs_dir):
    if not f.endswith('.md'): continue
    path = os.path.join(docs_dir, f)
    with open(path, 'r', encoding='utf-8') as fh:
        content = fh.read()
    if '参考文献' in content:
        continue
    # Append references before end or at end
    content = content.rstrip() + refs_block
    with open(path, 'w', encoding='utf-8') as fh:
        fh.write(content)
    print(f'Added refs: {f}')

print('Done.')
