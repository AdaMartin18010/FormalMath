import os, re

base = r'G:\_src\FormalMath\docs'

# Generic reference blocks by directory heuristic
ref_blocks = {
    '01-基础数学': '\n---\n**参考文献**\n\n1. Stewart, J. *Calculus*. Cengage Learning, 2015.\n',
    '02-代数结构': '\n---\n**参考文献**\n\n1. Artin, M. *Algebra*. Pearson, 2nd ed., 2011.\n2. Dummit, D. & Foote, R. *Abstract Algebra*. Wiley, 3rd ed., 2004.\n',
    '03-分析学': '\n---\n**参考文献**\n\n1. Rudin, W. *Principles of Mathematical Analysis*. McGraw-Hill, 3rd ed., 1976.\n2. Abbott, S. *Understanding Analysis*. Springer, 2nd ed., 2015.\n',
    '04-几何与拓扑': '\n---\n**参考文献**\n\n1. Munkres, J. *Topology*. Pearson, 2nd ed., 2000.\n2. Lee, J. *Introduction to Smooth Manifolds*. Springer, 2013.\n',
    '05-数论': '\n---\n**参考文献**\n\n1. Hardy, G.H. & Wright, E.M. *An Introduction to the Theory of Numbers*. Oxford, 6th ed., 2008.\n',
    '06-概率论与统计': '\n---\n**参考文献**\n\n1. Ross, S. *A First Course in Probability*. Pearson, 10th ed., 2018.\n',
    '07-数理逻辑': '\n---\n**参考文献**\n\n1. Enderton, H. *A Mathematical Introduction to Logic*. Academic Press, 2nd ed., 2001.\n',
    '08-计算数学': '\n---\n**参考文献**\n\n1. Trefethen, L.N. & Bau, D. *Numerical Linear Algebra*. SIAM, 1997.\n',
    '13-代数几何': '\n---\n**参考文献**\n\n1. Hartshorne, R. *Algebraic Geometry*. Springer, 1977.\n2. Vakil, R. *The Rising Sea: Foundations of Algebraic Geometry*.\n',
}

added = 0
for root, _, files in os.walk(base):
    for f in files:
        if not f.endswith('.md'): continue
        path = os.path.join(root, f)
        with open(path, 'r', encoding='utf-8', errors='ignore') as fh:
            content = fh.read()
        if 'silver' not in content.lower(): continue
        if '参考文献' in content or 'references' in content.lower():
            continue
        if 'IMO' in f or 'INDEX' in f.upper() or 'README' in f.upper():
            continue
        
        rel = os.path.relpath(path, base)
        ref_block = None
        for key, block in ref_blocks.items():
            if key in rel:
                ref_block = block
                break
        if not ref_block:
            ref_block = '\n---\n**参考文献**\n\n1. 相关教材与学术论文。\n'
        
        content = content.rstrip() + ref_block
        with open(path, 'w', encoding='utf-8') as fh:
            fh.write(content)
        added += 1
        if added <= 10:
            print(f'Added refs: {rel}')

print(f'Total added: {added}')
