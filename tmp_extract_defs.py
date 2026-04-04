import os, re, json

files = [
    'docs/13-代数几何/01-代数几何基础.md',
    'docs/13-代数几何/02-代数几何增强版.md',
    'docs/13-代数几何/03-代数几何深度扩展版.md',
    'docs/13-代数几何/04-层与上同调-深度扩展版.md',
    'docs/13-代数几何/04-除子与线丛的完整理论.md',
    'docs/13-代数几何/05-曲面的相交理论.md',
    'docs/13-代数几何/06-双有理几何基础.md',
    'docs/13-代数几何/06-除子与线丛-深度扩展版.md',
    'docs/13-代数几何/07-曲线理论-深度扩展版.md',
    'docs/13-代数几何/08-阿贝尔簇基础.md',
    'docs/13-代数几何/09-霍奇理论入门.md',
    '数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/00-概形理论-概念总览.md',
    '数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/05-拟凝聚层与凝聚层.md',
    '数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/07-除子与线丛.md',
    '数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/12-微分形式与对偶层.md',
    '数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/16-概形的维数理论.md',
    '数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/17-概形的切空间与切丛.md',
    '数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/25-概形的平坦族与形变理论.md',
    '数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/31-概形的层理论与层范畴.md',
    '数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/01-层上同调基础.md',
    '数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/10-上同调与基变化.md',
    '数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/15-上同调与函子关系.md',
    '数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/17-Cech上同调与层上同调.md',
    '数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/21-上同调与Serre对偶.md',
]

results = {}
for f in files:
    if not os.path.exists(f):
        results[f] = {'exists': False}
        continue
    with open(f, 'r', encoding='utf-8') as file:
        lines = file.readlines()
    defs = []
    for i, line in enumerate(lines):
        if '**定义' in line:
            start = max(0, i-1)
            end = min(len(lines), i+10)
            defs.append(''.join(lines[start:end]).strip())
    results[f] = {'exists': True, 'def_count': len(defs), 'defs': defs}

# print concise summary
for f, data in results.items():
    exists = data.get('exists', False)
    count = data.get('def_count', 0)
    print(f'{f}: exists={exists}, defs={count}')

# Save full results
with open('tmp_extract_defs.json', 'w', encoding='utf-8') as out:
    json.dump(results, out, ensure_ascii=False, indent=2)
print('Saved to tmp_extract_defs.json')
