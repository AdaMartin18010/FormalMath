import os, json

definitions = [
    # Module 0
    ("Affine variety", "docs/13-代数几何/01-代数几何基础.md", "仿射代数簇"),
    ("Projective variety", "docs/13-代数几何/01-代数几何基础.md", "射影代数簇"),
    ("Zariski topology", "docs/13-代数几何/02-代数几何增强版.md", "Zariski拓扑"),
    ("Quasi-projective variety", "docs/13-代数几何/01-代数几何基础.md", "拟射影簇"),
    ("Regular map (morphism of varieties)", "docs/13-代数几何/02-代数几何增强版.md", "正则映射"),
    ("Rational map", "docs/13-代数几何/06-双有理几何基础.md", "有理映射"),
    ("Birational isomorphism", "docs/13-代数几何/06-双有理几何基础.md", "双有理同构"),
    ("Blow-up of a point/subvariety", "docs/13-代数几何/06-双有理几何基础.md", "爆破"),
    ("Krull dimension of a variety", "数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/16-概形的维数理论.md", "Krull维数"),
    ("Zariski tangent space", "数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/17-概形的切空间与切丛.md", "Zariski切空间"),
    ("Smooth (nonsingular) point", "docs/13-代数几何/03-代数几何深度扩展版.md", "光滑点"),
    ("Tangent cone", "docs/13-代数几何/03-代数几何深度扩展版.md", "切锥"),
    ("Hilbert function of a projective variety", "docs/13-代数几何/03-代数几何深度扩展版.md", "Hilbert函数"),
    ("Hilbert polynomial", "docs/13-代数几何/03-代数几何深度扩展版.md", "Hilbert多项式"),
    ("Arithmetic genus", "docs/13-代数几何/07-曲线理论-深度扩展版.md", "算术亏格"),
    ("Weil divisor", "docs/13-代数几何/04-除子与线丛的完整理论.md", "Weil除子"),
    ("Principal divisor", "docs/13-代数几何/04-除子与线丛的完整理论.md", "主除子"),
    ("Linear equivalence of divisors", "docs/13-代数几何/04-除子与线丛的完整理论.md", "线性等价"),
    ("Linear series g^r_d", "docs/13-代数几何/07-曲线理论-深度扩展版.md", "线性系"),
    ("Canonical divisor K_X", "docs/13-代数几何/04-除子与线丛的完整理论.md", "典范除子"),
    ("Picard group Pic(X)", "docs/13-代数几何/06-除子与线丛-深度扩展版.md", "Picard群"),
    # Module 1
    ("Presheaf and sheaf", "docs/13-代数几何/04-层与上同调-深度扩展版.md", "预层"),
    ("Sheaf (Presheaf and sheaf)", "docs/13-代数几何/04-层与上同调-深度扩展版.md", "层"),
    ("Stalk of a sheaf", "docs/13-代数几何/04-层与上同调-深度扩展版.md", "茎"),
    ("Sheafification", "docs/13-代数几何/04-层与上同调-深度扩展版.md", "层化"),
    ("Exact sequences of sheaves", "docs/13-代数几何/04-层与上同调-深度扩展版.md", "正合列"),
    ("Structure sheaf O_X of a scheme", "数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/00-概形理论-概念总览.md", "结构层"),
    ("O_X-Module", "数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/31-概形的层理论与层范畴.md", "O_X模"),
    ("Quasi-coherent sheaf", "数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/05-拟凝聚层与凝聚层.md", "拟凝聚层"),
    ("Coherent sheaf", "数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/05-拟凝聚层与凝聚层.md", "凝聚层"),
    ("Locally free sheaf / vector bundle", "docs/13-代数几何/04-除子与线丛的完整理论.md", "局部自由层"),
    ("Reflexive sheaf", "docs/13-代数几何/04-层与上同调-深度扩展版.md", "自反层"),
    ("Cartier divisor", "docs/13-代数几何/04-除子与线丛的完整理论.md", "Cartier除子"),
    ("Line bundle associated to a Cartier divisor O_X(D)", "数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/07-除子与线丛.md", "线丛"),
    ("Picard group Pic(X) (Module 1)", "docs/13-代数几何/06-除子与线丛-深度扩展版.md", "Picard群"),
    # Module 2
    ("Sheaf cohomology H^i(X, F)", "docs/13-代数几何/04-层与上同调-深度扩展版.md", "层上同调"),
    ("Injective resolution", "数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/01-层上同调基础.md", "内射分解"),
    ("Flasque (flabby) sheaf", "数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/01-层上同调基础.md", "松弛层"),
    ("Acyclic resolution", "数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/01-层上同调基础.md", "无环分解"),
    ("Cech cohomology", "数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/17-Cech上同调与层上同调.md", "Cech上同调"),
    ("Refinement of an open cover", "数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/17-Cech上同调与层上同调.md", "加细"),
    ("Twisting sheaf O_{P^n}(d)", "docs/13-代数几何/04-除子与线丛的完整理论.md", "扭层"),
    ("Higher direct image R^i f_* F", "数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/15-上同调与函子关系.md", "高次正像"),
    ("Flat morphism", "数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/06-平坦性与平滑性.md", "平坦态射"),
    # Module 3
    ("Dualizing sheaf \\omega_X", "数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/12-微分形式与对偶层.md", "对偶化层"),
    ("Trace map H^n(X, \\omega_X) -> k", "数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/21-上同调与Serre对偶.md", "迹映射"),
    ("Euler characteristic \\chi(F)", "docs/13-代数几何/04-层与上同调-深度扩展版.md", "Euler示性数"),
    ("Degree of a line bundle on a curve", "docs/13-代数几何/04-除子与线丛的完整理论.md", "次数"),
    ("Special divisor", "docs/13-代数几何/07-曲线理论-深度扩展版.md", "特殊除子"),
    ("Brill-Noether number", "docs/13-代数几何/07-曲线理论-深度扩展版.md", "Brill-Noether数"),
    ("Jacobian variety J(X)", "docs/13-代数几何/08-阿贝尔簇基础.md", "Jacobian簇"),
    ("Abel-Jacobi map", "docs/13-代数几何/08-阿贝尔簇基础.md", "Abel-Jacobi映射"),
    # Module 4
    ("Intersection pairing on a smooth surface", "docs/13-代数几何/05-曲面的相交理论.md", "相交配对"),
    ("Self-intersection number C^2", "docs/13-代数几何/05-曲面的相交理论.md", "自交数"),
    ("Blow-up of a surface at a point", "docs/13-代数几何/06-双有理几何基础.md", "爆破"),
    ("Exceptional divisor", "docs/13-代数几何/06-双有理几何基础.md", "例外除子"),
    ("Arithmetic genus p_a(S)", "docs/13-代数几何/05-曲面的相交理论.md", "算术亏格"),
    ("Geometric genus p_g(S)", "docs/13-代数几何/05-曲面的相交理论.md", "几何亏格"),
    ("Irregularity q", "docs/13-代数几何/05-曲面的相交理论.md", "不规则性"),
    ("Holomorphic Euler characteristic \\chi(O_S)", "docs/13-代数几何/05-曲面的相交理论.md", "全纯Euler示性数"),
    ("Kodaira dimension \\kappa(S)", "docs/13-代数几何/06-双有理几何基础.md", "Kodaira维数"),
    ("Minimal surface", "docs/13-代数几何/06-双有理几何基础.md", "极小曲面"),
    ("Ruled surface", "docs/13-代数几何/06-双有理几何基础.md", "直纹曲面"),
    ("K3 surface", "docs/13-代数几何/03-代数几何深度扩展版.md", "K3曲面"),
    ("Enriques surface", "docs/13-代数几何/03-代数几何深度扩展版.md", "Enriques曲面"),
    ("Abelian surface", "docs/13-代数几何/08-阿贝尔簇基础.md", "阿贝尔曲面"),
    # Module 5
    ("Hodge decomposition", "docs/13-代数几何/09-霍奇理论入门.md", "Hodge分解"),
    ("Hodge numbers h^{p,q}", "docs/13-代数几何/09-霍奇理论入门.md", "Hodge数"),
    ("Period map", "docs/13-代数几何/09-霍奇理论入门.md", "周期映射"),
    ("Kodaira-Spencer map", "docs/13-代数几何/03-代数几何深度扩展版.md", "Kodaira-Spencer映射"),
    ("Deformation functor", "数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/25-概形的平坦族与形变理论.md", "形变函子"),
    ("First-order deformation", "数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/25-概形的平坦族与形变理论.md", "一阶形变"),
]

results = []
for name, filepath, term in definitions:
    if not os.path.exists(filepath):
        results.append({
            "term_en": name,
            "file": filepath,
            "term_zh": term,
            "found": False,
            "context": "",
            "error": "File not found"
        })
        continue
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    found = False
    contexts = []
    for i, line in enumerate(lines):
        if term in line:
            start = max(0, i-2)
            end = min(len(lines), i+5)
            contexts.append(''.join(lines[start:end]).strip())
            found = True
    results.append({
        "term_en": name,
        "file": filepath,
        "term_zh": term,
        "found": found,
        "contexts": contexts[:3]  # limit to first 3 matches
    })

with open('tmp_check_defs.json', 'w', encoding='utf-8') as f:
    json.dump(results, f, ensure_ascii=False, indent=2)

print(f"Checked {len(definitions)} definitions. Saved to tmp_check_defs.json")
