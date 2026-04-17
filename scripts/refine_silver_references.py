#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为重点银层文档补充精确的 chapters / pages。
"""
import yaml
from pathlib import Path

def load_fm(path):
    text = path.read_text(encoding="utf-8")
    if not text.startswith("---"):
        return None, text
    end = text.find("\n---", 3)
    if end == -1:
        return None, text
    return yaml.safe_load(text[3:end]), text[end+4:]

def save_fm(path, data, rest):
    out = "---\n" + yaml.dump(data, allow_unicode=True, sort_keys=False, default_flow_style=False) + "---" + rest
    path.write_text(out, encoding="utf-8")

def update_textbook(tb, info):
    if tb.get("id") == info.get("target_id"):
        if "chapters" in info:
            tb["chapters"] = info["chapters"]
        if "pages" in info:
            tb["pages"] = info["pages"]

# 映射：文件路径 -> (教材id -> {chapters, pages})
REFINEMENTS = {
    # ===== MIT 18.100A 实分析 =====
    "docs/03-分析学/01-实分析/MIT-18.100A/01-确界原理与Archimedean性质.md": {
        "rudin_pma": {"chapters": ["Chapter 1: The Real and Complex Number Systems"], "pages": "1-5"},
    },
    "docs/03-分析学/01-实分析/MIT-18.100A/02-介值定理.md": {
        "rudin_pma": {"chapters": ["Chapter 4: Continuity"], "pages": "85-90"},
    },
    "docs/03-分析学/01-实分析/MIT-18.100A/03-一致连续性.md": {
        "rudin_pma": {"chapters": ["Chapter 4: Continuity"], "pages": "90-91"},
    },
    "docs/03-分析学/01-实分析/MIT-18.100A/04-中值定理.md": {
        "rudin_pma": {"chapters": ["Chapter 5: Differentiation"], "pages": "108-110"},
    },
    "docs/03-分析学/01-实分析/MIT-18.100A/05-比较判别法与比值根值判别法.md": {
        "rudin_pma": {"chapters": ["Chapter 3: Numerical Sequences and Series"], "pages": "65-69"},
    },
    "docs/03-分析学/01-实分析/MIT-18.100A/06-Taylor定理.md": {
        "rudin_pma": {"chapters": ["Chapter 5: Differentiation"], "pages": "110-113"},
    },
    "docs/03-分析学/01-实分析/MIT-18.100A/07-Weierstrass-M-判别法.md": {
        "rudin_pma": {"chapters": ["Chapter 7: Sequences and Series of Functions"], "pages": "148-149"},
    },

    # ===== MIT 18.701 代数 =====
    "docs/02-代数结构/02-核心理论/MIT-18.701/01-拉格朗日定理.md": {
        "artin_algebra": {"chapters": ["Chapter 2: Groups, Section 2.8"], "pages": "55-60"},
        "dummit_foote_aa": {"chapters": ["Chapter 3: Quotient Groups and Homomorphisms, Section 3.2"], "pages": "89-95"},
    },
    "docs/02-代数结构/02-核心理论/MIT-18.701/02-第一同构定理-群论.md": {
        "artin_algebra": {"chapters": ["Chapter 2: Groups, Section 2.12"], "pages": "75-80"},
        "dummit_foote_aa": {"chapters": ["Chapter 3: Quotient Groups and Homomorphisms, Section 3.3"], "pages": "97-103"},
    },
    "docs/02-代数结构/02-核心理论/MIT-18.701/03-Sylow第一定理.md": {
        "artin_algebra": {"chapters": ["Chapter 7: More Group Theory, Section 7.7"], "pages": "205-210"},
        "dummit_foote_aa": {"chapters": ["Chapter 5: Group Actions, Section 5.4 (Sylow Theorems)"], "pages": "139-146"},
    },
    "docs/02-代数结构/02-核心理论/MIT-18.701/04-Cauchy定理.md": {
        "artin_algebra": {"chapters": ["Chapter 7: More Group Theory, Section 7.2"], "pages": "185-190"},
        "dummit_foote_aa": {"chapters": ["Chapter 4: Group Actions, Section 4.1 (Cauchy's Theorem)"], "pages": "93-96"},
    },
    "docs/02-代数结构/02-核心理论/MIT-18.701/05-轨道-稳定子定理.md": {
        "artin_algebra": {"chapters": ["Chapter 6: Symmetry, Section 6.8 (Orbit-Stabilizer)"], "pages": "178-183"},
        "dummit_foote_aa": {"chapters": ["Chapter 4: Group Actions, Section 4.1"], "pages": "112-118"},
    },
    "docs/02-代数结构/02-核心理论/MIT-18.701/06-第一同构定理-环论.md": {
        "artin_algebra": {"chapters": ["Chapter 11: Rings, Section 11.3"], "pages": "338-343"},
        "dummit_foote_aa": {"chapters": ["Chapter 7: Introduction to Rings, Section 7.3 (Ring Homomorphisms)"], "pages": "239-245"},
    },
    "docs/02-代数结构/02-核心理论/MIT-18.701/07-多项式环的欧几里得算法与唯一分解.md": {
        "artin_algebra": {"chapters": ["Chapter 12: Factoring, Section 12.2"], "pages": "367-375"},
        "dummit_foote_aa": {"chapters": ["Chapter 8: Euclidean Domains, Principal Ideal Domains and Unique Factorization Domains, Sections 8.1–8.3"], "pages": "270-292"},
    },

    # ===== MIT 18.06 线性代数 =====
    "docs/02-代数结构/线性代数与矩阵理论/MIT-18.06/07-特征值与特征向量的计算.md": {
        "strang_la": {"chapters": ["Chapter 6: Eigenvalues and Eigenvectors"], "pages": "283-330"},
    },

    # ===== 代数几何 FOAG 银层 =====
    "docs/13-代数几何/习题/AG-VK-016-层的层化与stalk判定正合性.md": {
        "vakil_foag": {"chapters": ["Section 2.4: Sheaves, Section 2.5: Sheaves of abelian groups and O_X-modules"], "pages": "65-72"},
        "hartshorne_ag": {"chapters": ["Chapter II, Section 1: Sheaves"], "pages": "60-69"},
    },
    "docs/13-代数几何/习题/AG-VK-017-仿射概形的结构层与Spec-Γ范畴等价.md": {
        "vakil_foag": {"chapters": ["Section 4.1: The structure sheaf of an affine scheme"], "pages": "125-130"},
        "hartshorne_ag": {"chapters": ["Chapter II, Section 2: Schemes"], "pages": "70-77"},
    },
    "docs/13-代数几何/习题/AG-VK-018-Proj构造与其泛性质.md": {
        "vakil_foag": {"chapters": ["Section 4.5: Proj and projective schemes"], "pages": "145-152"},
        "hartshorne_ag": {"chapters": ["Chapter II, Section 2: Schemes (Proj construction)"], "pages": "76-81"},
    },
    "docs/13-代数几何/习题/AG-VK-019-分离与本征态射的ValuativeCriterion.md": {
        "vakil_foag": {"chapters": ["Section 12.3: Separated morphisms, Section 12.7: The valuative criteria for separatedness and properness"], "pages": "335-345"},
        "hartshorne_ag": {"chapters": ["Chapter II, Section 4: Separated and Proper Morphisms"], "pages": "96-105"},
    },
    "docs/13-代数几何/习题/AG-VK-020-导出函子与Čech-导出上同调等价性.md": {
        "vakil_foag": {"chapters": ["Section 23.3: Derived functors and Čech cohomology"], "pages": "615-625"},
        "hartshorne_ag": {"chapters": ["Chapter III, Section 4: Čech Cohomology"], "pages": "220-225"},
    },
    "docs/13-代数几何/习题/AG-VK-021-曲线的Riemann-Roch定理与计算.md": {
        "vakil_foag": {"chapters": ["Section 19.4: The Riemann-Roch Theorem"], "pages": "505-515"},
        "hartshorne_ag": {"chapters": ["Chapter IV, Section 1: The Riemann-Roch Theorem"], "pages": "295-301"},
    },
    "docs/13-代数几何/习题/AG-VK-022-平坦性光滑性与上同调基变换.md": {
        "vakil_foag": {"chapters": ["Section 24.6: Flatness, Section 25.2: Smooth morphisms, Section 28.1: Base change theorems"], "pages": "655-675"},
        "hartshorne_ag": {"chapters": ["Chapter III, Section 9: Flat Morphisms; Chapter III, Section 10: Smooth Morphisms"], "pages": "253-269"},
    },
    "docs/13-代数几何/FOAG-深化/AG-VK-023-有限态射的整体与局部刻画.md": {
        "vakil_foag": {"chapters": ["Section 7.3: Morphisms of finite type and finite morphisms"], "pages": "195-200"},
        "hartshorne_ag": {"chapters": ["Chapter II, Section 3: First Properties of Schemes (Finite morphisms)"], "pages": "84-88"},
    },
    "docs/13-代数几何/FOAG-深化/AG-VK-024-Weil除子与Cartier除子的等价理论.md": {
        "vakil_foag": {"chapters": ["Section 14.2: Weil divisors and Cartier divisors"], "pages": "385-392"},
        "hartshorne_ag": {"chapters": ["Chapter II, Section 6: Divisors"], "pages": "129-138"},
    },
    "docs/13-代数几何/FOAG-深化/AG-VK-025-线丛与映射到射影空间.md": {
        "vakil_foag": {"chapters": ["Section 15.1: Line bundles and maps to projective space"], "pages": "405-415"},
        "hartshorne_ag": {"chapters": ["Chapter II, Section 7: Projective Morphisms"], "pages": "150-158"},
    },
    "docs/13-代数几何/FOAG-深化/AG-VK-026-Serre对偶定理的完整陈述与应用.md": {
        "vakil_foag": {"chapters": ["Section 30.1: Serre duality"], "pages": "815-825"},
        "hartshorne_ag": {"chapters": ["Chapter III, Section 7: Serre Duality"], "pages": "239-249"},
    },
    "docs/13-代数几何/FOAG-深化/AG-VK-027-爆破的几何与代数.md": {
        "vakil_foag": {"chapters": ["Section 19.4: Blow-ups"], "pages": "525-535"},
        "hartshorne_ag": {"chapters": ["Chapter I, Section 4: Rational Maps; Chapter II, Section 7: Blow-ups"], "pages": "28-32, 158-163"},
    },
    "docs/13-代数几何/FOAG-深化/AG-VK-028-椭圆曲线的群结构.md": {
        "vakil_foag": {"chapters": ["Section 19.9: Elliptic curves are group varieties"], "pages": "555-565"},
        "hartshorne_ag": {"chapters": ["Chapter IV, Section 4: The Elliptic Curve Group Law"], "pages": "321-327"},
    },
    "docs/13-代数几何/Harvard-232br-习题解答/II.5-模与层-续.md": {
        "hartshorne_ag": {"chapters": ["Chapter II, Section 5: Sheaves of Modules"], "pages": "110-118"},
    },
    "docs/13-代数几何/Harvard-232br-习题解答/II.6-除子.md": {
        "hartshorne_ag": {"chapters": ["Chapter II, Section 6: Divisors"], "pages": "129-138"},
    },
    "docs/13-代数几何/FOAG-深化/AG-VK-029-曲线的Hurwitz定理.md": {
        "vakil_foag": {"chapters": ["Section 21.7: The Hurwitz theorem"], "pages": "595-605"},
        "hartshorne_ag": {"chapters": ["Chapter IV, Section 2: Hurwitz's Theorem"], "pages": "301-306"},
    },
    "docs/13-代数几何/Harvard-232br-习题解答/II.7-射影态射.md": {
        "hartshorne_ag": {"chapters": ["Chapter II, Section 7: Projective Morphisms"], "pages": "150-158"},
    },
    "docs/13-代数几何/Harvard-232br-习题解答/II.8-微分形式.md": {
        "hartshorne_ag": {"chapters": ["Chapter II, Section 8: Differentials"], "pages": "172-180"},
    },
}

if __name__ == "__main__":
    for rel_path, updates in REFINEMENTS.items():
        p = Path(rel_path)
        if not p.exists():
            print(f"[跳过] 文件不存在: {p}")
            continue
        data, rest = load_fm(p)
        if data is None:
            print(f"[跳过] 无 frontmatter: {p}")
            continue
        refs = data.get("references", {})
        textbooks = refs.get("textbooks", [])
        modified = False
        for tb in textbooks:
            if not isinstance(tb, dict):
                continue
            tid = tb.get("id")
            if tid in updates:
                info = updates[tid]
                tb["chapters"] = info.get("chapters", [])
                if "pages" in info:
                    tb["pages"] = info["pages"]
                modified = True
        if modified:
            save_fm(p, data, rest)
            print(f"[已精修] {p}")
        else:
            print(f"[未改动] {p}")
