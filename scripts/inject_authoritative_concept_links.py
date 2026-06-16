#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为核心数学概念文档注入权威外部链接（nLab / Wikipedia / Stacks Project / MacTutor）。

仅对标题/文件名匹配到 curated 映射表的文档进行处理，避免误伤报告类文件。

用法：
    python scripts/inject_authoritative_concept_links.py
"""

import yaml
import re
from pathlib import Path
from urllib.parse import quote

PROJECT_ROOT = Path(__file__).resolve().parents[1]


def nlab_url(term: str) -> str:
    slug = term.replace(" ", "+").replace("(", "%28").replace(")", "%29")
    return f"https://ncatlab.org/nlab/show/{slug}"


def wiki_url(term: str) -> str:
    return f"https://en.wikipedia.org/wiki/{term.replace(' ', '_')}"


def stacks_search_url(term: str) -> str:
    return f"https://stacks.math.columbia.edu/search?query={quote(term)}"


def mactutor_url(name: str) -> str:
    # MacTutor 使用姓氏；这里用全名加下划线近似
    return f"https://mathshistory.st-andrews.ac.uk/Biographies/{name.replace(' ', '-')}/"


# curated 映射：关键词 -> (nlab slug, wiki slug)
CONCEPT_LINKS = {
    "集合": ("set", "Set_(mathematics)"),
    "函数": ("function", "Function_(mathematics)"),
    "映射": ("function", "Function_(mathematics)"),
    "群": ("group", "Group_(mathematics)"),
    "环": ("ring", "Ring_(mathematics)"),
    "域": ("field", "Field_(mathematics)"),
    "向量空间": ("vector+space", "Vector_space"),
    "线性映射": ("linear+map", "Linear_map"),
    "矩阵": ("matrix", "Matrix_(mathematics)"),
    "拓扑空间": ("topological+space", "Topological_space"),
    "连续映射": ("continuous+map", "Continuous_function"),
    "紧致": ("compact+space", "Compact_space"),
    "连通": ("connected+space", "Connected_space"),
    "流形": ("manifold", "Manifold"),
    "微分形式": ("differential+form", "Differential_form"),
    "层": ("sheaf", "Sheaf_(mathematics)"),
    "概形": ("scheme", "Scheme_(mathematics)"),
    "态射": ("morphism", "Morphism"),
    "范畴": ("category", "Category_(mathematics)"),
    "函子": ("functor", "Functor"),
    "自然变换": ("natural+transformation", "Natural_transformation"),
    "极限": ("limit", "Limit_(category_theory)"),
    "余极限": ("colimit", "Colimit"),
    "伴随": ("adjunction", "Adjoint_functors"),
    "单子": ("monad", "Monad_(category_theory)"),
    "阿贝尔范畴": ("abelian+category", "Abelian_category"),
    "导出范畴": ("derived+category", "Derived_category"),
    "同调代数": ("homological+algebra", "Homological_algebra"),
    "谱序列": ("spectral+sequence", "Spectral_sequence"),
    "层上同调": ("sheaf+cohomology", "Sheaf_cohomology"),
    "代数几何": ("algebraic+geometry", "Algebraic_geometry"),
    "代数拓扑": ("algebraic+topology", "Algebraic_topology"),
    "同伦论": ("homotopy+theory", "Homotopy_theory"),
    "同伦类型论": ("homotopy+type+theory", "Homotopy_type_theory"),
    "Topos": ("topos", "Topos"),
    "拓扑斯": ("topos", "Topos"),
    "无穷范畴": ("infinity-category", "Infinity-category"),
    "拟范畴": ("quasi-category", "Quasi-category"),
    "模型范畴": ("model+category", "Model_category"),
    "数论": ("number+theory", "Number_theory"),
    "椭圆曲线": ("elliptic+curve", "Elliptic_curve"),
    "模形式": ("modular+form", "Modular_form"),
    "黎曼曲面": ("Riemann+surface", "Riemann_surface"),
    "代数数论": ("algebraic+number+theory", "Algebraic_number_theory"),
    "表示论": ("representation+theory", "Representation_theory"),
    "李群": ("Lie+group", "Lie_group"),
    "李代数": ("Lie+algebra", "Lie_algebra"),
    "微分几何": ("differential+geometry", "Differential_geometry"),
    "黎曼几何": ("Riemannian+geometry", "Riemannian_geometry"),
    "辛几何": ("symplectic+geometry", "Symplectic_geometry"),
    "泛函分析": ("functional+analysis", "Functional_analysis"),
    "偏微分方程": ("partial+differential+equation", "Partial_differential_equation"),
    "概率论": ("probability+theory", "Probability_theory"),
    "数理逻辑": ("mathematical+logic", "Mathematical_logic"),
    "集合论": ("set+theory", "Set_theory"),
    "范畴论": ("category+theory", "Category_theory"),
    "伽罗瓦理论": ("Galois+theory", "Galois_theory"),
    "Galois理论": ("Galois+theory", "Galois_theory"),
    "群论": ("group+theory", "Group_theory"),
    "环论": ("ring+theory", "Ring_theory"),
    "域论": ("field+theory", "Field_theory_(mathematics)"),
    "模": ("module", "Module_(mathematics)"),
    "理想": ("ideal", "Ideal_(ring_theory)"),
    "素理想": ("prime+ideal", "Prime_ideal"),
    "极大理想": ("maximal+ideal", "Maximal_ideal"),
    "同态": ("homomorphism", "Homomorphism"),
    "同构": ("isomorphism", "Isomorphism"),
    "商群": ("quotient+group", "Quotient_group"),
    "正规子群": ("normal+subgroup", "Normal_subgroup"),
    "Sylow": ("Sylow+theorem", "Sylow_theorems"),
    "Cauchy": ("Cauchy+theorem", "Cauchy's_theorem_(group_theory)"),
    "拉格朗日": ("Lagrange+theorem", "Lagrange's_theorem_(group_theory)"),
    "轨道稳定子": ("orbit-stabilizer+theorem", "Orbit-stabilizer_theorem"),
    "中值定理": ("mean+value+theorem", "Mean_value_theorem"),
    "介值定理": ("intermediate+value+theorem", "Intermediate_value_theorem"),
    "Taylor": ("Taylor's+theorem", "Taylor's_theorem"),
    "一致连续": ("uniform+continuity", "Uniform_continuity"),
    "确界": ("supremum", "Infimum_and_supremum"),
    "收敛": ("convergence", "Convergence_(mathematics)"),
    "级数": ("series", "Series_(mathematics)"),
    "赋范线性空间": ("normed+vector+space", "Normed_vector_space"),
    "Banach空间": ("Banach+space", "Banach_space"),
    "Hilbert空间": ("Hilbert+space", "Hilbert_space"),
    "测度": ("measure", "Measure_(mathematics)"),
    "积分": ("integral", "Integral"),
    "勒贝格": ("Lebesgue+measure", "Lebesgue_measure"),
    "微分流形": ("differentiable+manifold", "Differentiable_manifold"),
    "切空间": ("tangent+space", "Tangent_space"),
    "向量丛": ("vector+bundle", "Vector_bundle"),
    "纤维丛": ("fiber+bundle", "Fiber_bundle"),
    "联络": ("connection", "Connection_(mathematics)"),
    "曲率": ("curvature", "Curvature"),
    "上同调": ("cohomology", "Cohomology"),
    "同调": ("homology", "Homology_(mathematics)"),
    "谱": ("spectrum", "Spectrum_(topology)"),
    "层化": ("sheafification", "Sheaf_(mathematics)"),
    "预层": ("presheaf", "Presheaf"),
    "Grothendieck拓扑": ("Grothendieck+topology", "Grothendieck_topology"),
    "下降理论": ("descent", "Descent_(mathematics)"),
}

MATHEMATICIAN_LINKS = {
    "伽罗瓦": ("Evariste_Galois", "Galois"),
    "Galois": ("Evariste_Galois", "Galois"),
    "黎曼": ("Bernhard_Riemann", "Riemann"),
    "Riemann": ("Bernhard_Riemann", "Riemann"),
    "高斯": ("Carl_Friedrich_Gauss", "Gauss"),
    "欧拉": ("Leonhard_Euler", "Euler"),
    "柯西": ("Augustin-Louis_Cauchy", "Cauchy"),
    "阿贝尔": ("Niels_Henrik_Abel", "Abel"),
    "诺特": ("Emmy_Noether", "Noether"),
    "希尔伯特": ("David_Hilbert", "Hilbert"),
    "格罗滕迪克": ("Alexander_Grothendieck", "Grothendieck"),
    "Grothendieck": ("Alexander_Grothendieck", "Grothendieck"),
    "塞尔": ("Jean-Pierre_Serre", "Serre"),
    "Serre": ("Jean-Pierre_Serre", "Serre"),
    "阿蒂亚": ("Michael_Atiyah", "Atiyah"),
    "Atiyah": ("Michael_Atiyah", "Atiyah"),
    "博特": ("Raoul_Bott", "Bott"),
    "Bott": ("Raoul_Bott", "Bott"),
    "陈省身": ("Shiing-Shen_Chern", "Chern"),
    "韦伊": ("Andre_Weil", "Weil"),
    "德林": ("Pierre_Deligne", "Deligne"),
    "丘成桐": ("Shing-Tung_Yau", "Yau"),
    "怀尔斯": ("Andrew_Wiles", "Wiles"),
    "纳什": ("John_Forbes_Nash_Jr", "Nash"),
    "图灵": ("Alan_Turing", "Turing"),
    "冯诺依曼": ("John_von_Neumann", "von-Neumann"),
}


def is_report_like(title: str, stem: str):
    report_markers = ["报告", "进度", "日报", "总结", "计划", "索引", "README", "FAQ", "指南", "模板", "清单"]
    if stem.startswith("00-"):
        return True
    if any(m in title or m in stem for m in report_markers):
        return True
    return False


def parse_frontmatter(text: str):
    if text.startswith("---"):
        end = text.find("---", 3)
        if end != -1:
            fm_text = text[3:end].strip()
            body = text[end + 3 :].strip()
            try:
                return yaml.safe_load(fm_text) or {}, body
            except yaml.YAMLError:
                return None, body
    return {}, text


def lookup_concept_links(title: str, stem: str):
    for key, (nlab_slug, wiki_slug) in CONCEPT_LINKS.items():
        if key in title or key in stem:
            return {"nlab_url": nlab_url(nlab_slug), "wikipedia_url": wiki_url(wiki_slug), "stacks_search_url": stacks_search_url(key)}
    return None


def lookup_mathematician_links(title: str, stem: str):
    for key, (wiki_name, last_name) in MATHEMATICIAN_LINKS.items():
        if key in title or key in stem:
            return {
                "wikipedia_url": wiki_url(wiki_name),
                "mactutor_url": mactutor_url(last_name),
            }
    return None


def process_file(path: Path):
    text = path.read_text(encoding="utf-8", errors="ignore")
    fm, body = parse_frontmatter(text)
    if fm is None:
        return False

    title = fm.get("title", "")
    stem = path.stem
    if is_report_like(title, stem):
        return False

    external_ids = fm.get("external_ids") or {}
    added = {}

    concept = lookup_concept_links(title, stem)
    if concept:
        for k, v in concept.items():
            if not external_ids.get(k):
                external_ids[k] = v
                added[k] = v

    math = lookup_mathematician_links(title, stem)
    if math:
        for k, v in math.items():
            if not external_ids.get(k):
                external_ids[k] = v
                added[k] = v

    if not added:
        return False

    fm["external_ids"] = external_ids
    new_text = (
        "---\n"
        + yaml.safe_dump(fm, allow_unicode=True, sort_keys=False, default_flow_style=False)
        + "---\n"
        + body
    )
    path.write_text(new_text, encoding="utf-8")
    return True


def main():
    changed = 0
    for p in PROJECT_ROOT.rglob("*.md"):
        if any(x in p.parts for x in ("node_modules", ".git", "00-归档", "归档")):
            continue
        if process_file(p):
            changed += 1
    print(f"Injected authoritative links into {changed} docs.")


if __name__ == "__main__":
    main()
