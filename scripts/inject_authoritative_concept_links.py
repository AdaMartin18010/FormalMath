#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为核心数学概念与数学家文档注入权威外部链接（nLab / Wikipedia / Stacks Project / MacTutor）。

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
    if not term:
        return ""
    slug = term.replace(" ", "+").replace("(", "%28").replace(")", "%29")
    return f"https://ncatlab.org/nlab/show/{slug}"


def wiki_url(term: str) -> str:
    if not term:
        return ""
    return f"https://en.wikipedia.org/wiki/{term.replace(' ', '_')}"


def stacks_search_url(term: str) -> str:
    return f"https://stacks.math.columbia.edu/search?query={quote(term)}"


def mactutor_url(name: str) -> str:
    if not name:
        return ""
    return f"https://mathshistory.st-andrews.ac.uk/Biographies/{name.replace(' ', '-')}/"


# 概念映射：关键词 -> (nlab slug, wiki slug)
# nlab slug 为空时仅注入 Wikipedia 链接
CONCEPT_LINKS = {
    # 基础 / 逻辑 / 集合
    "集合": ("set", "Set_(mathematics)"),
    "函数": ("function", "Function_(mathematics)"),
    "映射": ("function", "Function_(mathematics)"),
    "关系": ("relation", "Relation_(mathematics)"),
    "等价关系": ("equivalence+relation", "Equivalence_relation"),
    "偏序": ("partial+order", "Partially_ordered_set"),
    "全序": ("total+order", "Total_order"),
    "基数": ("cardinal", "Cardinal_number"),
    "序数": ("ordinal", "Ordinal_number"),
    "良序": ("well-order", "Well-order"),
    "超限归纳": ("transfinite+induction", "Transfinite_induction"),
    "数学归纳法": ("mathematical+induction", "Mathematical_induction"),
    "选择公理": ("axiom+of+choice", "Axiom_of_choice"),
    "佐恩引理": ("Zorn's+lemma", "Zorn's_lemma"),
    "连续统假设": ("continuum+hypothesis", "Continuum_hypothesis"),
    "力迫": ("forcing", "Forcing_(mathematics)"),
    "大基数": ("large+cardinal", "Large_cardinal"),
    "可构造宇宙": ("constructible+universe", "Constructible_universe"),
    "描述集合论": ("descriptive+set+theory", "Descriptive_set_theory"),
    "对角线论证": ("diagonal+argument", "Diagonal_argument"),
    "反证法": ("proof+by+contradiction", "Proof_by_contradiction"),
    "构造数学": ("constructive+mathematics", "Constructive_mathematics"),
    "直觉主义": ("intuitionistic+logic", "Intuitionism"),
    "一阶逻辑": ("first-order+logic", "First-order_logic"),
    "模态逻辑": ("modal+logic", "Modal_logic"),
    "证明论": ("proof+theory", "Proof_theory"),
    "模型论": ("model+theory", "Model_theory"),
    "可计算性": ("computability", "Computability_theory"),
    "递归论": ("computability", "Computability_theory"),
    "丘奇-图灵": ("Church-Turing+thesis", "Church%E2%80%93Turing_thesis"),
    "λ演算": ("lambda-calculus", "Lambda_calculus"),
    "类型论": ("type+theory", "Type_theory"),
    "集合论": ("set+theory", "Set_theory"),
    "数理逻辑": ("mathematical+logic", "Mathematical_logic"),
    # 代数
    "群": ("group", "Group_(mathematics)"),
    "环": ("ring", "Ring_(mathematics)"),
    "域": ("field", "Field_(mathematics)"),
    "模": ("module", "Module_(mathematics)"),
    "代数": ("algebra", "Algebra_(ring_theory)"),
    "李代数": ("Lie+algebra", "Lie_algebra"),
    "李群": ("Lie+group", "Lie_group"),
    "交换代数": ("commutative+algebra", "Commutative_algebra"),
    "群论": ("group+theory", "Group_theory"),
    "环论": ("ring+theory", "Ring_theory"),
    "域论": ("field+theory", "Field_theory_(mathematics)"),
    "表示论": ("representation+theory", "Representation_theory"),
    "伽罗瓦理论": ("Galois+theory", "Galois_theory"),
    "Galois理论": ("Galois+theory", "Galois_theory"),
    "理想": ("ideal", "Ideal_(ring_theory)"),
    "素理想": ("prime+ideal", "Prime_ideal"),
    "极大理想": ("maximal+ideal", "Maximal_ideal"),
    "主理想": ("principal+ideal", "Principal_ideal"),
    "同态": ("homomorphism", "Homomorphism"),
    "同构": ("isomorphism", "Isomorphism"),
    "自同构": ("automorphism", "Automorphism"),
    "商群": ("quotient+group", "Quotient_group"),
    "正规子群": ("normal+subgroup", "Normal_subgroup"),
    "群作用": ("group+action", "Group_action"),
    "Sylow": ("Sylow+theorem", "Sylow_theorems"),
    "Cauchy": ("Cauchy+theorem", "Cauchy's_theorem_(group_theory)"),
    "拉格朗日": ("Lagrange+theorem", "Lagrange's_theorem_(group_theory)"),
    "轨道稳定子": ("orbit-stabilizer+theorem", "Orbit-stabilizer_theorem"),
    "阿贝尔群": ("abelian+group", "Abelian_group"),
    "自由群": ("free+group", "Free_group"),
    "有限群": ("finite+group", "Finite_group"),
    "单群": ("simple+group", "Simple_group"),
    "群表示": ("group+representation", "Group_representation"),
    "特征标": ("character", "Character_theory"),
    "范畴": ("category", "Category_(mathematics)"),
    "范畴论": ("category+theory", "Category_theory"),
    "函子": ("functor", "Functor"),
    "自然变换": ("natural+transformation", "Natural_transformation"),
    "极限": ("limit", "Limit_(category_theory)"),
    "余极限": ("colimit", "Colimit"),
    "伴随": ("adjunction", "Adjoint_functors"),
    "单子": ("monad", "Monad_(category_theory)"),
    "阿贝尔范畴": ("abelian+category", "Abelian_category"),
    "三角范畴": ("triangulated+category", "Triangulated_category"),
    "导出范畴": ("derived+category", "Derived_category"),
    "同调代数": ("homological+algebra", "Homological_algebra"),
    "谱序列": ("spectral+sequence", "Spectral_sequence"),
    "K-理论": ("K-theory", "K-theory"),
    "代数K理论": ("algebraic+K-theory", "Algebraic_K-theory"),
    # 数论
    "数论": ("number+theory", "Number_theory"),
    "代数数论": ("algebraic+number+theory", "Algebraic_number_theory"),
    "解析数论": ("analytic+number+theory", "Analytic_number_theory"),
    "超越数论": ("transcendental+number+theory", "Transcendental_number_theory"),
    "椭圆曲线": ("elliptic+curve", "Elliptic_curve"),
    "模形式": ("modular+form", "Modular_form"),
    "丢番图方程": ("Diophantine+equation", "Diophantine_equation"),
    "二次互反律": ("quadratic+reciprocity", "Quadratic_reciprocity"),
    "素数定理": ("prime+number+theorem", "Prime_number_theorem"),
    "黎曼ζ函数": ("Riemann+zeta+function", "Riemann_zeta_function"),
    "狄利克雷特征": ("Dirichlet+character", "Dirichlet_character"),
    "狄利克雷定理": ("Dirichlet's+theorem", "Dirichlet's_theorem_on_arithmetic_progressions"),
    "分圆域": ("cyclotomic+field", "Cyclotomic_field"),
    "类域论": ("class+field+theory", "Class_field_theory"),
    "岩泽理论": ("Iwasawa+theory", "Iwasawa_theory"),
    "p进数": ("p-adic+number", "P-adic_number"),
    "p进Langlands": ("p-adic+Langlands+program", "P-adic_Langlands_program"),
    "莫德尔-韦伊": ("Mordell-Weil+theorem", "Mordell%E2%80%93Weil_theorem"),
    "BSD": ("Birch-Swinnerton-Dyer+conjecture", "Birch_and_Swinnerton-Dyer_conjecture"),
    "费马大定理": ("Fermat's+last+theorem", "Fermat's_Last_Theorem"),
    "谷山-志村": ("Taniyama-Shimura+conjecture", "Modularity_theorem"),
    "朗兰兹纲领": ("Langlands+program", "Langlands_program"),
    # 代数几何
    "代数几何": ("algebraic+geometry", "Algebraic_geometry"),
    "概形": ("scheme", "Scheme_(mathematics)"),
    "态射": ("morphism", "Morphism"),
    "层": ("sheaf", "Sheaf_(mathematics)"),
    "预层": ("presheaf", "Presheaf"),
    "层化": ("sheafification", "Sheaf_(mathematics)"),
    "凝聚层": ("coherent+sheaf", "Coherent_sheaf"),
    "层上同调": ("sheaf+cohomology", "Sheaf_cohomology"),
    "黎曼-罗赫": ("Riemann-Roch+theorem", "Riemann%E2%80%93Roch_theorem"),
    "Serre对偶": ("Serre+duality", "Serre_duality"),
    "小平消没": ("Kodaira+vanishing+theorem", "Kodaira_vanishing_theorem"),
    "霍奇猜想": ("Hodge+conjecture", "Hodge_conjecture"),
    "霍奇理论": ("Hodge+theory", "Hodge_theory"),
    "霍奇结构": ("Hodge+structure", "Hodge_structure"),
    " motive": ("motive", "Motive_(algebraic_geometry)"),
    "代数曲线": ("algebraic+curve", "Algebraic_curve"),
    "代数曲面": ("algebraic+surface", "Algebraic_surface"),
    "阿贝尔簇": ("abelian+variety", "Abelian_variety"),
    "雅可比簇": ("Jacobian+variety", "Jacobian_variety"),
    "皮卡簇": ("Picard+variety", "Picard_variety"),
    "卡拉比-丘": ("Calabi-Yau+manifold", "Calabi%E2%80%93Yau_manifold"),
    "凯勒流形": ("Kähler+manifold", "Kähler_manifold"),
    "复流形": ("complex+manifold", "Complex_manifold"),
    "复几何": ("complex+geometry", "Complex_geometry"),
    "双有理几何": ("birational+geometry", "Birational_geometry"),
    "模空间": ("moduli+space", "Moduli_space"),
    "相交理论": ("intersection+theory", "Intersection_theory"),
    "下降理论": ("descent", "Descent_(mathematics)"),
    "Grothendieck拓扑": ("Grothendieck+topology", "Grothendieck_topology"),
    "Topos": ("topos", "Topos"),
    "拓扑斯": ("topos", "Topos"),
    # 拓扑 / 几何
    "拓扑空间": ("topological+space", "Topological_space"),
    "连续映射": ("continuous+map", "Continuous_function"),
    "紧致": ("compact+space", "Compact_space"),
    "连通": ("connected+space", "Connected_space"),
    "道路连通": ("path+connected+space", "Connected_space"),
    "Hausdorff": ("Hausdorff+space", "Hausdorff_space"),
    "度量空间": ("metric+space", "Metric_space"),
    "一致空间": ("uniform+space", "Uniform_space"),
    "流形": ("manifold", "Manifold"),
    "微分流形": ("differentiable+manifold", "Differentiable_manifold"),
    "光滑流形": ("smooth+manifold", "Differentiable_manifold"),
    "向量丛": ("vector+bundle", "Vector_bundle"),
    "纤维丛": ("fiber+bundle", "Fiber_bundle"),
    "切空间": ("tangent+space", "Tangent_space"),
    "余切空间": ("cotangent+space", "Cotangent_space"),
    "张量": ("tensor", "Tensor"),
    "微分形式": ("differential+form", "Differential_form"),
    "德拉姆上同调": ("de+Rham+cohomology", "De_Rham_cohomology"),
    "庞加莱对偶": ("Poincaré+duality", "Poincar%C3%A9_duality"),
    "同伦": ("homotopy", "Homotopy"),
    "同伦群": ("homotopy+group", "Homotopy_group"),
    "同伦论": ("homotopy+theory", "Homotopy_theory"),
    "同调": ("homology", "Homology_(mathematics)"),
    "上同调": ("cohomology", "Cohomology"),
    "奇异同调": ("singular+homology", "Singular_homology"),
    "胞腔同调": ("cellular+homology", "Cellular_homology"),
    "代数拓扑": ("algebraic+topology", "Algebraic_topology"),
    "微分拓扑": ("differential+topology", "Differential_topology"),
    "微分几何": ("differential+geometry", "Differential_geometry"),
    "黎曼几何": ("Riemannian+geometry", "Riemannian_geometry"),
    "黎曼度量": ("Riemannian+metric", "Riemannian_metric"),
    "黎曼面": ("Riemann+surface", "Riemann_surface"),
    "黎曼曲面": ("Riemann+surface", "Riemann_surface"),
    "辛几何": ("symplectic+geometry", "Symplectic_geometry"),
    "辛流形": ("symplectic+manifold", "Symplectic_manifold"),
    "联络": ("connection", "Connection_(mathematics)"),
    "曲率": ("curvature", "Curvature"),
    "测地线": ("geodesic", "Geodesic"),
    "示性类": ("characteristic+class", "Characteristic_class"),
    "陈类": ("Chern+class", "Chern_class"),
    "配边": ("cobordism", "Cobordism"),
    "纽结": ("knot", "Knot_(mathematics)"),
    "链环": ("link", "Link_(knot_theory)"),
    "辫群": ("braid+group", "Braid_group"),
    "三维流形": ("3-manifold", "3-manifold"),
    "四维流形": ("4-manifold", "4-manifold"),
    "莫尔斯理论": ("Morse+theory", "Morse_theory"),
    "谱": ("spectrum", "Spectrum_(topology)"),
    "无穷范畴": ("infinity-category", "Infinity-category"),
    "拟范畴": ("quasi-category", "Quasi-category"),
    "模型范畴": ("model+category", "Model_category"),
    "同伦类型论": ("homotopy+type+theory", "Homotopy_type_theory"),
    # 分析
    "数学分析": ("analysis", "Mathematical_analysis"),
    "实分析": ("real+analysis", "Real_analysis"),
    "复分析": ("complex+analysis", "Complex_analysis"),
    "泛函分析": ("functional+analysis", "Functional_analysis"),
    "调和分析": ("harmonic+analysis", "Harmonic_analysis"),
    "傅里叶级数": ("Fourier+series", "Fourier_series"),
    "傅里叶变换": ("Fourier+transform", "Fourier_transform"),
    "拉普拉斯变换": ("Laplace+transform", "Laplace_transform"),
    "小波": ("wavelet", "Wavelet"),
    "中值定理": ("mean+value+theorem", "Mean_value_theorem"),
    "介值定理": ("intermediate+value+theorem", "Intermediate_value_theorem"),
    "Taylor": ("Taylor's+theorem", "Taylor's_theorem"),
    "一致连续": ("uniform+continuity", "Uniform_continuity"),
    "确界": ("supremum", "Infimum_and_supremum"),
    "收敛": ("convergence", "Convergence_(mathematics)"),
    "级数": ("series", "Series_(mathematics)"),
    "绝对收敛": ("absolute+convergence", "Absolute_convergence"),
    "一致收敛": ("uniform+convergence", "Uniform_convergence"),
    "赋范线性空间": ("normed+vector+space", "Normed_vector_space"),
    "Banach空间": ("Banach+space", "Banach_space"),
    "Hilbert空间": ("Hilbert+space", "Hilbert_space"),
    "内积空间": ("inner+product+space", "Inner_product_space"),
    "对偶空间": ("dual+space", "Dual_space"),
    "弱收敛": ("weak+convergence", "Weak_convergence_(Hilbert_space)"),
    "算子": ("operator", "Operator_(mathematics)"),
    "紧算子": ("compact+operator", "Compact_operator"),
    "自伴算子": ("self-adjoint+operator", "Self-adjoint_operator"),
    "谱理论": ("spectral+theory", "Spectral_theory"),
    "谱定理": ("spectral+theorem", "Spectral_theorem"),
    "测度": ("measure", "Measure_(mathematics)"),
    "测度论": ("measure+theory", "Measure_(mathematics)"),
    "积分": ("integral", "Integral"),
    "勒贝格": ("Lebesgue+measure", "Lebesgue_measure"),
    "勒贝格积分": ("Lebesgue+integral", "Lebesgue_integral"),
    "分布": ("distribution", "Distribution_(mathematics)"),
    "索伯列夫空间": ("Sobolev+space", "Sobolev_space"),
    "变分法": ("calculus+of+variations", "Calculus_of_variations"),
    "凸分析": ("convex+analysis", "Convex_analysis"),
    # 方程 / 应用数学
    "微分方程": ("differential+equation", "Differential_equation"),
    "常微分方程": ("ordinary+differential+equation", "Ordinary_differential_equation"),
    "偏微分方程": ("partial+differential+equation", "Partial_differential_equation"),
    "动力系统": ("dynamical+system", "Dynamical_system"),
    "遍历理论": ("ergodic+theory", "Ergodic_theory"),
    "混沌": ("chaos", "Chaos_theory"),
    "分形": ("fractal", "Fractal"),
    "数值分析": ("numerical+analysis", "Numerical_analysis"),
    "数值线性代数": ("numerical+linear+algebra", "Numerical_linear_algebra"),
    "有限元": ("finite+element+method", "Finite_element_method"),
    "优化": ("optimization", "Mathematical_optimization"),
    "凸优化": ("convex+optimization", "Convex_optimization"),
    "控制论": ("control+theory", "Control_theory"),
    "最优控制": ("optimal+control", "Optimal_control"),
    # 概率 / 统计 / 信息 / 计算
    "概率论": ("probability+theory", "Probability_theory"),
    "随机过程": ("stochastic+process", "Stochastic_process"),
    "马尔可夫链": ("Markov+chain", "Markov_chain"),
    "鞅": ("martingale", "Martingale_(probability_theory)"),
    "布朗运动": ("Brownian+motion", "Brownian_motion"),
    "大数定律": ("law+of+large+numbers", "Law_of_large_numbers"),
    "中心极限定理": ("central+limit+theorem", "Central_limit_theorem"),
    "随机矩阵": ("random+matrix", "Random_matrix"),
    "大偏差": ("large+deviation", "Large_deviations_theory"),
    "渗流": ("percolation", "Percolation_theory"),
    "统计学": ("statistics", "Statistics"),
    "统计推断": ("statistical+inference", "Statistical_inference"),
    "回归分析": ("regression+analysis", "Regression_analysis"),
    "贝叶斯": ("Bayesian+inference", "Bayesian_inference"),
    "机器学习": ("machine+learning", "Machine_learning"),
    "神经网络": ("neural+network", "Neural_network"),
    "深度学习": ("deep+learning", "Deep_learning"),
    "强化学习": ("reinforcement+learning", "Reinforcement_learning"),
    "算法": ("algorithm", "Algorithm"),
    "数据结构": ("data+structure", "Data_structure"),
    "计算复杂性": ("computational+complexity", "Computational_complexity_theory"),
    "P与NP": ("P+vs+NP", "P_versus_NP_problem"),
    "自动机": ("automata+theory", "Automata_theory"),
    "形式语言": ("formal+language", "Formal_language"),
    "图灵机": ("Turing+machine", "Turing_machine"),
    "信息论": ("information+theory", "Information_theory"),
    "编码理论": ("coding+theory", "Coding_theory"),
    "密码学": ("cryptography", "Cryptography"),
    "量子计算": ("quantum+computation", "Quantum_computing"),
    "量子信息": ("quantum+information", "Quantum_information"),
    "蒙特卡洛": ("Monte+Carlo+method", "Monte_Carlo_method"),
    "快速傅里叶变换": ("fast+Fourier+transform", "Fast_Fourier_transform"),
    # 物理 / 交叉
    "经典力学": ("classical+mechanics", "Classical_mechanics"),
    "哈密顿力学": ("Hamiltonian+mechanics", "Hamiltonian_mechanics"),
    "拉格朗日力学": ("Lagrangian+mechanics", "Lagrangian_mechanics"),
    "辛结构": ("symplectic+structure", "Symplectic_geometry"),
    "诺特定理": ("Noether+theorem", "Noether%27s_theorem"),
    "量子力学": ("quantum+mechanics", "Quantum_mechanics"),
    "量子场论": ("quantum+field+theory", "Quantum_field_theory"),
    "规范场": ("gauge+theory", "Gauge_theory"),
    "杨-米尔斯": ("Yang-Mills+theory", "Yang%E2%80%93Mills_theory"),
    "Yang-Mills": ("Yang-Mills+theory", "Yang%E2%80%93Mills_theory"),
    "标准模型": ("standard+model", "Standard_Model"),
    "广义相对论": ("general+relativity", "General_relativity"),
    "狭义相对论": ("special+relativity", "Special_relativity"),
    "黑洞": ("black+hole", "Black_hole"),
    "引力波": ("gravitational+wave", "Gravitational_wave"),
    "全息原理": ("holographic+principle", "Holographic_principle"),
    "AdS/CFT": ("AdS/CFT+correspondence", "AdS/CFT_correspondence"),
    "弦论": ("string+theory", "String_theory"),
    "超对称": ("supersymmetry", "Supersymmetry"),
    "宇宙学": ("cosmology", "Cosmology"),
    "暗物质": ("dark+matter", "Dark_matter"),
    "暗能量": ("dark+energy", "Dark_energy"),
    "热力学": ("thermodynamics", "Thermodynamics"),
    "统计力学": ("statistical+mechanics", "Statistical_mechanics"),
}

MATHEMATICIAN_LINKS = {
    # 古典
    "欧几里得": ("Euclid", "Euclid"),
    "Euclid": ("Euclid", "Euclid"),
    "阿基米德": ("Archimedes", "Archimedes"),
    "Archimedes": ("Archimedes", "Archimedes"),
    "阿波罗尼奥斯": ("Apollonius_of_Perga", "Apollonius"),
    "丢番图": ("Diophantus", "Diophantus"),
    # 17-18 世纪
    "牛顿": ("Isaac_Newton", "Newton"),
    "Newton": ("Isaac_Newton", "Newton"),
    "莱布尼茨": ("Gottfried_Wilhelm_Leibniz", "Leibniz"),
    "Leibniz": ("Gottfried_Wilhelm_Leibniz", "Leibniz"),
    "欧拉": ("Leonhard_Euler", "Euler"),
    "Euler": ("Leonhard_Euler", "Euler"),
    "拉格朗日": ("Joseph-Louis_Lagrange", "Lagrange"),
    "Lagrange": ("Joseph-Louis_Lagrange", "Lagrange"),
    "拉普拉斯": ("Pierre-Simon_Laplace", "Laplace"),
    "Laplace": ("Pierre-Simon_Laplace", "Laplace"),
    "傅里叶": ("Joseph_Fourier", "Fourier"),
    "Fourier": ("Joseph_Fourier", "Fourier"),
    "高斯": ("Carl_Friedrich_Gauss", "Gauss"),
    "Gauss": ("Carl_Friedrich_Gauss", "Gauss"),
    "勒让德": ("Adrien-Marie_Legendre", "Legendre"),
    "勒让德": ("Adrien-Marie_Legendre", "Legendre"),
    "雅可比": ("Carl_Gustav_Jacob_Jacobi", "Jacobi"),
    "Jacobi": ("Carl_Gustav_Jacob_Jacobi", "Jacobi"),
    "阿贝尔": ("Niels_Henrik_Abel", "Abel"),
    "Abel": ("Niels_Henrik_Abel", "Abel"),
    "伽罗瓦": ("Évariste_Galois", "Galois"),
    "Galois": ("Évariste_Galois", "Galois"),
    "柯西": ("Augustin-Louis_Cauchy", "Cauchy"),
    "Cauchy": ("Augustin-Louis_Cauchy", "Cauchy"),
    "黎曼": ("Bernhard_Riemann", "Riemann"),
    "Riemann": ("Bernhard_Riemann", "Riemann"),
    "魏尔斯特拉斯": ("Karl_Weierstrass", "Weierstrass"),
    "Weierstrass": ("Karl_Weierstrass", "Weierstrass"),
    "康托尔": ("Georg_Cantor", "Cantor"),
    "Cantor": ("Georg_Cantor", "Cantor"),
    "戴德金": ("Richard_Dedekind", "Dedekind"),
    "Dedekind": ("Richard_Dedekind", "Dedekind"),
    "克罗内克": ("Leopold_Kronecker", "Kronecker"),
    "Kronecker": ("Leopold_Kronecker", "Kronecker"),
    "庞加莱": ("Henri_Poincaré", "Poincare"),
    "Poincaré": ("Henri_Poincaré", "Poincare"),
    "庞加莱猜想": ("Henri_Poincaré", "Poincare"),
    "希尔伯特": ("David_Hilbert", "Hilbert"),
    "Hilbert": ("David_Hilbert", "Hilbert"),
    # 20 世纪数学家
    "诺特": ("Emmy_Noether", "Noether"),
    "Noether": ("Emmy_Noether", "Noether"),
    "巴拿赫": ("Stefan_Banach", "Banach"),
    "Banach": ("Stefan_Banach", "Banach"),
    "冯诺依曼": ("John_von_Neumann", "von-Neumann"),
    "von Neumann": ("John_von_Neumann", "von-Neumann"),
    "哥德尔": ("Kurt_Gödel", "Godel"),
    "Gödel": ("Kurt_Gödel", "Godel"),
    "图灵": ("Alan_Turing", "Turing"),
    "Turing": ("Alan_Turing", "Turing"),
    "香农": ("Claude_Shannon", "Shannon"),
    "Shannon": ("Claude_Shannon", "Shannon"),
    "维纳": ("Norbert_Wiener", "Wiener"),
    "Wiener": ("Norbert_Wiener", "Wiener"),
    "柯尔莫哥洛夫": ("Andrey_Kolmogorov", "Kolmogorov"),
    "Kolmogorov": ("Andrey_Kolmogorov", "Kolmogorov"),
    "勒贝格": ("Henri_Lebesgue", "Lebesgue"),
    "Lebesgue": ("Henri_Lebesgue", "Lebesgue"),
    "博雷尔": ("Émile_Borel", "Borel"),
    "Borel": ("Émile_Borel", "Borel"),
    "策梅洛": ("Ernst_Zermelo", "Zermelo"),
    "Zermelo": ("Ernst_Zermelo", "Zermelo"),
    "罗素": ("Bertrand_Russell", "Russell"),
    "Russell": ("Bertrand_Russell", "Russell"),
    "丘奇": ("Alonzo_Church", "Church"),
    "Church": ("Alonzo_Church", "Church"),
    "塔斯基": ("Alfred_Tarski", "Tarski"),
    "Tarski": ("Alfred_Tarski", "Tarski"),
    "外尔": ("Hermann_Weyl", "Weyl"),
    "Weyl": ("Hermann_Weyl", "Weyl"),
    "嘉当": ("Élie_Cartan", "Cartan"),
    "Cartan": ("Élie_Cartan", "Cartan"),
    "韦伊": ("André_Weil", "Weil"),
    "Weil": ("André_Weil", "Weil"),
    "布尔巴基": ("Nicolas_Bourbaki", "Bourbaki"),
    "Bourbaki": ("Nicolas_Bourbaki", "Bourbaki"),
    "格罗滕迪克": ("Alexander_Grothendieck", "Grothendieck"),
    "Grothendieck": ("Alexander_Grothendieck", "Grothendieck"),
    "塞尔": ("Jean-Pierre_Serre", "Serre"),
    "Serre": ("Jean-Pierre_Serre", "Serre"),
    "博特": ("Raoul_Bott", "Bott"),
    "Bott": ("Raoul_Bott", "Bott"),
    "米尔诺": ("John_Milnor", "Milnor"),
    "Milnor": ("John_Milnor", "Milnor"),
    "斯梅尔": ("Stephen_Smale", "Smale"),
    "Smale": ("Stephen_Smale", "Smale"),
    "阿蒂亚": ("Michael_Atiyah", "Atiyah"),
    "Atiyah": ("Michael_Atiyah", "Atiyah"),
    "希策布鲁赫": ("Friedrich_Hirzebruch", "Hirzebruch"),
    "Hirzebruch": ("Friedrich_Hirzebruch", "Hirzebruch"),
    "德利涅": ("Pierre_Deligne", "Deligne"),
    "Deligne": ("Pierre_Deligne", "Deligne"),
    "法尔廷斯": ("Gerd_Faltings", "Faltings"),
    "Faltings": ("Gerd_Faltings", "Faltings"),
    "森重文": ("Shigefumi_Mori", "Mori"),
    "Mori": ("Shigefumi_Mori", "Mori"),
    "唐纳森": ("Simon_Donaldson", "Donaldson"),
    "Donaldson": ("Simon_Donaldson", "Donaldson"),
    "威滕": ("Edward_Witten", "Witten"),
    "Witten": ("Edward_Witten", "Witten"),
    "孔采维奇": ("Maxim_Kontsevich", "Kontsevich"),
    "Kontsevich": ("Maxim_Kontsevich", "Kontsevich"),
    "彼得·舒尔策": ("Peter_Scholze", "Scholze"),
    "Scholze": ("Peter_Scholze", "Scholze"),
    "怀尔斯": ("Andrew_Wiles", "Wiles"),
    "Wiles": ("Andrew_Wiles", "Wiles"),
    "佩雷尔曼": ("Grigori_Perelman", "Perelman"),
    "Perelman": ("Grigori_Perelman", "Perelman"),
    "陈省身": ("Shiing-Shen_Chern", "Chern"),
    "Chern": ("Shiing-Shen_Chern", "Chern"),
    "丘成桐": ("Shing-Tung_Yau", "Yau"),
    "Yau": ("Shing-Tung_Yau", "Yau"),
    "陶哲轩": ("Terence_Tao", "Tao"),
    "Tao": ("Terence_Tao", "Tao"),
    "张益唐": ("Yitang_Zhang", "Zhang_Yitang"),
    "Yitang Zhang": ("Yitang_Zhang", "Zhang_Yitang"),
    "梅纳德": ("James_Maynard_(mathematician)", "Maynard"),
    "Maynard": ("James_Maynard_(mathematician)", "Maynard"),
    "纳什": ("John_Forbes_Nash_Jr.", "Nash"),
    "Nash": ("John_Forbes_Nash_Jr.", "Nash"),
    "维拉尼": ("Cédric_Villani", "Villani"),
    "Villani": ("Cédric_Villani", "Villani"),
    "吴文俊": ("Wen-Tsun_Wu", "Wu"),
    "华罗庚": ("Hua_Loo-Keng", "Hua"),
    "陈景润": ("Chen_Jingrun", "Chen_Jingrun"),
    # 物理学家 / 跨界
    "爱因斯坦": ("Albert_Einstein", "Einstein"),
    "Einstein": ("Albert_Einstein", "Einstein"),
    "普朗克": ("Max_Planck", "Planck"),
    "Planck": ("Max_Planck", "Planck"),
    "玻尔": ("Niels_Bohr", "Bohr"),
    "Bohr": ("Niels_Bohr", "Bohr"),
    "海森堡": ("Werner_Heisenberg", "Heisenberg"),
    "Heisenberg": ("Werner_Heisenberg", "Heisenberg"),
    "薛定谔": ("Erwin_Schrödinger", "Schrodinger"),
    "Schrödinger": ("Erwin_Schrödinger", "Schrodinger"),
    "狄拉克": ("Paul_Dirac", "Dirac"),
    "Dirac": ("Paul_Dirac", "Dirac"),
    "费曼": ("Richard_Feynman", "Feynman"),
    "Feynman": ("Richard_Feynman", "Feynman"),
    "霍金": ("Stephen_Hawking", "Hawking"),
    "Hawking": ("Stephen_Hawking", "Hawking"),
    "彭罗斯": ("Roger_Penrose", "Penrose"),
    "Penrose": ("Roger_Penrose", "Penrose"),
    "杨振宁": ("Chen-Ning_Yang", "Yang"),
    "Yang": ("Chen-Ning_Yang", "Yang"),
    "米尔斯": ("Robert_Mills_(physicist)", "Mills"),
    "Mills": ("Robert_Mills_(physicist)", "Mills"),
    "希格斯": ("Peter_Higgs", "Higgs"),
    "Higgs": ("Peter_Higgs", "Higgs"),
    "温伯格": ("Steven_Weinberg", "Weinberg"),
    "Weinberg": ("Steven_Weinberg", "Weinberg"),
    "格拉肖": ("Sheldon_Glashow", "Glashow"),
    "Glashow": ("Sheldon_Glashow", "Glashow"),
    "特胡夫特": ("Gerard_'t_Hooft", "tHooft"),
    "特·胡夫特": ("Gerard_'t_Hooft", "tHooft"),
    "麦克斯韦": ("James_Clerk_Maxwell", "Maxwell"),
    "Maxwell": ("James_Clerk_Maxwell", "Maxwell"),
    "玻尔兹曼": ("Ludwig_Boltzmann", "Boltzmann"),
    "Boltzmann": ("Ludwig_Boltzmann", "Boltzmann"),
}


def is_report_like(title: str, stem: str):
    report_markers = ["报告", "进度", "日报", "总结", "计划", "索引", "README", "FAQ", "指南", "模板", "清单", "对齐", "课程表", "Syllabus"]
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
            result = {"wikipedia_url": wiki_url(wiki_slug), "stacks_search_url": stacks_search_url(key)}
            if nlab_slug:
                result["nlab_url"] = nlab_url(nlab_slug)
            return result
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
