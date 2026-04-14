import json
from pathlib import Path

JSON_PATH = Path("e:/_src/FormalMath/tools/lean_stats.json")
README_PATH = Path("e:/_src/FormalMath/docs/09-形式化证明/Lean4/README.md")
OVERVIEW_PATH = Path("e:/_src/FormalMath/docs/09-形式化证明/Lean4/00-定理形式化状态总览.md")
LEAN_REPO_URL = "https://github.com/formalmath/formalmath/tree/main/FormalMath-Enhanced/lean4/FormalMath/FormalMath"
MATHLIB_DOCS = "https://leanprover-community.github.io/mathlib4_docs/"

def mathlib_search_link(keyword):
    if not keyword:
        return f"[{MATHLIB_DOCS}]({MATHLIB_DOCS})"
    # Just return a generic docs link with tooltip
    return f"[搜索 `{keyword}`]({MATHLIB_DOCS})"

def category_label(cat):
    if cat == "A":
        return "✅ 完整形式化示例"
    elif cat == "B":
        return "⚠️ 部分证明（含 sorry）"
    else:
        return "📖 定理陈述与概念解释（建议参考Mathlib4官方实现）"

def main():
    with open(JSON_PATH, "r", encoding="utf-8") as f:
        data = json.load(f)
    
    # Sort by category A->B->C, then domain, then filename
    cat_order = {"A": 0, "B": 1, "C": 2}
    data.sort(key=lambda x: (cat_order[x["category"]], x["domain"], x["filename"]))
    
    # Build README content
    readme_lines = [
        "---",
        "msc_primary: 68V20",
        "msc_secondary:",
        "- 03B35",
        "- 03B70",
        "title: FormalMath - Mathlib4对齐形式化证明库",
        "processed_at: '2026-04-05'",
        "---",
        "msc_primary: \"68V20\"",
        "msc_secondary: [\"03B35\", \"03B70\"]",
        "---",
        "",
        "# FormalMath - Mathlib4对齐形式化证明库",
        "",
        "## 项目定位声明",
        "",
        "> **重要说明**：本项目的Lean4代码定位为**\"示例与概念解释\"**，而非一个完整的数学形式化库。",
        "> 我们采取\"战略性放弃\"策略：保留少量完整证明作为学习示例，其余高级定理转为引用Mathlib4现有定理的中文解释。",
        "> 如果您需要可直接编译的完整形式化库，请参考 [Mathlib4 官方文档](https://leanprover-community.github.io/mathlib4_docs/)。",
        "",
        "## 概述",
        "",
        "本目录包含FormalMath项目与Mathlib4对齐的核心定理形式化证明（及概念解释）。",
        "所有代码使用Lean 4编写，与Mathlib 4.19.0版本对齐。",
        "",
        "## Lean4文件形式化状态总览",
        "",
        "| 文件名 | 领域 | 定理数 | sorry数 | 分类 | 状态说明 | Mathlib4对应/搜索关键词 |",
        "|--------|------|--------|---------|------|----------|------------------------|",
    ]
    
    for item in data:
        file = item["file"]
        filename = item["filename"]
        domain = item["domain"]
        thm_cnt = item["theorem_count"]
        sorry_cnt = item["sorry_count"]
        cat = item["category"]
        label = category_label(cat)
        refs = item["mathlib_refs"]
        keywords = ", ".join(refs) if refs else "Mathlib " + filename.replace(".lean", "")
        # Build mathlib link
        mathlib_link = f"[搜索]({MATHLIB_DOCS}) (`{keywords}`)"
        readme_lines.append(f"| `{filename}` | {domain} | {thm_cnt} | {sorry_cnt} | {cat} | {label} | {mathlib_link} |")
    
    readme_lines.extend([
        "",
        "### 分类说明",
        "",
        "- **A类（✅ 完整形式化示例）**：sorry 数量为 0 或极少（<10%），可直接作为学习参考。",
        "- **B类（⚠️ 部分证明）**：含有 sorry，但证明框架较完整（10%-50%），可用于理解证明结构。",
        "- **C类（📖 定理陈述与概念解释）**：sorry 占绝大多数（>50%）或仅有声明，建议结合Mathlib4官方实现阅读。",
        "",
        "## 50个核心定理",
        "",
        "以下表格列出项目早期关注的50个核心定理（部分状态已根据实际代码更新）：",
        "",
        "| # | 定理名称 | Mathlib4对应 | 文件名 | 领域 | 状态 |",
        "|---|----------|--------------|--------|------|------|",
    ])
    
    # We keep the original 50-core table but update statuses based on our data where possible.
    core_theorems = [
        ("1", "拉格朗日定理", "`Subgroup.index_mul_card`", "LagrangeTheorem.lean", "代数结构"),
        ("2", "第一同构定理", "`MonoidHom.quotientKerEquivRange`", "FirstIsomorphismTheorem.lean", "代数结构"),
        ("3", "唯一分解定理", "`UniqueFactorizationMonoid`", "UniqueFactorization.lean", "代数结构"),
        ("4", "Cayley定理", "`Cayley.embedding`", "CayleyTheorem.lean", "代数结构"),
        ("5", "Sylow第一定理", "`Sylow.exists_subgroup_card_pow_prime`", "SylowFirstTheorem.lean", "代数结构"),
        ("6", "中值定理", "`exists_hasDerivAt_eq_slope`", "MeanValueTheorem.lean", "分析学"),
        ("7", "Bolzano-Weierstrass定理", "`BolzanoWeierstrass.tendsto_subseq`", "BolzanoWeierstrass.lean", "分析学"),
        ("8", "介值定理", "`intermediate_value_Icc`", "IntermediateValueTheorem.lean", "分析学"),
        ("9", "Heine-Borel定理", "`isCompact_iff_isClosed_bounded`", "HeineBorel.lean", "分析学"),
        ("10", "费马小定理", "`ZMod.pow_card`", "FermatLittleTheorem.lean", "数论"),
        ("11", "欧几里得算法", "`Nat.gcd_comm`, `EuclideanDomain`", "EuclideanAlgorithm.lean", "数论"),
        ("12", "素数无穷多", "`Nat.infinite_setOf_prime`", "InfinitudeOfPrimes.lean", "数论"),
        ("13", "康托尔定理", "`Cardinal.cantor`", "CantorDiagonal.lean", "集合论"),
        ("14", "鸽巢原理", "`Fintype.exists_ne_map_eq_of_card_lt`", "PigeonholePrinciple.lean", "组合数学"),
        ("15", "无穷鸽巢原理", "`infinite_pigeonhole`", "InfinitePigeonhole.lean", "集合论"),
        ("16", "二次互反律", "`legendreSym.quadratic_reciprocity`", "QuadraticReciprocity.lean", "数论"),
        ("17", "威尔逊定理", "`Nat.wilsons_lemma`", "WilsonTheorem.lean", "数论"),
        ("18", "柯西-施瓦茨不等式", "`norm_inner_le_norm`", "CauchySchwarz.lean", "泛函分析"),
        ("19", "凯莱-哈密顿定理", "`Matrix.aeval_self_charpoly`", "CayleyHamilton.lean", "线性代数"),
        ("20", "阿廷-韦德伯恩定理", "`IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite`", "ArtinWedderburn.lean", "环论"),
        ("21", "隐函数定理", "`HasStrictFDerivAt.implicitFunction`", "ImplicitFunctionTheorem.lean", "分析学"),
        ("22", "逆函数定理", "`HasStrictFDerivAt.to_localInverse`", "InverseFunctionTheorem.lean", "分析学"),
        ("23", "斯托克斯定理", "发展中", "StokesTheorem.lean", "微分几何"),
        ("24", "乌雷松引理", "`exists_continuous_zero_one_of_isClosed`", "UrysohnsLemma.lean", "拓扑学"),
        ("25", "蒂茨扩张定理", "`BoundedContinuousFunction.exists_extension`", "TietzeExtension.lean", "拓扑学"),
        ("26", "一阶逻辑完备性定理", "`isSatisfiable_iff_all_finite_subsets_isSatisfiable`", "CompletenessTheorem.lean", "数理逻辑"),
        ("27", "拉姆齐定理", "发展中", "RamseyTheorem.lean", "组合数学"),
        ("28", "霍尔婚配定理", "`Finset.all_card_le_biUnion_card_iff_exists_injective`", "HallsMarriageTheorem.lean", "组合数学"),
        ("29", "高斯-博内定理", "发展中", "GaussBonnet.lean", "微分几何"),
        ("30", "Faltings定理", "发展中", "FaltingsTheorem.lean", "算术几何"),
        ("31", "中国剩余定理", "`ZMod.chineseRemainder`", "ChineseRemainderTheorem.lean", "代数结构"),
        ("32", "原根存在定理", "`IsPrimitiveRoot`", "PrimitiveRootTheorem.lean", "数论"),
        ("33", "希尔伯特基定理", "`Polynomial.isNoetherianRing`", "HilbertBasisTheorem.lean", "代数结构"),
        ("34", "Hilbert零点定理", "`Ideal.isVanishingIdeal`", "Nullstellensatz.lean", "代数几何"),
        ("35", "Picard-Lindelöf定理", "ODE存在唯一性框架", "PicardLindelof.lean", "微分方程"),
        ("36", "Fourier级数收敛", "`hasSum_fourier_series`", "FourierSeriesConvergence.lean", "调和分析"),
        ("37", "Green定理", "多元积分框架", "GreenTheorem.lean", "多元微积分"),
        ("38", "散度定理", "流形积分框架", "DivergenceTheorem.lean", "多元微积分"),
        ("39", "Morse理论基本定理", "`IsMorseFunction`", "MorseTheory.lean", "微分拓扑"),
        ("40", "毛球定理", "`EulerCharacteristic`", "HairyBallTheorem.lean", "代数拓扑"),
        ("41", "Sard定理", "光滑映射框架", "SardTheorem.lean", "微分拓扑"),
        ("42", "Zorn引理", "`zorn_nonempty`", "ZornLemma.lean", "集合论"),
        ("43", "良序定理", "`wellOrderingTheorem`", "WellOrderingTheorem.lean", "集合论"),
        ("44", "Atiyah-Singer指标定理", "占位/框架", "AtiyahSingerIndex.lean", "全局分析"),
        ("45", "Poincaré猜想（3维）", "Perelman证明概述", "PoincareConjecture3D.lean", "几何拓扑"),
    ]
    
    file_to_cat = {item["filename"]: item["category"] for item in data}
    
    for num, name, mathlib, fname, domain in core_theorems:
        cat = file_to_cat.get(fname, "C")
        if cat == "A":
            status = "✅ 完成"
        elif cat == "B":
            status = "⚠️ 部分"
        else:
            # Some were originally placeholders
            if fname in ["StokesTheorem.lean", "RamseyTheorem.lean", "GaussBonnet.lean", "FaltingsTheorem.lean", "AtiyahSingerIndex.lean", "PoincareConjecture3D.lean", "CompletenessTheorem.lean", "MorseTheory.lean", "SardTheorem.lean"]:
                status = "📖 概念解释"
            else:
                status = "📖 概念解释"
        readme_lines.append(f"| {num} | {name} | {mathlib} | `{fname}` | {domain} | {status} |")
    
    # Append the rest of the original README (priority categories, usage guide, etc.)
    # For brevity, we include a condensed version.
    readme_lines.extend([
        "",
        "## 优先级分类（历史规划）",
        "",
        "> 以下分类反映了项目早期的规划重点。当前实际代码状态请参见上方的\"Lean4文件形式化状态总览\"表格。",
        "",
        "### P0级（基础代数）",
        "",
        "- `LagrangeTheorem.lean` - 群论基础",
        "- `FirstIsomorphismTheorem.lean` - 同态基本定理",
        "- `UniqueFactorization.lean` - 环论基础",
        "- `CayleyTheorem.lean` - 群的置换表示",
        "- `SylowFirstTheorem.lean` - 有限群分类基础",
        "- `ArtinWedderburn.lean` - 半单环分类",
        "- `ChineseRemainderTheorem.lean` - 模算术",
        "- `HilbertBasisTheorem.lean` - Noetherian环论",
        "- `PrimitiveRootTheorem.lean` - 乘法群结构",
        "",
        "### P1级（分析与拓扑）",
        "",
        "- `MeanValueTheorem.lean` - 微积分核心",
        "- `BolzanoWeierstrass.lean` - 实分析基础",
        "- `IntermediateValueTheorem.lean` - 连续性核心",
        "- `HeineBorel.lean` - 紧致性理论",
        "- `BrouwerFixedPoint.lean` - 拓扑学应用",
        "- `Compactness.lean` - 拓扑基础",
        "- `ImplicitFunctionTheorem.lean` - 隐函数存在性",
        "- `InverseFunctionTheorem.lean` - 局部可逆性",
        "- `UrysohnsLemma.lean` - 正规空间刻画",
        "- `TietzeExtension.lean` - 连续函数扩张",
        "- `PicardLindelof.lean` - ODE存在唯一性",
        "- `FourierSeriesConvergence.lean` - 调和分析",
        "- `GreenTheorem.lean` - 多元微积分",
        "- `DivergenceTheorem.lean` - 向量分析",
        "",
        "### P2级（数论与逻辑）",
        "",
        "- `FermatLittleTheorem.lean` - 初等数论",
        "- `EuclideanAlgorithm.lean` - 算法数论",
        "- `InfinitudeOfPrimes.lean` - 素数理论",
        "- `QuadraticReciprocity.lean` - 二次互反律",
        "- `WilsonTheorem.lean` - 威尔逊定理",
        "- `CantorDiagonal.lean` - 集合论",
        "- `PigeonholePrinciple.lean` - 组合数学",
        "- `InfinitePigeonhole.lean` - 无穷组合",
        "- `HallsMarriageTheorem.lean` - 二分图匹配",
        "- `RamseyTheorem.lean` - Ramsey理论",
        "- `FundamentalTheoremAlgebra.lean` - 代数与分析",
        "- `GodelIncompleteness.lean` - 数理逻辑",
        "- `CompletenessTheorem.lean` - 一阶逻辑完备性",
        "- `ZornLemma.lean` - 选择公理等价形式",
        "- `WellOrderingTheorem.lean` - 集合论基础",
        "",
        "### P3级（微分几何与拓扑）",
        "",
        "- `StokesTheorem.lean` - 微分几何统一定理",
        "- `GaussBonnet.lean` - 曲率与拓扑",
        "- `Nullstellensatz.lean` - 代数几何基础",
        "- `MorseTheory.lean` - 临界点理论",
        "- `HairyBallTheorem.lean` - 代数拓扑",
        "- `SardTheorem.lean` - 微分拓扑",
        "",
        "### P4级（前沿/挑战）",
        "",
        "- `FaltingsTheorem.lean` - Mordell猜想",
        "- `AtiyahSingerIndex.lean` - 指标理论（框架）",
        "- `PoincareConjecture3D.lean` - 几何拓扑（框架）",
        "",
        "## 使用指南",
        "",
        "### 环境要求",
        "",
        "```bash",
        "# Lean 4 版本要求",
        "lean --version  # 需要 ≥ 4.19.0",
        "",
        "# 安装依赖",
        "lake update mathlib",
        "```",
        "",
        "## 编译代码",
        "",
        "```bash",
        "# 在Lean4目录下",
        "lake build",
        "",
        "# 检查所有文件",
        "lean *.lean",
        "```",
        "",
        "## 导入模块",
        "",
        "```lean",
        "import docs.形式化证明.Lean4.LagrangeTheorem",
        "import docs.形式化证明.Lean4.FirstIsomorphismTheorem",
        "```",
        "",
        "## 代码结构",
        "",
        "每个定理文件包含：",
        "",
        "1. **Mathlib4对应说明** - 定理的Mathlib4位置和对应关系",
        "2. **数学背景** - 定理的数学意义和历史",
        "3. **形式化定义** - 核心概念的形式化",
        "4. **主定理证明** - 完整的Lean4证明（A类）或证明框架（B/C类）",
        "5. **应用示例** - 定理的具体应用",
        "",
        "```",
        "theorem_file.lean",
        "├── 导入语句 (import)",
        "├── 命名空间定义 (namespace)",
        "├── 核心概念 (definitions)",
        "├── 辅助引理 (lemmas)",
        "├── 主定理证明 (main theorem)",
        "└── 应用示例 (examples)",
        "```",
        "",
        "## 与Mathlib4的对齐策略",
        "",
        "### 1. 直接引用",
        "",
        "对于Mathlib4中已完整实现的定理，直接引用：",
        "",
        "```lean",
        "theorem my_theorem : ... := by",
        "  exact Mathlib4.theorem_name",
        "```",
        "",
        "### 2. 补充证明",
        "",
        "对于Mathlib4中有定义但缺少特定视角的证明，补充证明：",
        "",
        "```lean",
        "theorem alternative_proof : ... := by",
        "  -- 不同的证明方法",
        "```",
        "",
        "### 3. 教学版本",
        "",
        "为教学目的提供更详细的证明版本：",
        "",
        "```lean",
        "theorem detailed_proof : ... := by",
        "  -- 分步详细注释",
        "```",
        "",
        "## 定理依赖关系",
        "",
        "```",
        "基础层:",
        "├── PigeonholePrinciple.lean",
        "├── InfinitePigeonhole.lean",
        "└── EuclideanAlgorithm.lean",
        "",
        "代数层:",
        "├── LagrangeTheorem.lean",
        "│   └── (使用) PigeonholePrinciple",
        "├── FirstIsomorphismTheorem.lean",
        "│   └── (使用) LagrangeTheorem",
        "├── CayleyTheorem.lean",
        "│   └── (使用) LagrangeTheorem",
        "└── SylowFirstTheorem.lean",
        "    └── (使用) LagrangeTheorem",
        "",
        "分析层:",
        "├── MeanValueTheorem.lean",
        "├── BolzanoWeierstrass.lean",
        "├── IntermediateValueTheorem.lean",
        "└── HeineBorel.lean",
        "    └── (使用) BolzanoWeierstrass",
        "",
        "数论层:",
        "├── FermatLittleTheorem.lean",
        "│   └── (使用) LagrangeTheorem",
        "├── InfinitudeOfPrimes.lean",
        "└── UniqueFactorization.lean",
        "    └── (使用) EuclideanAlgorithm",
        "",
        "集合论层:",
        "├── CantorDiagonal.lean",
        "└── (与所有层关联)",
        "```",
        "",
        "## 扩展计划",
        "",
        "### 近期（2026年Q2）",
        "",
        "- [x] 补充更多群论定理（Cayley定理、Sylow定理）",
        "- [x] 完善环论内容（欧几里得算法、素数无穷多）",
        "- [x] 添加分析学基础（Bolzano-Weierstrass、介值定理）",
        "- [ ] 添加线性代数基础（秩-零化度定理、谱定理）",
        "",
        "### 中期（2026年Q3-Q4）",
        "",
        "- [ ] 建立更完整的分析学分支（一致连续性、Riemann积分）",
        "- [ ] 完善拓扑学内容（连通性、道路连通性）",
        "- [ ] 添加测度论基础",
        "- [ ] 添加复分析基础（Cauchy积分公式）",
        "",
        "### 长期（2027年）",
        "",
        "- [x] 代数几何初步（Hilbert零点定理）✅ 2026年4月",
        "- [ ] 同调代数（长正合序列、导出函子）",
        "- [ ] 范畴论应用（伴随函子、极限）",
        "- [ ] 泛函分析基础（Hahn-Banach定理）",
        "- [ ] 全指标定理形式化（长期目标）",
        "- [ ] Ricci流理论（长期目标）",
        "",
        "## 贡献指南",
        "",
        "### 添加新定理",
        "",
        "1. 在对应优先级目录下创建`.lean`文件",
        "2. 按照模板填写Mathlib4对应信息",
        "3. 提供完整的Lean4证明（针对A类示例）或清晰的概念解释框架（针对C类）",
        "4. 添加数学背景和应用示例",
        "5. 更新本README",
        "",
        "### 代码规范",
        "",
        "- 使用4空格缩进",
        "- 遵循Mathlib4命名约定",
        "- 添加详细的注释说明",
        "- 包含完整的导入语句",
        "- 每个定理包含Mathlib4对应关系注释",
        "",
        "## 参考文献",
        "",
        "### Mathlib4资源",
        "",
        "- [Mathlib4文档](https://leanprover-community.github.io/mathlib4_docs/)",
        "- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)",
        "- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)",
        "",
        "### 数学参考",
        "",
        "- Dummit, D. S., & Foote, R. M. *Abstract Algebra*",
        "- Munkres, J. *Topology*",
        "- Rudin, W. *Principles of Mathematical Analysis*",
        "- Hardy, G. H., & Wright, E. M. *An Introduction to the Theory of Numbers*",
        "- Boolos, G., et al. *Computability and Logic*",
        "",
        "## 维护信息",
        "",
        "- **最后更新**: 2026年4月15日",
        "- **Mathlib4版本**: 4.19.0",
        "- **Lean版本**: 4.19.0",
        "- **维护者**: FormalMath项目团队",
        "- **定理数量**: 168个Lean文件（A类11个 / B类7个 / C类150个）",
        "",
        "## 许可证",
        "",
        "本目录下的代码遵循与Mathlib4相同的许可证（Apache 2.0）。",
        "",
        "---",
        "",
        "**FormalMath项目**: 建立与Mathlib4紧密对齐的形式化数学知识体系",
    ])
    
    with open(README_PATH, "w", encoding="utf-8") as f:
        f.write("\n".join(readme_lines) + "\n")
    
    # Build 00-定理形式化状态总览.md
    overview_lines = [
        "# Lean4 定理形式化状态总览",
        "",
        "> 本文档由脚本自动生成，基于 `FormalMath-Enhanced/lean4/FormalMath/FormalMath/` 目录下所有 `.lean` 文件的统计结果。",
        "",
        "## 统计摘要",
        "",
        f"- **总文件数**: {len(data)} 个",
        f"- **A类（完整证明）**: {sum(1 for x in data if x['category']=='A')} 个",
        f"- **B类（部分证明）**: {sum(1 for x in data if x['category']=='B')} 个",
        f"- **C类（定理陈述/概念解释）**: {sum(1 for x in data if x['category']=='C')} 个",
        "",
        "## 按分类排序的定理列表",
        "",
        "| 序号 | 文件名 | 领域 | 主要定理名（前5个） | 定理数 | sorry数 | 分类 | Mathlib4搜索关键词 |",
        "|------|--------|------|---------------------|--------|---------|------|-------------------|",
    ]
    
    idx = 1
    for item in data:
        names = ", ".join(item["theorem_names"][:5])
        refs = ", ".join(item["mathlib_refs"]) if item["mathlib_refs"] else "Mathlib " + item["filename"].replace(".lean", "")
        overview_lines.append(
            f"| {idx} | `{item['filename']}` | {item['domain']} | {names} | {item['theorem_count']} | {item['sorry_count']} | {item['category']} | `{refs}` |"
        )
        idx += 1
    
    overview_lines.extend([
        "",
        "## 分类标准",
        "",
        "- **A类**：sorry 数量为 0 或占定理总数 < 10%。可作为可直接编译学习的完整形式化示例。",
        "- **B类**：sorry 数量占定理总数 10% ~ 50%。证明框架较完整，适合理解证明思路。",
        "- **C类**：sorry 数量占定理总数 > 50%，或仅有定理声明。主要用作概念解释与Mathlib4对应入口，建议读者转至Mathlib4官方文档查阅完整实现。",
        "",
        "## 使用建议",
        "",
        "1. **初学者**: 从 A 类文件入手，如 `CategoryTheory.lean`、`CoveringSpace.lean`、`CurvatureTensor.lean` 等，学习完整的Lean4证明写法。",
        "2. **进阶者**: 阅读 B 类文件，理解证明框架与关键步骤的衔接方式。",
        "3. **研究者**: 通过 C 类文件快速定位 Mathlib4 中已有对应实现的高级定理，利用表格中的搜索关键词在 [Mathlib4 Docs](https://leanprover-community.github.io/mathlib4_docs/) 中查找官方定义。",
        "",
        "---",
        "",
        "*生成时间: 2026-04-15*",
    ])
    
    with open(OVERVIEW_PATH, "w", encoding="utf-8") as f:
        f.write("\n".join(overview_lines) + "\n")
    
    print("README.md and 00-定理形式化状态总览.md generated successfully.")

if __name__ == "__main__":
    main()
