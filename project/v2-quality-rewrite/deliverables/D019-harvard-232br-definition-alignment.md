
### Module 1: Sheaves and Coherent Sheaves

#### 22. Presheaf and sheaf
- **课程来源**: Module 1 / Sheaf Theory on Varieties and Schemes
- **课程定义**: 预层为反变函子 $\mathcal{F}:\operatorname{Open}(X)^{\mathrm{op}}\to\mathrm{Set}$（或 Abel 群），带限制映射；层额外满足局部性与粘接性。
- **项目对应路径**: `docs/13-代数几何/04-层与上同调-深度扩展版.md`
- **项目中的表述**: **定义 13.4.1** (预层) 与 **定义 13.4.2** (层公理：局部性 + 粘接性) — 与 Hartshorne II.1 完全一致。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

#### 23. Stalk of a sheaf
- **课程来源**: Module 1 / Sheaf Theory on Varieties and Schemes
- **课程定义**: $\mathcal{F}_x=\varinjlim_{U\ni x}\mathcal{F}(U)$。
- **项目对应路径**: `docs/13-代数几何/04-层与上同调-深度扩展版.md`
- **项目中的表述**: 该文档 **未给出** stalk 的显式定义（仅在结构层性质中提及“茎是局部环”）。
- **对齐判定**: 缺失
- **差异分析**: 核心定义缺失。
- **修正建议**: 补充 stalk 的定义及与层化的关系。

#### 24. Sheafification
- **课程来源**: Module 1 / Sheaf Theory on Varieties and Schemes
- **课程定义**: 层化函子 $a:\operatorname{PSh}(X)\to\operatorname{Sh}(X)$，是包含函子的左伴随；$a\mathcal{F}=\mathcal{F}^{++}$。
- **项目对应路径**: `docs/13-代数几何/04-层与上同调-深度扩展版.md`
- **项目中的表述**: **定理 13.4.1** 给出层化函子 $a\dashv i$，并显式构造 $a\mathcal{F}=\mathcal{F}^{++}$。
- **对齐判定**: 严格等价
- **差异分析**: 以定理形式呈现，但数学内容等价。
- **修正建议**: 无需修正。

#### 25. Exact sequences of sheaves
- **课程来源**: Module 1 / Sheaf Theory on Varieties and Schemes
- **课程定义**: 层的序列 $0\to\mathcal{F}'\to\mathcal{F}\to\mathcal{F}''\to 0$ 正合，若在每个 stalk 上正合（或等价地，对每个开集 $U$，截面序列 $0\to\mathcal{F}'(U)\to\mathcal{F}(U)\to\mathcal{F}''(U)$ 左正合且满射在局部成立）。
- **项目对应路径**: `docs/13-代数几何/04-层与上同调-深度扩展版.md`
- **项目中的表述**: 该文档 **未给出** exact sequence of sheaves 的定义块（仅在层上同调定理中使用了短正合列）。
- **对齐判定**: 缺失
- **差异分析**: 核心定义缺失。
- **修正建议**: 补充 exact sequence of sheaves 的定义（stalk 正合或像层 = 核层）。

#### 26. Structure sheaf $\mathcal{O}_X$ of a scheme
- **课程来源**: Module 1 / Sheaf Theory on Varieties and Schemes
- **课程定义**: 概形 $(X,\mathcal{O}_X)$ 的环层，局部同构于仿射概形的结构层；对 $\operatorname{Spec}(A)$，$\mathcal{O}_X(D(f))=A_f$。
- **项目对应路径**: `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/00-概形理论-概念总览.md`
- **项目中的表述**: 该文档为 **概念索引/目录**，仅有表格罗列“结构层”为关键词，**无定义块**。
- **对齐判定**: 缺失
- **差异分析**: 指定路径为空壳引用页。
- **修正建议**: 将路径修正为 `02-仿射概形基础.md` 或 `docs/13-代数几何/02-代数几何增强版.md`，并在该文档中补充结构层的显式定义。

#### 27. $\mathcal{O}_X$-Module
- **课程来源**: Module 1 / Quasi-Coherent and Coherent Sheaves
- **课程定义**: 层 $\mathcal{F}$  equipped with an action $\mathcal{O}_X\otimes\mathcal{F}\to\mathcal{F}$，使得每个 $\mathcal{F}(U)$ 是 $\mathcal{O}_X(U)$-模，且限制映射是模同态。
- **项目对应路径**: `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/31-概形的层理论与层范畴.md`
- **项目中的表述**: ASCII 框图描述：“对每个开集 $U$，$\mathcal{F}(U)$ 是 $\mathcal{O}_X(U)$ 模，限制映射是模同态”。缺少严格的形式化定义（如层作用、模范畴的刻画）。
- **对齐判定**: 近似表述
- **差异分析**: 仅有描述性框图，无严格定义块；缺少 $\mathcal{O}_X$-Module 作为 Abel 层范畴上环对象的模的正式定义。
- **修正建议**: 补充严格的数学定义块，明确 $\mathcal{O}_X$-模层 = 带有 $\mathcal{O}_X$-作用的 Abel 层。

#### 28. Quasi-coherent sheaf
- **课程来源**: Module 1 / Quasi-Coherent and Coherent Sheaves
- **课程定义**: 概形 $X$ 上的 $\mathcal{O}_X$-模层 $\mathcal{F}$，使得对每个仿射开集 $U=\operatorname{Spec}(A)$，$\mathcal{F}|_U\cong\widetilde{M}$（$M$ 为 $A$-模）。
- **项目对应路径**: `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/05-拟凝聚层与凝聚层.md`
- **项目中的表述**: 明确给出：“对每个仿射开集 $U=\operatorname{Spec}(R)$，$\mathcal{F}|_U\cong\widetilde{M}$（$M$ 是 $R$-模）”。在 11.1 中还有局部刻画。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

#### 29. Coherent sheaf
- **课程来源**: Module 1 / Quasi-Coherent and Coherent Sheaves
- **课程定义**: $X$ 为 Noether 概形时，$\mathcal{F}$ 凝聚若 (1) 有限型；(2) 对任意开集 $U$ 和同态 $\phi:\mathcal{O}_X^n|_U\to\mathcal{F}|_U$，$\ker\phi$ 也是有限型的（Hartshorne II.5）。
- **项目对应路径**: `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/05-拟凝聚层与凝聚层.md`
- **项目中的表述**: 文档给出 ASCII 框图：“凝聚条件：有限型（局部有限生成），有限表示（局部有限表示）”。在 11.2 中甚至写“$\mathcal{F}$ 凝聚 $\iff$ 拟凝聚且有限型”，这对一般概形是 **错误的**（只在局部 Noether 概形上成立）。
- **对齐判定**: 近似表述
- **差异分析**: 缺少关键的 kernel 有限型条件；给出的等价命题在数学上不精确（未限定 Noether 条件）。
- **修正建议**: 重写凝聚层定义，补全 Hartshorne II.5 的标准两条：有限型 + kernel 有限型；并注明 Noether 条件。

#### 30. Locally free sheaf / vector bundle
- **课程来源**: Module 1 / Quasi-Coherent and Coherent Sheaves
- **课程定义**: $\mathcal{O}_X$-模层 $\mathcal{E}$，使得存在 $X$ 的 Zariski 开覆盖 $\{U_i\}$ 满足 $\mathcal{E}|_{U_i}\cong\mathcal{O}_{U_i}^{\oplus r}$（$r$ 为秩）。
- **项目对应路径**: `docs/13-代数几何/04-除子与线丛的完整理论.md`
- **项目中的表述**: 文档 **定义 3.1** 仅定义了 **可逆层**（秩 1 局部自由层），未给出一般秩 $r$ 的 locally free sheaf / vector bundle 的定义。
- **对齐判定**: 缺失
- **差异分析**: 核心定义缺失（仅有秩 1 特例）。
- **修正建议**: 补充一般局部自由层/向量丛的定义，并说明与可逆层的关系。

#### 31. Reflexive sheaf
- **课程来源**: Module 1 / Quasi-Coherent and Coherent Sheaves
- **课程定义**: 凝聚层 $\mathcal{F}$ 满足自然映射 $\mathcal{F}\to\mathcal{F}^{\vee\vee}$ 为同构（$\mathcal{F}^\vee=\mathcal{H}om(\mathcal{F},\mathcal{O}_X)$）。
- **项目对应路径**: `docs/13-代数几何/04-层与上同调-深度扩展版.md`
- **项目中的表述**: 该文档中 **不存在** reflexive sheaf 的定义。
- **对齐判定**: 缺失
- **差异分析**: 核心定义缺失。
- **修正建议**: 补充 reflexive sheaf 的定义及与局部自由层、挠自由层的关系。

#### 32. Cartier divisor
- **课程来源**: Module 1 / Divisors and Line Bundles Revisited
- **课程定义**: 等价类 $D=\{(U_i,f_i)\}$，$f_i\in K(X)^*$，且 $f_i/f_j\in\mathcal{O}_X^*(U_i\cap U_j)$。
- **项目对应路径**: `docs/13-代数几何/04-除子与线丛的完整理论.md`
- **项目中的表述**: **定义 2.4** — 与 Hartshorne II.6 完全一致。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

#### 33. Weil divisor
- **课程来源**: Module 1 / Divisors and Line Bundles Revisited
- **课程定义**: 同条目 16。
- **项目对应路径**: `docs/13-代数几何/04-除子与线丛的完整理论.md`
- **项目中的表述**: 同条目 16。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

#### 34. Line bundle associated to a Cartier divisor $\mathcal{O}_X(D)$
- **课程来源**: Module 1 / Divisors and Line Bundles Revisited
- **课程定义**: 对 $D=\{(U_i,f_i)\}$，$\mathcal{O}_X(D)|_{U_i}=f_i^{-1}\cdot\mathcal{O}_{U_i}\subset K(X)$；转移函数为 $f_i/f_j$。
- **项目对应路径**: `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/07-除子与线丛.md`
- **项目中的表述**: 明确给出 $\mathcal{O}_X(D)|_{U_i}=f_i^{-1}\mathcal{O}_{U_i}$，并说明 Cartier 除子类 $ \cong \operatorname{Pic}(X)$。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

#### 35. Picard group $\operatorname{Pic}(X)$
- **课程来源**: Module 1 / Divisors and Line Bundles Revisited
- **课程定义**: 同条目 21。
- **项目对应路径**: `docs/13-代数几何/06-除子与线丛-深度扩展版.md`
- **项目中的表述**: 同条目 21。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

### Module 2: Sheaf Cohomology

#### 36. Sheaf cohomology $H^i(X,\mathcal{F})$
- **课程来源**: Module 2 / Derived Functors and Sheaf Cohomology
- **课程定义**: 全局截面函子 $\Gamma(X,-)$ 的右导出函子：$H^i(X,\mathcal{F})=R^i\Gamma(X,\mathcal{F})$，通过内射分解构造。
- **项目对应路径**: `docs/13-代数几何/04-层与上同调-深度扩展版.md`
- **项目中的表述**: **定义 13.4.6** — 明确给出导出函子构造与内射分解。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

#### 37. Injective resolution
- **课程来源**: Module 2 / Derived Functors and Sheaf Cohomology
- **课程定义**: Abel 层范畴中的内射对象序列 $0\to\mathcal{F}\to\mathcal{I}^0\to\mathcal{I}^1\to\cdots$，正合。
- **项目对应路径**: `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/01-层上同调基础.md`
- **项目中的表述**: 公式中提到 "$I^\bullet$ 是 $\mathcal{F}$ 的内射分解”，但 **未给出** injective object / injective resolution 的显式定义块。
- **对齐判定**: 缺失
- **差异分析**: 仅有符号使用，无定义。
- **修正建议**: 补充 injective resolution 及层范畴有足够内射对象的说明。

#### 38. Flasque (flabby) sheaf
- **课程来源**: Module 2 / Derived Functors and Sheaf Cohomology
- **课程定义**: 层 $\mathcal{F}$ 满足对所有开包含 $V\subseteq U$，限制映射 $\mathcal{F}(U)\to\mathcal{F}(V)$ 是满射。
- **项目对应路径**: `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/01-层上同调基础.md`
- **项目中的表述**: 该文档中 **不存在** flasque sheaf 的定义。
- **对齐判定**: 缺失
- **差异分析**: 核心定义缺失（仅在 `04-层与上同调-深度扩展版.md` 定理 13.4.3 中提及“flabby 层上同调消失”，但无定义）。
- **修正建议**: 补充 flasque sheaf 的定义及其在导出函子理论中的作用。

#### 39. Acyclic resolution
- **课程来源**: Module 2 / Derived Functors and Sheaf Cohomology
- **课程定义**: 层的正合列 $0\to\mathcal{F}\to\mathcal{A}^\bullet$，其中每个 $\mathcal{A}^i$ 是 $\Gamma(X,-)$-acyclic（如 flasque 或软层）。
- **项目对应路径**: `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/01-层上同调基础.md`
- **项目中的表述**: 该文档中 **不存在** acyclic resolution 的定义。
- **对齐判定**: 缺失
- **差异分析**: 核心定义缺失。
- **修正建议**: 补充 acyclic resolution 的定义及用于计算上同调的定理。

#### 40. Čech cohomology $\check{H}^i(\mathcal{U},\mathcal{F})$
- **课程来源**: Module 2 / Čech Cohomology
- **课程定义**: 对开覆盖 $\mathcal{U}=\{U_i\}$，Čech 复形 $C^p(\mathcal{U},\mathcal{F})=\prod_{i_0<\dots<i_p}\mathcal{F}(U_{i_0\dots i_p})$，微分由交错和给出；$\check{H}^p(\mathcal{U},\mathcal{F})=H^p(C^\bullet)$。
- **项目对应路径**: `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/17-Cech上同调与层上同调.md`
- **项目中的表述**: **10.1 Čech上同调的严格构造** 中明确给出复形、微分与上同调的完整公式。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

#### 41. Refinement of an open cover
- **课程来源**: Module 2 / Čech Cohomology
- **课程定义**: 开覆盖 $\mathcal{V}=\{V_j\}$ 是 $\mathcal{U}=\{U_i\}$ 的加细，若存在加细映射 $\lambda:J\to I$ 使得 $V_j\subseteq U_{\lambda(j)}$。
- **项目对应路径**: `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/17-Cech上同调与层上同调.md`
- **项目中的表述**: 文档在公式 8 中提到“$\mathcal{V}$ 加细 $\mathcal{U}$”，但 **未给出** refinement / 加细映射的显式定义块。
- **对齐判定**: 缺失
- **差异分析**: 仅有符号使用。
- **修正建议**: 补充 refinement 的定义及诱导的 Čech 上同调映射。

#### 42. Twisting sheaf $\mathcal{O}_{\mathbb{P}^n}(d)$
- **课程来源**: Module 2 / Cohomology of Coherent Sheaves on Projective Space
- **课程定义**: $\mathcal{O}_{\mathbb{P}^n}(d)=\mathcal{O}_{\mathbb{P}^n}(1)^{\otimes d}$（$d>0$）或其逆（$d<0$），其中 $\mathcal{O}_{\mathbb{P}^n}(1)$ 对应超平面除子的可逆层；亦可定义为齐次坐标环的 $d$ 次分次的层化 $\widetilde{S(d)}$。
- **项目对应路径**: `docs/13-代数几何/04-除子与线丛的完整理论.md`
- **项目中的表述**: 文档在例 4.2、例 9.1 中使用了 $\mathcal{O}(d)$ 记号，并给出 $H^0(\mathbb{P}^1,\mathcal{O}(n))$ 的维数，但 **不存在** twisting sheaf 的显式定义块。
- **对齐判定**: 缺失
- **差异分析**: 仅有符号使用和计算，无定义。
- **修正建议**: 补充 $\mathcal{O}_{\mathbb{P}^n}(d)$ 的严格定义（作为 $S(d)^\sim$ 或转移函数的粘合）。

#### 43. Serre's twisting sheaf
- **课程来源**: Module 2 / Cohomology of Coherent Sheaves on Projective Space
- **课程定义**: 同条目 42（$\mathcal{O}_{\mathbb{P}^n}(1)$）。
- **项目对应路径**: `docs/13-代数几何/04-除子与线丛的完整理论.md`
- **项目中的表述**: 同条目 42。
- **对齐判定**: 缺失
- **差异分析**: 同条目 42。
- **修正建议**: 同条目 42。

#### 44. Higher direct image $R^i f_*\mathcal{F}$
- **课程来源**: Module 2 / Higher Direct Images and Cohomology and Base Change
- **课程定义**: 推前函子 $f_*$ 的右导出函子：$R^i f_*\mathcal{F}=H^i(Rf_*\mathcal{F})=H^i(f_*\mathcal{I}^\bullet)$。
- **项目对应路径**: `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/15-上同调与函子关系.md`
- **项目中的表述**: 公式 1 明确给出 $R^i f_*\mathcal{F}=H^i(Rf_*\mathcal{F})=H^i(f_*I^\bullet)$；10.1 中在导出范畴框架下进一步阐述。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

#### 45. Flat morphism
- **课程来源**: Module 2 / Higher Direct Images and Cohomology and Base Change
- **课程定义**: 概形态射 $f:X\to Y$ 平坦，若对每个 $x\in X$，局部环同态 $\mathcal{O}_{Y,f(x)}\to\mathcal{O}_{X,x}$ 是平坦模同态。
- **项目对应路径**: `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/06-平坦性与平滑性.md`
- **项目中的表述**: 明确给出：“$f$ 平坦，若对任意 $x\in X$，$\mathcal{O}_{Y,f(x)}\to\mathcal{O}_{X,x}$ 平坦”。公式总结中亦有等价表述。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。


### Module 3: Duality and Curves

#### 46. Dualizing sheaf $\omega_X$
- **课程来源**: Module 3 / Serre Duality and the Dualizing Sheaf
- **课程定义**: 对 $n$ 维光滑射影簇，$\omega_X=\bigwedge^n\Omega_{X/k}^1$（Kähler 微分的外积）；更一般地，对 proper Cohen-Macaulay 概形，$\omega_X$ 定义为对偶函子的对偶化层。
- **项目对应路径**: `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/21-上同调与Serre对偶.md`
- **项目中的表述**: 文档定义 $\omega_X=\det(\Omega_{X/k}^1)^*$（即 $n$ 阶 Kähler 微分），并给出 Serre 对偶。文档 **未给出** 一般 proper/CM 概形上的对偶化层定义。
- **对齐判定**: 近似表述
- **差异分析**: 对象域被限制到光滑簇；课程可能（视教材而定）需要更一般的 dualizing sheaf 定义（Hartshorne III.7）。如果课程采用 FOAG 则仅覆盖光滑情形，可视为等价，但严格标准下缺少一般定义。
- **修正建议**: 补充一般概形/Cohen-Macaulay 概形上 dualizing sheaf 的定义（作为对偶复形 $f^!\mathcal{O}_Y$ 的最高非零上同调层）。

#### 47. Trace map
- **课程来源**: Module 3 / Serre Duality and the Dualizing Sheaf
- **课程定义**: 在 Serre 对偶中，迹映射 $\operatorname{Tr}: H^n(X,\omega_X)\to k$ 是同构（$X$ 光滑射影 $n$ 维）。
- **项目对应路径**: `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/21-上同调与Serre对偶.md`
- **项目中的表述**: 文档给出“最高维上同调的同构 $H^n(X,\omega_X)\cong k$”，并提及作为 Serre 对偶的退化形式。但未明确命名为“trace map”。
- **对齐判定**: 近似表述
- **差异分析**: 数学陈述等价，但缺少 trace map 的命名、泛性质及与残差映射的等价性说明。
- **修正建议**: 显式引入 trace map 的名称及其泛性质。

#### 48. Serre duality
- **课程来源**: Module 3 / Serre Duality and the Dualizing Sheaf
- **课程定义**: 对光滑射影簇 $X$，$\dim X=n$，$\mathcal{F}$ 凝聚，存在自然同构 $H^i(X,\mathcal{F})^*\cong H^{n-i}(X,\mathcal{F}^\vee\otimes\omega_X)$。
- **项目对应路径**: `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/21-上同调与Serre对偶.md`
- **项目中的表述**: **定理**: $H^i(X,\mathcal{F})^*\cong H^{n-i}(X,\mathcal{F}^\vee\otimes\omega_X)$。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

#### 49. Riemann–Roch theorem for curves
- **课程来源**: Module 3 / Riemann–Roch for Curves and Applications
- **课程定义**: 对光滑射影曲线 $C$ 上除子 $D$，$h^0(D)-h^1(D)=\deg D+1-g$。
- **项目对应路径**: `docs/13-代数几何/04-除子与线丛的完整理论.md`
- **项目中的表述**: **定理 6.1** — 与标准形式完全一致。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

#### 50. Genus of a smooth projective curve
- **课程来源**: Module 3 / Riemann–Roch for Curves and Applications
- **课程定义**: 光滑射影曲线 $C$ 的亏格 $g=\dim_k H^1(C,\mathcal{O}_C)=\dim_k H^0(C,\omega_C)$。
- **项目对应路径**: `docs/13-代数几何/07-曲线理论-深度扩展版.md`
- **项目中的表述**: 文档在 **定义 13.7.1** 中给出“亏格 $g(C)=h^1(C,\mathcal{O}_C)=h^0(C,\omega_C)$”，并补充了几何意义（周期格点的复环面）。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

#### 51. Degree of a line bundle on a curve
- **课程来源**: Module 3 / Riemann–Roch for Curves and Applications
- **课程定义**: 对曲线 $C$ 上可逆层（线丛）$\mathcal{L}$，$\deg\mathcal{L}=\deg D$（其中 $\mathcal{L}\cong\mathcal{O}_C(D)$）。
- **项目对应路径**: `docs/13-代数几何/04-除子与线丛的完整理论.md`
- **项目中的表述**: 文档在 Riemann-Roch 相关段落中使用了 $\deg D$ 和 $\mathcal{L}(D)$，但 **未给出** “线丛的 degree” 的独立定义块。
- **对齐判定**: 缺失
- **差异分析**: 仅有符号使用，无独立定义。
- **修正建议**: 补充线丛/可逆层度数的定义（通过对应除子类的度，或 stalk 长度）。

#### 52. Embedding of a curve into projective space
- **课程来源**: Module 3 / Riemann–Roch for Curves and Applications
- **课程定义**: 完全线性系 $|D|$ 给出的态射 $C\to\mathbb{P}^r$（$r=h^0(D)-1$），当 $|D|$ 基点自由时定义；若 $D$ 非常丰富则为闭浸入。
- **项目对应路径**: `docs/13-代数几何/07-曲线理论-深度扩展版.md`
- **项目中的表述**: 文档在 **定理 2.1** (Plücker 公式)、**定理 3.1** (Veronese 嵌入) 中提及射影嵌入，但 **未给出** 由完全线性系 $|D|$ 构造射影嵌入的定义块。
- **对齐判定**: 缺失
- **差异分析**: 仅有构造的几何后果，无嵌入的显式定义。
- **修正建议**: 补充线性系给出射影嵌入的构造与判据（$D$ very ample 等价于 $|D|$ 给出闭浸入）。

### Module 4: Surfaces and Intersection Theory

#### 53. Intersection pairing on a surface
- **课程来源**: Module 4 / Intersection Theory on Surfaces
- **课程定义**: 光滑射影曲面 $S$ 上，两个除子 $C,D$ 的相交数 $(C\cdot D)\in\mathbb{Z}$，双线性对称，满足 $(C\cdot D)=\sum_{P\in C\cap D}(C\cdot D)_P$（局部相交重数），对一般位置可计算为横截交点的个数。
- **项目对应路径**: `docs/13-代数几何/08-曲面理论-深度扩展版.md`
- **项目中的表述**: **定义 13.8.1** 给出“相交数 $(C\cdot D)\in\mathbb{Z}$，双线性、对称，对一般位置横截相交即交点个数”。并补充局部重数分解及 blowing-up 不变性。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

#### 54. Self-intersection $C^2$
- **课程来源**: Module 4 / Intersection Theory on Surfaces
- **课程定义**: $(C\cdot C)$，通过对一般位置代表元 $C'\sim C$ 计算 $(C\cdot C')$ 得到；亦可定义为限制法丛的次数。
- **项目对应路径**: `docs/13-代数几何/08-曲面理论-深度扩展版.md`
- **项目中的表述**: **定义 13.8.1** 中明确包含 $C^2=(C\cdot C)$，并给出 blow-up 公式 $C^2=\tilde{C}^2+1$（$\tilde{C}$ 为 strict transform）。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

#### 55. Exceptional divisor of a blow-up
- **课程来源**: Module 4 / Intersection Theory on Surfaces
- **课程定义**: 对点 $p\in S$ 的 blow-up $\pi:\tilde{S}\to S$，例外除子 $E=\pi^{-1}(p)\cong\mathbb{P}^1$，满足 $E^2=-1$。
- **项目对应路径**: `docs/13-代数几何/08-曲面理论-深度扩展版.md`
- **项目中的表述**: **定义 13.8.2** 给出例外除子为 $\pi^{-1}(p)\cong\mathbb{P}^1$，并说明 $E^2=-1$。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

#### 56. Blow-up of a surface at a point
- **课程来源**: Module 4 / Intersection Theory on Surfaces
- **课程定义**: 曲面 $S$ 在点 $p$ 的爆破 $\pi:\tilde{S}\to S$，由 $Bl_p(S)\subset S\times\mathbb{P}^1$ 给出；或局部坐标下 $(x,y)\mapsto (x:y)$。
- **项目对应路径**: `docs/13-代数几何/08-曲面理论-深度扩展版.md`
- **项目中的表述**: **定义 13.8.2** 给出局部坐标下的爆破构造（$(x,y)\mapsto (x:y)$）及严格变换的定义。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

#### 57. Arithmetic genus $p_a(S)$ of a surface
- **课程来源**: Module 4 / Classification of Surfaces
- **课程定义**: 对射影曲面 $S$，$p_a(S)=(-1)^{\dim S}(P_S(0)-1)$，或等价地 $p_a(S)=h^2(\mathcal{O}_S)-h^1(\mathcal{O}_S)$。
- **项目对应路径**: `docs/13-代数几何/08-曲面理论-深度扩展版.md`
- **项目中的表述**: 该文档中 **不存在** 算术亏格 $p_a(S)$ 的显式定义。
- **对齐判定**: 缺失
- **差异分析**: 核心定义缺失。
- **修正建议**: 补充曲面算术亏格 $p_a(S)$ 的定义（通过 Hilbert 多项式或层上同调）。

#### 58. Geometric genus $p_g(S)$
- **课程来源**: Module 4 / Classification of Surfaces
- **课程定义**: $p_g(S)=h^0(S,\omega_S)=h^2(S,\mathcal{O}_S)$（Serre 对偶）。
- **项目对应路径**: `docs/13-代数几何/08-曲面理论-深度扩展版.md`
- **项目中的表述**: 文档在 **定义 13.8.5** 中给出 $p_g(S)=h^0(S,\omega_S)=h^2(S,\mathcal{O}_S)$，并指出通过 Serre 对偶等价。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

#### 59. Irregularity $q(S)$
- **课程来源**: Module 4 / Classification of Surfaces
- **课程定义**: $q(S)=h^1(S,\mathcal{O}_S)=h^1(S,\omega_S)$。
- **项目对应路径**: `docs/13-代数几何/08-曲面理论-深度扩展版.md`
- **项目中的表述**: 该文档中 **不存在** irregularity $q(S)$ 的显式定义。
- **对齐判定**: 缺失
- **差异分析**: 核心定义缺失。
- **修正建议**: 补充 irregularity $q(S)$ 的定义及其与 Albanese 簇的关系。

#### 60. Kodaira dimension $\kappa(S)$
- **课程来源**: Module 4 / Classification of Surfaces
- **课程定义**: 对光滑射影簇 $X$，$\kappa(X)=\operatorname{tr.deg}_k\bigoplus_{m\ge 0}H^0(X,\omega_X^{\otimes m})-1$；若所有 $H^0=0$ 则定义 $\kappa(X)=-\infty$。
- **项目对应路径**: `docs/13-代数几何/08-曲面理论-深度扩展版.md`
- **项目中的表述**: 文档中 **未出现** Kodaira dimension 的定义。
- **对齐判定**: 缺失
- **差异分析**: 核心定义缺失。
- **修正建议**: 补充 Kodaira dimension 的定义及 Enriques 分类中的作用。

#### 61. Minimal surface
- **课程来源**: Module 4 / Classification of Surfaces
- **课程定义**: 光滑射影曲面 $S$ 为极小的，若不存在到另一光滑射影曲面的非同构双有理态射（等价于不存在例外 $-1$-曲线）。
- **项目对应路径**: `docs/13-代数几何/08-曲面理论-深度扩展版.md`
- **项目中的表述**: **定义 13.8.6** 中给出：不存在到另一光滑曲面的双有理态射，或等价地无例外 $-1$-曲线。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

#### 62. Ruled surface
- **课程来源**: Module 4 / Classification of Surfaces
- **课程定义**: 双有理等价于 $C\times\mathbb{P}^1$（$C$ 为曲线）的曲面；或存在到曲线 $C$ 的态射 $S\to C$ 使得一般纤维为 $\mathbb{P}^1$。
- **项目对应路径**: `docs/13-代数几何/08-曲面理论-深度扩展版.md`
- **项目中的表述**: 文档中 **未出现** ruled surface 的显式定义。
- **对齐判定**: 缺失
- **差异分析**: 核心定义缺失。
- **修正建议**: 补充 ruled surface 的定义及极小直纹面的分类。

#### 63. K3 surface
- **课程来源**: Module 4 / Classification of Surfaces
- **课程定义**: 满足 $K_S=0$ 且 $h^1(\mathcal{O}_S)=0$ 的光滑射影曲面。
- **项目对应路径**: `docs/13-代数几何/08-曲面理论-深度扩展版.md`
- **项目中的表述**: 文档中 **未出现** K3 surface 的显式定义。
- **对齐判定**: 缺失
- **差异分析**: 核心定义缺失。
- **修正建议**: 补充 K3 surface 的定义及基本例子（如四次曲面、Kummer 曲面）。

#### 64. Enriques surface
- **课程来源**: Module 4 / Classification of Surfaces
- **课程定义**: 满足 $q=0$、$p_g=0$、$2K_S\sim 0$（但 $K_S\not\sim 0$）的光滑射影曲面。
- **项目对应路径**: `docs/13-代数几何/08-曲面理论-深度扩展版.md`
- **项目中的表述**: 文档中 **未出现** Enriques surface 的显式定义。
- **对齐判定**: 缺失
- **差异分析**: 核心定义缺失。
- **修正建议**: 补充 Enriques surface 的定义及与 K3 的二次覆盖关系。

#### 65. Abelian surface
- **课程来源**: Module 4 / Classification of Surfaces
- **课程定义**: 二维阿贝尔簇（复 2-维复环面且可代数嵌入），具有群结构，$q=2$、$p_g=1$、$K_S=0$。
- **项目对应路径**: `docs/13-代数几何/08-曲面理论-深度扩展版.md`
- **项目中的表述**: 文档中 **未出现** Abelian surface 的显式定义。
- **对齐判定**: 缺失
- **差异分析**: 核心定义缺失。
- **修正建议**: 补充 Abelian surface 的定义及例子（如 $E\times E'$）。

### Module 5: Advanced Topics and Research Frontiers

#### 66. Hodge decomposition
- **课程来源**: Module 5 / Hodge Theory and the Period Map
- **课程定义**: 对紧 Kähler 流形 $X$，$H^n(X,\mathbb{C})=\bigoplus_{p+q=n}H^{p,q}(X)$，且 $\overline{H^{p,q}}=H^{q,p}$。
- **项目对应路径**: `docs/13-代数几何/09-霍奇理论入门.md`
- **项目中的表述**: **定义 13.9.1 (Hodge 分解)** 明确给出该分解及对称性条件。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

#### 67. Hodge numbers $h^{p,q}$
- **课程来源**: Module 5 / Hodge Theory and the Period Map
- **课程定义**: $h^{p,q}=\dim_\mathbb{C}H^{p,q}(X)$；满足 $h^{p,q}=h^{q,p}=h^{n-p,n-q}$（Serre 对偶）。
- **项目对应路径**: `docs/13-代数几何/09-霍奇理论入门.md`
- **项目中的表述**: 文档给出 $h^{p,q}=\dim_\mathbb{C}H^q(X,\Omega^p)$ 及对称性；虽未明确写出 $h^{p,q}=h^{n-p,n-q}$，但这是标准推论。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

#### 68. Period map / Period domain
- **课程来源**: Module 5 / Hodge Theory and the Period Map
- **课程定义**: 族 $f:\mathcal{X}\to B$ 诱导的映射 $\Phi:B\to D/\Gamma$，将参数 $t$ 映到 $H^n(X_t,\mathbb{C})$ 的 Hodge 结构；$D$ 为 Griffiths 周期域。
- **项目对应路径**: `docs/13-代数几何/09-霍奇理论入门.md`
- **项目中的表述**: 文档给出周期映射的定义（将参数映到 Hodge 结构）、周期域 $D$ 的定义（满足 Hodge-Riemann 关系的 Flag 流形子集），以及 Griffiths 横截性。
- **对齐判定**: 严格等价
- **差异分析**: 无。
- **修正建议**: 无需修正。

#### 69. Kodaira-Spencer map
- **课程来源**: Module 5 / Deformation Theory
- **课程定义**: 对族 $f:\mathcal{X}\to B$（$B$ 为参数空间，$0\in B$），KS 映射 $\kappa:T_0B\to H^1(X_0,T_{X_0})$，刻画无穷小形变方向。
- **项目对应路径**: `docs/13-代数几何/03-代数几何深度扩展版.md`
- **项目中的表述**: 文档为导出/无穷/量子代数几何综述；在文末列出了 Kodaira-Spencer 理论为前沿方向之一，但 **未给出** KS 映射的定义块。
- **对齐判定**: 缺失
- **差异分析**: 仅有方向性提及，无严格定义。
- **修正建议**: 补充 Kodaira-Spencer 映射的完整定义及几何解释。

#### 70. Deformation functor
- **课程来源**: Module 5 / Deformation Theory
- **课程定义**: 对概形 $X_0$，形变函子 $F:\mathbf{Art}/k\to\mathbf{Set}$ 将局部 Artin 环 $A$ 映到 $X_0$ 在 $A$ 上的平坦形变的同构类。
- **项目对应路径**: `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/25-概形的平坦族与形变理论.md`
- **项目中的表述**: 文档为 ASCII 卡片式概述，公式框中仅出现“形变函子 $F(A)=\{\text{平坦族 } X\to\operatorname{Spec}(A)\}$”，无局部 Artin 环、同构类、或 Schlessinger 条件的定义块。
- **对齐判定**: 近似表述
- **差异分析**: 仅有极其简略的公式框，缺少函子定义域、局部 Artin 环、及泛性条件。
- **修正建议**: 补充 Schlessinger 的形变函子定义（定义域为 $\mathbf{Art}/k$），并列出 Schlessinger 条件 (H1)–(H4)。

#### 71. First-order deformation
- **课程来源**: Module 5 / Deformation Theory
- **课程定义**: $X_0$ 在 $k[\varepsilon]/\varepsilon^2$ 上的平坦形变（无穷小一阶形变）；同构类空间为 $H^1(X_0,T_{X_0})$。
- **项目对应路径**: `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/25-概形的平坦族与形变理论.md`
- **项目中的表述**: 文档中仅有一句“$k[\varepsilon]/\varepsilon^2$ 上的平坦族”，无完整的“first-order deformation”定义块（未说明 obstruction space $H^2$、或 Cech 1-上闭链构造）。
- **对齐判定**: 近似表述
- **差异分析**: 数学对象被点到，但缺少完整的定义（如平坦族、同构类、与切空间 $H^1$ 的等价说明）。
- **修正建议**: 补充一阶形变的完整定义及与 $H^1(X_0,T_{X_0})$ 的等价性证明梗概。

#### 72. Obstruction theory
- **课程来源**: Module 5 / Deformation Theory
- **课程定义**: 给定 $A'\twoheadrightarrow A$ 的小扩张及 $X_0$ 在 $A$ 上的形变 $X$，研究将 $X$ 提升到 $A'$ 的障碍；通常属于 $H^2(X_0,T_{X_0})$。
- **项目对应路径**: `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/25-概形的平坦族与形变理论.md`
- **项目中的表述**: 文档中 **未出现** obstruction theory 的定义。
- **对齐判定**: 缺失
- **差异分析**: 核心定义缺失。
- **修正建议**: 补充形变障碍理论的定义及主障碍空间 $H^2(X_0,T_{X_0})$ 的说明。

#### 73. Moduli space
- **课程来源**: Module 5 / Deformation Theory
- **课程定义**: 参数化给定几何对象（如光滑射影曲线、向量丛）的代数簇（或 Deligne-Mumford 栈）$\mathcal{M}$，满足泛性质。
- **项目对应路径**: `docs/13-代数几何/03-代数几何深度扩展版.md`
- **项目中的表述**: 文档在 **13.3.5 模空间与稳定化** 中给出模空间的哲学描述，但 **无严格定义块**（如粗模空间、精细模空间、Deligne-Mumford 栈）。
- **对齐判定**: 近似表述
- **差异分析**: 仅有描述性/启发性文字，缺少严格的粗/精细模空间定义。
- **修正建议**: 补充模空间（coarse vs. fine）的严格定义，并说明 Deligne-Mumford 栈在模空间中的作用。

---

## 附录：严格等价判定清单

| 条目 | 定义名称 | 判定 |
|:----:|:---------|:----:|
| 1 | Affine variety | 严格 |
| 2 | Projective variety | 严格 |
| 3 | Zariski topology | 近似 |
| 4 | Quasi-projective variety | 缺失 |
| 5 | Regular map (morphism of varieties) | 缺失 |
| 6 | Rational map | 严格 |
| 7 | Birational isomorphism | 严格 |
| 8 | Blow-up of a point/subvariety | 近似 |
| 9 | Krull dimension of a variety | 近似 |
| 10 | Zariski tangent space | 严格 |
| 11 | Smooth (nonsingular) point | 缺失 |
| 12 | Tangent cone | 缺失 |
| 13 | Hilbert function | 缺失 |
| 14 | Hilbert polynomial | 缺失 |
| 15 | Arithmetic genus | 缺失 |
| 16 | Weil divisor | 严格 |
| 17 | Principal divisor | 严格 |
| 18 | Linear equivalence | 严格 |
| 19 | Linear series $g^r_d$ | 缺失 |
| 20 | Canonical divisor $K_X$ | 缺失 |
| 21 | Picard group | 严格 |
| 22 | Presheaf and sheaf | 严格 |
| 23 | Stalk of a sheaf | 缺失 |
| 24 | Sheafification | 严格 |
| 25 | Exact sequences of sheaves | 缺失 |
| 26 | Structure sheaf $\mathcal{O}_X$ | 缺失 |
| 27 | $\mathcal{O}_X$-Module | 近似 |
| 28 | Quasi-coherent sheaf | 严格 |
| 29 | Coherent sheaf | 近似 |
| 30 | Locally free sheaf / vector bundle | 缺失 |
| 31 | Reflexive sheaf | 缺失 |
| 32 | Cartier divisor | 严格 |
| 33 | Weil divisor | 严格 |
| 34 | $\mathcal{O}_X(D)$ (Cartier) | 严格 |
| 35 | Picard group | 严格 |
| 36 | Sheaf cohomology $H^i(X,\mathcal{F})$ | 严格 |
| 37 | Injective resolution | 缺失 |
| 38 | Flasque sheaf | 缺失 |
| 39 | Acyclic resolution | 缺失 |
| 40 | Čech cohomology | 严格 |
| 41 | Refinement of an open cover | 缺失 |
| 42 | Twisting sheaf $\mathcal{O}_{\mathbb{P}^n}(d)$ | 缺失 |
| 43 | Serre's twisting sheaf | 缺失 |
| 44 | Higher direct image $R^i f_*\mathcal{F}$ | 严格 |
| 45 | Flat morphism | 严格 |
| 46 | Dualizing sheaf $\omega_X$ | 近似 |
| 47 | Trace map | 近似 |
| 48 | Serre duality | 严格 |
| 49 | Riemann–Roch for curves | 严格 |
| 50 | Genus of a smooth projective curve | 严格 |
| 51 | Degree of a line bundle on a curve | 缺失 |
| 52 | Embedding of a curve into projective space | 缺失 |
| 53 | Intersection pairing on a surface | 严格 |
| 54 | Self-intersection $C^2$ | 严格 |
| 55 | Exceptional divisor of a blow-up | 严格 |
| 56 | Blow-up of a surface at a point | 严格 |
| 57 | Arithmetic genus $p_a(S)$ | 缺失 |
| 58 | Geometric genus $p_g(S)$ | 严格 |
| 59 | Irregularity $q(S)$ | 缺失 |
| 60 | Kodaira dimension $\kappa(S)$ | 缺失 |
| 61 | Minimal surface | 严格 |
| 62 | Ruled surface | 缺失 |
| 63 | K3 surface | 缺失 |
| 64 | Enriques surface | 缺失 |
| 65 | Abelian surface | 缺失 |
| 66 | Hodge decomposition | 严格 |
| 67 | Hodge numbers | 严格 |
| 68 | Period map / Period domain | 严格 |
| 69 | Kodaira-Spencer map | 缺失 |
| 70 | Deformation functor | 近似 |
| 71 | First-order deformation | 近似 |
| 72 | Obstruction theory | 缺失 |
| 73 | Moduli space | 近似 |

---

## 附录：新增文档需求列表

为填补 **29** 个缺失条目，建议新建或补充以下文档/章节：

1. `docs/13-代数几何/01-代数几何基础.md` — 补充 quasi-projective variety。
2. `docs/13-代数几何/02-代数几何增强版.md` — 补充 regular map (morphism of varieties)、smooth point（非循环定义）、tangent cone。
3. `docs/13-代数几何/03-代数几何深度扩展版.md` — 补充 Hilbert function / polynomial、Kodaira-Spencer map、moduli space 严格定义。
4. `docs/13-代数几何/04-层与上同调-深度扩展版.md` — 补充 stalk、exact sequence of sheaves、reflexive sheaf。
5. `docs/13-代数几何/04-除子与线丛的完整理论.md` — 补充 twisting sheaf $\mathcal{O}_{\mathbb{P}^n}(d)$、canonical divisor $K_X$、locally free sheaf (general rank)、degree of line bundle on curve。
6. `docs/13-代数几何/06-除子与线丛-深度扩展版.md` — 补充分解 Pic 与 Cartier 除子的等价性（已部分存在）。
7. `docs/13-代数几何/07-曲线理论-深度扩展版.md` — 补充 $g^r_d$、arithmetic genus $p_a$、embedding of a curve into $\mathbb{P}^r$。
8. `docs/13-代数几何/08-曲面理论-深度扩展版.md` — 补充 $p_a(S)$、$q(S)$、$\kappa(S)$、ruled surface、K3 / Enriques / Abelian surface。
9. `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/00-概形理论-概念总览.md` — 不应作为结构层 $\mathcal{O}_X$ 的定义源；需将引用指向 `02-仿射概形基础.md`。
10. `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/31-概形的层理论与层范畴.md` — 重写 $\mathcal{O}_X$-Module 为严格定义块。
11. `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/05-拟凝聚层与凝聚层.md` — 重写 coherent sheaf，补全 Hartshorne 两条标准条件。
12. `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/01-层上同调基础.md` — 补充 injective resolution、flasque sheaf、acyclic resolution。
13. `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/17-Cech上同调与层上同调.md` — 补充 refinement 定义。
14. `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/21-上同调与Serre对偶.md` — 补充 dualizing sheaf 的一般定义（proper/CM）及 trace map 名称。
15. `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/25-概形的平坦族与形变理论.md` — 大幅扩充：deformation functor（Schlessinger 框架）、first-order deformation、obstruction theory。

---

**文档结束**
