---
title: MIT 18.100A Real Analysis 定义对齐手册 (L3 语义对齐)
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# MIT 18.100A Real Analysis 定义对齐手册 (L3 语义对齐)

**文档编号**: D016  
**课程**: MIT 18.100A — Introduction to Real Analysis  
**教材**: Lebl, *Basic Analysis I*  
**生成日期**: 2026-04-04  
**对齐标准**: D002 — L3 定义对齐的精确判定标准  

---

## 定义: Union, intersection, complement
- **课程来源**: MIT 18.100A, Week 1: Foundations — Sets, Induction, and Cardinality, Sets and their operations, [JL] Section 0.3
- **课程定义**: For sets A, B in a universal set X: A ∪ B = {x : x ∈ A or x ∈ B}; A ∩ B = {x : x ∈ A and x ∈ B}; Aᶜ = X \ A = {x ∈ X : x ∉ A}.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档中未找到并集、交集、补集的形式化定义。仅在目录的'交叉关系 / Intersection Relations'条目中出现'交集'一词。
- **对齐判定**: 缺失
- **差异分析**: 项目文档未包含集合论基础定义。
- **修正建议**: 在 `docs/01-基础数学/集合论/01-集合论基础-国际标准版.md` 中已存在相关内容，建议将该文档链接加入 D006 的 formal_math_path，或在实分析文档中增加前置知识小节。

## 定义: Power set
- **课程来源**: MIT 18.100A, Week 1: Foundations — Sets, Induction, and Cardinality, Sets and their operations, [JL] Section 0.3
- **课程定义**: The power set P(A) of a set A is the set of all subsets of A, i.e., P(A) = {B : B ⊆ A}.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档中未找到'幂集'一词。
- **对齐判定**: 缺失
- **差异分析**: 项目文档完全缺失幂集定义。
- **修正建议**: 建议参考 `docs/01-基础数学/集合论/01-集合论基础-国际标准版.md` 中的幂集定义，并在课程对齐路径中显式映射。

## 定义: Injective, surjective, bijective functions
- **课程来源**: MIT 18.100A, Week 1: Foundations — Sets, Induction, and Cardinality, Sets and their operations, [JL] Section 0.3
- **课程定义**: A function f: A → B is injective if f(x)=f(y) ⇒ x=y; surjective if ∀b∈B, ∃a∈A with f(a)=b; bijective if both injective and surjective.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档中未找到单射、满射、双射的形式化定义。
- **对齐判定**: 缺失
- **差异分析**: 项目文档未包含函数基本性质的定义。
- **修正建议**: 建议映射到 `docs/01-基础数学/集合论/03-函数与映射-深度扩展版.md`。

## 定义: Cardinality (size) of sets
- **课程来源**: MIT 18.100A, Week 1: Foundations — Sets, Induction, and Cardinality, Sets and their operations, [JL] Section 0.3
- **课程定义**: Two sets A and B have the same cardinality, |A| = |B|, if there exists a bijection f: A → B.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档中未找到'基数'、'等势'或'cardinality'的定义。
- **对齐判定**: 缺失
- **差异分析**: 项目文档完全缺失基数定义。
- **修正建议**: 建议在集合论基础文档中补充，并在 D006 中修正映射路径。

## 定义: Countable set
- **课程来源**: MIT 18.100A, Week 1: Foundations — Sets, Induction, and Cardinality, Sets and their operations, [JL] Section 0.3
- **课程定义**: A set A is countable if |A| = |ℕ|, i.e., there exists a bijection between A and ℕ. A set is countably infinite if it is countable and infinite.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档中未找到'可数集'的定义。
- **对齐判定**: 缺失
- **差异分析**: 项目文档完全缺失可数集定义。
- **修正建议**: 建议在集合论基础文档或实分析前置知识中补充。

## 定义: Field
- **课程来源**: MIT 18.100A, Week 2: The Real Numbers — Ordered Fields and Completeness, Ordered fields and the real numbers, [JL] Sections 1.1 and 1.2
- **课程定义**: A field is a set F together with two operations + and · satisfying: (i) associativity and commutativity of both operations; (ii) existence of additive and multiplicative identities; (iii) existence of additive inverses and multiplicative inverses (for nonzero elements); (iv) distributivity of · over +.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: **定义 3.1.1** (实数域 / Real Number Field)
实数集 ℝ 是一个有序域，满足以下公理：
1. **域公理** (Field Axioms)：加法结合律、加法交换律、加法单位元、加法逆元、乘法结合律、乘法交换律、乘法单位元、乘法逆元（对于 a ≠ 0）、分配律。
2. **序公理** (Order Axioms)：自反性、反对称性、传递性、完全性。
- **对齐判定**: 近似表述
- **差异分析**: 项目文档将域公理嵌入在'ℝ 是一个有序域'的陈述中，没有给出一般域的抽象定义（即未说明'域是集合 F 配备运算 +, · 满足……'）。对象域被限制为 ℝ，而非一般集合 F。对于 Lebl 教材中在一般有序域框架下讲授的课程而言，这是一个对象域缩小的问题。
- **修正建议**: 建议在实分析文档中补充一般域的抽象定义，再说明 ℝ 是满足完备性公理的有序域实例。

## 定义: Ordered field
- **课程来源**: MIT 18.100A, Week 2: The Real Numbers — Ordered Fields and Completeness, Ordered fields and the real numbers, [JL] Sections 1.1 and 1.2
- **课程定义**: An ordered field is a field F together with a relation < satisfying: (i) trichotomy; (ii) transitivity; (iii) a < b ⇒ a + c < b + c; (iv) a < b and c > 0 ⇒ ac < bc.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 同'Field'条目。项目文档将序公理与域公理一起列出，但同样未给出一般有序域的抽象定义。
- **对齐判定**: 近似表述
- **差异分析**: 与 Field 条目相同：项目文档未在一般集合 F 的层面上定义有序域，而是直接断言'ℝ 是一个有序域'。课程教材 Lebl §1.1 明确在一般有序域上定义了序关系的三歧性、传递性以及与运算的相容性。
- **修正建议**: 建议补充一般有序域的抽象定义，明确列出序关系与域运算相容的四个条件。

## 定义: Least upper bound (supremum)
- **课程来源**: MIT 18.100A, Week 2: The Real Numbers — Ordered Fields and Completeness, Ordered fields and the real numbers, [JL] Sections 1.1 and 1.2
- **课程定义**: Let S ⊆ ℝ be a set. A number M is the least upper bound (supremum) of S if (i) M is an upper bound of S (i.e., x ≤ M for all x ∈ S); and (ii) if M' < M, then M' is not an upper bound of S (i.e., for every ε > 0 there exists x ∈ S such that M − ε < x).
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: **定义 3.1.2** (上确界 / Supremum)
集合 A ⊆ ℝ 的上确界 sup A 是 A 的最小上界。
- **对齐判定**: 近似表述
- **差异分析**: 项目文档的表述过于简略，仅给出直观描述'最小上界'，缺少课程要求的形式化两条：(i) 是上界；(ii) 任何小于它的数都不是上界。虽然这在数学上等价，但对于 L3 定义对齐标准，项目文档缺少显式的条件分解，不利于学生对照教材理解。
- **修正建议**: 建议将定义改写为：'集合 A ⊆ ℝ 的上确界 sup A 是满足以下条件的实数 M：(1) 对任意 x ∈ A，有 x ≤ M；(2) 对任意 ε > 0，存在 x ∈ A 使得 M − ε < x。'

## 定义: Greatest lower bound (infimum)
- **课程来源**: MIT 18.100A, Week 2: The Real Numbers — Ordered Fields and Completeness, Ordered fields and the real numbers, [JL] Sections 1.1 and 1.2
- **课程定义**: A number m is the greatest lower bound (infimum) of S ⊆ ℝ if (i) m is a lower bound of S; and (ii) if m < m', then m' is not a lower bound of S.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: **定义 3.1.3** (下确界 / Infimum)
集合 A ⊆ ℝ 的下确界 inf A 是 A 的最大下界。
- **对齐判定**: 近似表述
- **差异分析**: 与上确界条目相同：表述过于简略，缺少形式化的两条条件分解。
- **修正建议**: 建议仿照上确界修正建议，补充下确界的形式化双条件定义。

## 定义: Archimedean property
- **课程来源**: MIT 18.100A, Week 3: Properties of ℝ — Archimedean Property, Density, and Uncountability, Archimedean property and density, [JL] Sections 1.2, 1.3, 1.5, and 2.1
- **课程定义**: The real numbers ℝ have the Archimedean property: for any x, y ∈ ℝ with x > 0, there exists n ∈ ℕ such that nx > y. Equivalently, for any x ∈ ℝ there exists n ∈ ℕ such that n > x.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档中未找到'阿基米德性质'或'Archimedean property'的定义。
- **对齐判定**: 缺失
- **差异分析**: 项目文档完全缺失阿基米德性质的定义。
- **修正建议**: P0：在实分析文档的'实数性质'小节中补充阿基米德性质的正式定义。

## 定义: Density of ℚ in ℝ
- **课程来源**: MIT 18.100A, Week 3: Properties of ℝ — Archimedean Property, Density, and Uncountability, Archimedean property and density, [JL] Sections 1.2, 1.3, 1.5, and 2.1
- **课程定义**: The rational numbers ℚ are dense in ℝ: for any x, y ∈ ℝ with x < y, there exists r ∈ ℚ such that x < r < y.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档中未找到'有理数在实数中稠密'的形式化定义。仅在思维导图和目录中出现'稠密性'一词。
- **对齐判定**: 缺失
- **差异分析**: 项目文档缺少有理数稠密性的形式化定义。
- **修正建议**: P0：在实分析文档中补充'对任意 x, y ∈ ℝ，若 x < y，则存在 r ∈ ℚ 使得 x < r < y'的正式定义块。

## 定义: Absolute value
- **课程来源**: MIT 18.100A, Week 3: Properties of ℝ — Archimedean Property, Density, and Uncoverability, Archimedean property and density, [JL] Sections 1.2, 1.3, 1.5, and 2.1
- **课程定义**: For x ∈ ℝ, the absolute value is |x| = x if x ≥ 0, and |x| = −x if x < 0.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档中未找到'绝对值'的定义。
- **对齐判定**: 缺失
- **差异分析**: 项目文档完全缺失绝对值定义。
- **修正建议**: P1：在实分析文档中补充绝对值的分段定义。

## 定义: Triangle inequality
- **课程来源**: MIT 18.100A, Week 3: Properties of ℝ — Archimedean Property, Density, and Uncountability, Archimedean property and density, [JL] Sections 1.2, 1.3, 1.5, and 2.1
- **课程定义**: For all x, y ∈ ℝ, |x + y| ≤ |x| + |y|. More generally, |x − y| ≤ |x − z| + |z − y| for all x, y, z ∈ ℝ.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档中仅在 Lean 4 代码注释中出现'应用三角不等式'，没有作为独立概念给出形式化定义。
- **对齐判定**: 缺失
- **差异分析**: 项目文档未将三角不等式作为可引用的定义/定理块呈现。
- **修正建议**: P1：在实分析文档中补充三角不等式的正式陈述。

## 定义: Sequence of real numbers
- **课程来源**: MIT 18.100A, Week 4: Sequences — Convergence and Algebraic Properties, Convergent sequences, [JL] Sections 2.1 and 2.2
- **课程定义**: A sequence of real numbers is a function a: ℕ → ℝ, usually denoted (aₙ)_{n=1}^∞ or simply (aₙ).
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: **定义 3.1.4** (序列 / Sequence)
序列是一个函数 a: ℕ → ℝ，记作 (aₙ)_{n=1}^∞。
- **对齐判定**: 严格等价
- **差异分析**: 对象域、逻辑条件、符号约定均与课程教材一致。
- **修正建议**: 无需修正。

## 定义: Convergence of a sequence (ε-N definition)
- **课程来源**: MIT 18.100A, Week 4: Sequences — Convergence and Algebraic Properties, Convergent sequences, [JL] Sections 2.1 and 2.2
- **课程定义**: A sequence (aₙ) converges to L ∈ ℝ if for every ε > 0 there exists N ∈ ℕ such that for all n ≥ N, |aₙ − L| < ε. We write lim_{n→∞} aₙ = L.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: **定义 3.1.5** (序列极限 / Sequence Limit)
序列 (aₙ) 收敛到 L ∈ ℝ，记作 lim_{n → ∞} aₙ = L，如果：
∀ ε > 0, ∃ N ∈ ℕ, ∀ n ≥ N, |aₙ − L| < ε
- **对齐判定**: 严格等价
- **差异分析**: ε-N 定义的量化结构、不等式形式、符号使用均与 Lebl §2.1 完全一致。
- **修正建议**: 无需修正。

## 定义: Subsequence
- **课程来源**: MIT 18.100A, Week 4: Sequences — Convergence and Algebraic Properties, Convergent sequences, [JL] Sections 2.1 and 2.2
- **课程定义**: A subsequence of (aₙ) is a sequence (a_{n_k}) where n_k ∈ ℕ is a strictly increasing sequence of indices (n_1 < n_2 < n_3 < ⋯).
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档中未找到'子列'或'subsequence'的形式化定义。仅在'概念深度分析：极限'的'逻辑必然的属性'中提到'收敛序列的任意子序列也收敛到同一极限'，但没有先给出子列的定义。
- **对齐判定**: 缺失
- **差异分析**: 项目文档缺少子列的形式化定义，仅在定理/性质中使用了该概念。
- **修正建议**: P0：在'序列与极限'章节中补充子列的定义：'设 (aₙ) 为序列，若 n_k ∈ ℕ 严格递增，则称 (a_{n_k}) 为 (aₙ) 的子列。'

## 定义: Monotone sequence
- **课程来源**: MIT 18.100A, Week 4: Sequences — Convergence and Algebraic Properties, Convergent sequences, [JL] Sections 2.1 and 2.2
- **课程定义**: A sequence (aₙ) is monotone increasing if aₙ ≤ a_{n+1} for all n; monotone decreasing if aₙ ≥ a_{n+1} for all n.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档中未找到'单调序列'的形式化定义。在单调收敛定理的证明中直接使用了'单调递增''单调递减'的表述，但未前置定义。
- **对齐判定**: 缺失
- **差异分析**: 项目文档在定理证明中使用了单调序列，但未给出其定义。
- **修正建议**: P0：在单调收敛定理之前补充单调递增/单调递减序列的定义。

## 定义: Limit superior (limsup)
- **课程来源**: MIT 18.100A, Week 5: Completeness and Series — Limsup, Liminf, and Bolzano-Weierstrass, Limsup, liminf, and completeness, [JL] Sections 2.2, 2.3, 2.4, and 2.5
- **课程定义**: For a bounded sequence (xₙ), limsup_{n→∞} xₙ = inf_{n∈ℕ} sup_{k≥n} x_k = lim_{n→∞} (sup_{k≥n} x_k).
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档中仅在'概念深度分析：极限'的'相关实例'中提到'序列的上极限'，没有给出数学公式或形式化定义。
- **对齐判定**: 缺失
- **差异分析**: 项目文档只有直观提及，没有 limsup 的形式化定义（如 inf sup 或极限形式）。
- **修正建议**: P0：补充 limsup 和 liminf 的正式定义，建议给出 Lebl 采用的 inf-sup 构造形式。

## 定义: Limit inferior (liminf)
- **课程来源**: MIT 18.100A, Week 5: Completeness and Series — Limsup, Liminf, and Bolzano-Weierstrass, Limsup, liminf, and completeness, [JL] Sections 2.2, 2.3, 2.4, and 2.5
- **课程定义**: For a bounded sequence (xₙ), liminf_{n→∞} xₙ = sup_{n∈ℕ} inf_{k≥n} x_k = lim_{n→∞} (inf_{k≥n} x_k).
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 与 limsup 相同，仅作为'相关实例'被提及，无形式化定义。
- **对齐判定**: 缺失
- **差异分析**: 项目文档缺少 liminf 的形式化定义。
- **修正建议**: P0：与 limsup 一同补充。

## 定义: Cauchy sequence
- **课程来源**: MIT 18.100A, Week 5: Completeness and Series — Limsup, Liminf, and Bolzano-Weierstrass, Limsup, liminf, and completeness, [JL] Sections 2.2, 2.3, 2.4, and 2.5
- **课程定义**: A sequence (xₙ) is a Cauchy sequence if for every ε > 0 there exists M ∈ ℕ such that for all n, k ≥ M, |xₙ − x_k| < ε.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 主文档 `01-实分析.md` 中未找到 Cauchy 序列的正式定义。仅在 Lean 4 文档 `docs/09-形式化证明/Lean4/08-柯西收敛准则.lean` 和深度扩展版中出现定义，但这两个路径均非 D006 指定的 formal_math_path。
- **对齐判定**: 缺失
- **差异分析**: 根据任务要求，必须以 D006 标注的 formal_math_path 为准。主文档缺失 Cauchy 序列的定义块。
- **修正建议**: P0：在 `docs/03-分析学/01-实分析/01-实分析.md` 的'序列与极限'章节中补充 Cauchy 序列的 ε-N 定义。

## 定义: Convergent series
- **课程来源**: MIT 18.100A, Week 5: Completeness and Series — Limsup, Liminf, and Bolzano-Weierstrass, Limsup, liminf, and completeness, [JL] Sections 2.2, 2.3, 2.4, and 2.5
- **课程定义**: Given a sequence (aₙ), the series ∑_{n=1}^∞ aₙ converges if the sequence of partial sums (Sₙ) converges, where Sₙ = ∑_{k=1}^n a_k.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: **定义 3.1.5.2** (级数收敛 / Series Convergence)
级数 ∑_{n=1}^∞ aₙ 收敛，如果部分和序列 (Sₙ) 收敛，即存在 S ∈ ℝ 使得：
lim_{n → ∞} Sₙ = S
此时称 S 为级数的和，记作 ∑_{n=1}^∞ aₙ = S。
- **对齐判定**: 严格等价
- **差异分析**: 项目文档通过部分和序列的极限来定义级数收敛，与 Lebl §2.5 的定义完全一致。
- **修正建议**: 无需修正。

## 定义: Partial sum
- **课程来源**: MIT 18.100A, Week 5: Completeness and Series — Limsup, Liminf, and Bolzano-Weierstrass, Limsup, liminf, and completeness, [JL] Sections 2.2, 2.3, 2.4, and 2.5
- **课程定义**: The N-th partial sum of a series ∑ aₙ is S_N = a_1 + a_2 + ⋯ + a_N = ∑_{n=1}^N a_n.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: **定义 3.1.5.1** (级数 / Series)
给定序列 (aₙ)_{n=1}^∞，级数 ∑_{n=1}^∞ aₙ 定义为部分和序列 (Sₙ) 的极限，其中：
Sₙ = ∑_{k=1}^n a_k
- **对齐判定**: 严格等价
- **差异分析**: 项目文档在级数定义中明确给出了部分和 Sₙ 的公式，与课程教材等价。
- **修正建议**: 无需修正。

## 定义: Absolute convergence
- **课程来源**: MIT 18.100A, Week 6: Series Tests — Absolute, Comparison, Ratio, Root, and Alternating, Convergence tests for series, [JL] Sections 2.5 and 2.6
- **课程定义**: A series ∑ aₙ converges absolutely if the series ∑ |aₙ| converges.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档中仅在'概念深度分析：级数'的'定义方式'和'概念外延'中提到'绝对收敛'，没有给出'若 ∑|aₙ| 收敛，则称 ∑aₙ 绝对收敛'的形式化定义块。
- **对齐判定**: 缺失
- **差异分析**: 项目文档缺少绝对收敛的形式化定义，仅有概念提及。
- **修正建议**: P0：在级数章节中补充绝对收敛和条件收敛的定义块。

## 定义: Conditional convergence
- **课程来源**: MIT 18.100A, Week 6: Series Tests — Absolute, Comparison, Ratio, Root, and Alternating, Convergence tests for series, [JL] Sections 2.5 and 2.6
- **课程定义**: A series ∑ aₙ converges conditionally if ∑ aₙ converges but ∑ |aₙ| diverges.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 与绝对收敛相同，仅有概念提及，无形式化定义。
- **对齐判定**: 缺失
- **差异分析**: 项目文档缺少条件收敛的形式化定义。
- **修正建议**: P0：与绝对收敛一同补充。

## 定义: p-series
- **课程来源**: MIT 18.100A, Week 6: Series Tests — Absolute, Comparison, Ratio, Root, and Alternating, Convergence tests for series, [JL] Sections 2.5 and 2.6
- **课程定义**: A p-series is a series of the form ∑_{n=1}^∞ 1/n^p for some real number p.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档在'标准实例'中列出：'p-级数：∑_{n=1}^∞ 1/n^p - p-级数（p > 1时收敛）'。这是一个实例说明，而非定义块。
- **对齐判定**: 近似表述
- **差异分析**: 项目文档将 p-级数作为'标准实例'呈现，而非正式的 Definition 块。虽然数学内容正确，但不符合课程教材中'定义 → 实例'的讲授结构。
- **修正建议**: 建议将 p-级数从'实例'提升为正式定义：'形如 ∑ 1/n^p 的级数称为 p-级数，其中 p ∈ ℝ。'

## 定义: Cluster point (accumulation point)
- **课程来源**: MIT 18.100A, Week 7: Limits of Functions, Limits of functions, [JL] Section 3.1
- **课程定义**: A point p ∈ ℝ is a cluster point of a set S ⊆ ℝ if for every ε > 0, the punctured neighborhood (p − ε, p + ε) \ {p} contains a point of S. Equivalently, there exists a sequence (xₙ) in S \ {p} such that lim xₙ = p.
- **项目对应路径**: `docs/05-拓扑学/01-点集拓扑.md`
- **项目中的表述**: 指定的拓扑学文档中完全未找到'聚点'、'accumulation point'、'cluster point'或'极限点'的定义。在深度扩展版 `docs/03-分析学/01-实分析/01-实分析-深度扩展版.md` 的函数极限定义中出现了'a 是 A 的聚点'的前提，但主文档和指定的拓扑文档均无聚点的独立定义。
- **对齐判定**: 缺失
- **差异分析**: D006 将聚点映射到 `docs/05-拓扑学/01-点集拓扑.md`，但该文档中不存在此概念。
- **修正建议**: P0：在 `docs/05-拓扑学/01-点集拓扑.md` 或 `docs/03-分析学/01-实分析/01-实分析.md` 中补充聚点的 ε-邻域定义。

## 定义: Limit of a function (ε-δ definition)
- **课程来源**: MIT 18.100A, Week 7: Limits of Functions, Limits of functions, [JL] Section 3.1
- **课程定义**: Let f: S → ℝ be a function and c a cluster point of S. We say the limit of f(x) as x approaches c is L if for every ε > 0 there exists δ > 0 such that for all x ∈ S with 0 < |x − c| < δ, we have |f(x) − L| < ε.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: **定义 3.1.6** (函数极限 / Function Limit)
函数 f: A → ℝ 在点 a 的极限为 L，记作 lim_{x → a} f(x) = L，如果：
∀ ε > 0, ∃ δ > 0, ∀ x ∈ A, 0 < |x − a| < δ ⇒ |f(x) − L| < ε
- **对齐判定**: 严格等价
- **差异分析**: 项目文档给出了标准的 ε-δ 定义，量化结构与不等式形式和 Lebl §3.1 完全一致。
- **修正建议**: 无需修正。

## 定义: Sequential criterion for limits
- **课程来源**: MIT 18.100A, Week 7: Limits of Functions, Limits of functions, [JL] Section 3.1
- **课程定义**: Let f: S → ℝ and c be a cluster point of S. Then lim_{x→c} f(x) = L if and only if for every sequence (xₙ) in S \ {c} such that lim xₙ = c, the sequence (f(xₙ)) converges to L.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档中未找到'序列准则'或'sequential criterion'的独立定义。虽然在定理部分可能隐含此等价刻画，但没有作为定义或定理显式陈述。
- **对齐判定**: 缺失
- **差异分析**: 项目文档未显式给出函数极限的序列刻画。
- **修正建议**: P0：在函数极限章节中补充定理/定义：'lim_{x→a} f(x) = L 当且仅当对任意满足 xₙ → a 且 xₙ ≠ a 的序列，有 f(xₙ) → L。'

## 定义: Continuity at a point
- **课程来源**: MIT 18.100A, Week 8: Continuity — Definitions and Classic Examples, Continuity of functions, [JL] Sections 3.1 and 3.2
- **课程定义**: A function f: S → ℝ is continuous at c ∈ S if for every ε > 0 there exists δ > 0 such that for all x ∈ S with |x − c| < δ, we have |f(x) − f(c)| < ε. Equivalently, lim_{x→c} f(x) = f(c).
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: **定义 3.1.9** (连续函数 / Continuous Function)
函数 f: A → ℝ 在点 a ∈ A 连续，如果：
lim_{x → a} f(x) = f(a)
等价地，对于任意 ε > 0，存在 δ > 0 使得：
|x − a| < δ ⇒ |f(x) − f(a)| < ε
- **对齐判定**: 严格等价
- **差异分析**: 项目文档同时给出了极限形式和 ε-δ 形式，与 Lebl §3.2 完全一致。
- **修正建议**: 无需修正。

## 定义: One-sided limits
- **课程来源**: MIT 18.100A, Week 8: Continuity — Definitions and Classic Examples, Continuity of functions, [JL] Sections 3.1 and 3.2
- **课程定义**: The right-hand limit lim_{x→a^+} f(x) = L if ∀ε>0, ∃δ>0 such that ∀x∈S with a < x < a+δ, |f(x)−L|<ε. The left-hand limit is defined analogously.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: **定义 3.1.7** (右极限 / Right Limit)
lim_{x → a^+} f(x) = L ↔ ∀ ε > 0, ∃ δ > 0, ∀ x ∈ A, a < x < a + δ ⇒ |f(x) − L| < ε

**定义 3.1.8** (左极限 / Left Limit)
lim_{x → a^-} f(x) = L ↔ ∀ ε > 0, ∃ δ > 0, ∀ x ∈ A, a − δ < x < a ⇒ |f(x) − L| < ε
- **对齐判定**: 严格等价
- **差异分析**: 项目文档给出了精确的 ε-δ 单侧极限定义，与课程教材等价。
- **修正建议**: 无需修正。

## 定义: Dirichlet function
- **课程来源**: MIT 18.100A, Week 8: Continuity — Definitions and Classic Examples, Continuity of functions, [JL] Sections 3.1 and 3.2
- **课程定义**: The Dirichlet function D: ℝ → ℝ is defined by D(x) = 1 if x ∈ ℚ, and D(x) = 0 if x ∉ ℚ (i.e., x ∈ ℝ \ ℚ).
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析-增强版.md`
- **项目中的表述**: ```lean
def dirichlet_function (x : ℝ) : ℝ :=
  if x ∈ Set.range (λ n : ℕ, (n : ℝ)) then 1 else 0
```
- **对齐判定**: 近似表述
- **差异分析**: **严重问题**：项目增强版中的 Lean 4 实现将 Dirichlet 函数定义为'当 x 是自然数（ℕ）时为 1，否则为 0'，这与标准的 Dirichlet 函数（x ∈ ℚ 时为 1，x ∉ ℚ 时为 0）完全不同。该实现甚至不是 Dirichlet 函数的一个变体，而是一个完全不同的函数（自然数的特征函数）。
- **修正建议**: **必须修正**：将 Lean 4 代码改为 `if ∃ q : ℚ, x = (q : ℝ) then 1 else 0` 或等价的 ℚ-成员判定，并在文档中给出标准数学定义：D(x) = 1 (x ∈ ℚ), D(x) = 0 (x ∉ ℚ)。

## 定义: Uniform continuity
- **课程来源**: MIT 18.100A, Week 9: Global Properties of Continuous Functions and the Derivative, Continuous functions on closed bounded intervals, [JL] Sections 3.3, 3.4, and 4.1
- **课程定义**: A function f: S → ℝ is uniformly continuous if for every ε > 0 there exists δ > 0 such that for all x, c ∈ S with |x − c| < δ, we have |f(x) − f(c)| < ε.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档中仅在'概念深度分析：连续'的'标准实例'和'间接外延'中提到'一致连续'，没有给出 ε-δ 形式化的定义块。
- **对齐判定**: 缺失
- **差异分析**: 项目文档缺少一致连续性的形式化定义。课程强调'δ 只依赖于 ε 而不依赖于点'这一关键区别，但项目文档未呈现。
- **修正建议**: P0：在连续函数章节中补充一致连续的正式定义，并强调 δ 的全局性。

## 定义: Derivative
- **课程来源**: MIT 18.100A, Week 9: Global Properties of Continuous Functions and the Derivative, Continuous functions on closed bounded intervals, [JL] Sections 3.3, 3.4, and 4.1
- **课程定义**: The derivative of f at a is f'(a) = lim_{h→0} [f(a+h) − f(a)] / h, provided this limit exists.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: **定义 3.1.10** (导数 / Derivative)
函数 f 在点 a 的导数为：
f'(a) = lim_{h → 0} (f(a + h) − f(a)) / h
如果这个极限存在。
- **对齐判定**: 严格等价
- **差异分析**: 项目文档给出了标准的差商极限定义，与 Lebl §4.1 完全一致。
- **修正建议**: 无需修正。

## 定义: Lipschitz continuity
- **课程来源**: MIT 18.100A, Week 9: Global Properties of Continuous Functions and the Derivative, Continuous functions on closed bounded intervals, [JL] Sections 3.3, 3.4, and 4.1
- **课程定义**: A function f: S → ℝ is Lipschitz continuous if there exists K > 0 such that |f(x) − f(y)| ≤ K|x − y| for all x, y ∈ S.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档中仅在'概念深度分析：连续'中提到'Lipschitz连续：函数满足Lipschitz条件'，没有给出 Lipschitz 条件的数学公式。
- **对齐判定**: 缺失
- **差异分析**: 项目文档只有名称提及，没有 Lipschitz 常数 K 和不等式的形式化定义。
- **修正建议**: P1：补充定义：'存在 K > 0，使得对所有 x, y ∈ S，有 |f(x) − f(y)| ≤ K|x − y|。'

## 定义: Differentiable at a point
- **课程来源**: MIT 18.100A, Week 10: Differentiation — Rules, Rolle, and Mean Value, Differentiability, [JL] Sections 4.1 and 4.2
- **课程定义**: A function f is differentiable at a if the limit defining f'(a) exists.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 同'Derivative'条目。**定义 3.1.10** 在给出导数公式后明确说明'如果这个极限存在'，这即等价于'函数在点 a 可微'。
- **对齐判定**: 严格等价
- **差异分析**: 项目文档通过'极限存在'自然蕴含了可微性的定义，与课程教材等价。
- **修正建议**: 无需修正。

## 定义: Relative (local) maximum and minimum
- **课程来源**: MIT 18.100A, Week 10: Differentiation — Rules, Rolle, and Mean Value, Differentiability, [JL] Sections 4.1 and 4.2
- **课程定义**: A function f has a relative (local) maximum at c if there exists δ > 0 such that f(x) ≤ f(c) for all x in (c − δ, c + δ). A relative minimum is defined with f(x) ≥ f(c).
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档中未找到'局部极大值'、'局部极小值'或'relative maximum'的定义。
- **对齐判定**: 缺失
- **差异分析**: 项目文档完全缺失局部极值的定义。
- **修正建议**: P1：在微分学章节中补充局部极大值和局部极小值的 δ-邻域定义。

## 定义: Taylor polynomial
- **课程来源**: MIT 18.100A, Week 11: Taylor's Theorem and the Riemann Integral, Taylor expansion and Riemann integration, [JL] Section 4.3
- **课程定义**: The n-th Taylor polynomial of f at a is P_n(x) = f(a) + f'(a)(x−a) + f''(a)(x−a)²/2! + ⋯ + f^{(n)}(a)(x−a)^n/n!.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档中仅在'概念深度分析：级数'中提及'泰勒级数：函数的泰勒展开'，没有给出 Taylor 多项式的显式公式。
- **对齐判定**: 缺失
- **差异分析**: 项目文档缺少 Taylor 多项式的显式定义（只提到泰勒级数）。
- **修正建议**: P1：在微分学或级数章节中补充 n 阶 Taylor 多项式的公式定义。

## 定义: Partition
- **课程来源**: MIT 18.100A, Week 11: Taylor's Theorem and the Riemann Integral, Taylor expansion and Riemann integration, [JL] Section 4.3
- **课程定义**: A partition P of [a, b] is a finite set {x_0, x_1, …, x_n} such that a = x_0 < x_1 < ⋯ < x_n = b.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: **定义 3.1.11** (分割 / Partition)
区间 [a, b] 的分割是有限点集 P = {x_0, x_1, …, x_n}，其中 a = x_0 < x_1 < ⋯ < x_n = b。
- **对齐判定**: 严格等价
- **差异分析**: 项目文档给出的分割定义与 Lebl §4.3 完全一致。
- **修正建议**: 无需修正。

## 定义: Riemann sum
- **课程来源**: MIT 18.100A, Week 11: Taylor's Theorem and the Riemann Integral, Taylor expansion and Riemann integration, [JL] Section 4.3
- **课程定义**: Given a partition P and sample points ξ_i ∈ [x_{i−1}, x_i], the Riemann sum is S(f, P) = ∑_{i=1}^n f(ξ_i)(x_i − x_{i−1}).
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: **定义 3.1.12** (黎曼和 / Riemann Sum)
对于分割 P 和函数 f，黎曼和为：
S(f, P) = ∑_{i=1}^n f(ξ_i)(x_i − x_{i−1})
其中 ξ_i ∈ [x_{i−1}, x_i]。
- **对齐判定**: 严格等价
- **差异分析**: 项目文档明确给出了带样本点 ξ_i 的黎曼和定义，与课程教材一致。
- **修正建议**: 无需修正。

## 定义: Riemann integral
- **课程来源**: MIT 18.100A, Week 11: Taylor's Theorem and the Riemann Integral, Taylor expansion and Riemann integration, [JL] Section 4.3
- **课程定义**: A function f is Riemann integrable on [a, b] if there exists I ∈ ℝ such that for every ε > 0 there exists δ > 0 such that for every partition P with ||P|| < δ and every choice of sample points, |S(f, P) − I| < ε.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: **定义 3.1.13** (黎曼积分 / Riemann Integral)
函数 f 在 [a, b] 上黎曼可积，如果存在 I ∈ ℝ 使得：
∀ ε > 0, ∃ δ > 0, ∀ P, ||P|| < δ ⇒ |S(f, P) − I| < ε
其中 ||P|| = max_{1≤i≤n} (x_i − x_{i−1}) 是分割的范数。
- **对齐判定**: 近似表述
- **差异分析**: 项目文档的黎曼积分定义**缺少关键条件**：'对任意样本点 ξ_i 的选取'（for every choice of sample points）。虽然 S(f, P) 的表达式中出现了 ξ_i，但定义 3.1.13 的量化语句中未显式要求该不等式对所有可能的 ξ_i 选取成立。在严格性要求下，这是一个逻辑条件不完整的问题。
- **修正建议**: 建议修正为：'函数 f 在 [a, b] 上黎曼可积，如果存在 I ∈ ℝ 使得：∀ ε > 0, ∃ δ > 0, 对 [a, b] 的任意分割 P 满足 ||P|| < δ 以及任意选取的样本点 ξ_i ∈ [x_{i−1}, x_i]，都有 |S(f, P) − I| < ε。'

## 定义: Pointwise convergence of sequences of functions
- **课程来源**: MIT 18.100A, Week 12: Fundamental Theorem of Calculus and Sequences of Functions, FTC and convergence of functions, [JL] Section 6.1
- **课程定义**: A sequence of functions (f_n) converges pointwise to f on S if for every x ∈ S, lim_{n→∞} f_n(x) = f(x). That is, ∀x∈S, ∀ε>0, ∃N∈ℕ such that ∀n≥N, |f_n(x)−f(x)|<ε.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档中未找到'点态收敛'或'pointwise convergence'的形式化定义。
- **对齐判定**: 缺失
- **差异分析**: 项目文档完全缺失函数列点态收敛的定义。
- **修正建议**: P0：在级数/函数列章节中补充点态收敛的 ε-N 定义。

## 定义: Uniform convergence of sequences of functions
- **课程来源**: MIT 18.100A, Week 12: Fundamental Theorem of Calculus and Sequences of Functions, FTC and convergence of functions, [JL] Section 6.1
- **课程定义**: A sequence of functions (f_n) converges uniformly to f on S if for every ε > 0 there exists N ∈ ℕ such that for all n ≥ N and all x ∈ S, |f_n(x) − f(x)| < ε.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 主文档 `01-实分析.md` 中未找到一致收敛的形式化定义。虽然在思维导图文档 `docs/visualizations/思维导图/概念/分析学/一致收敛.md` 中有精确定义，但该路径并非 D006 指定的 formal_math_path。
- **对齐判定**: 缺失
- **差异分析**: 根据任务要求，以 D006 指定的 `docs/03-分析学/01-实分析/01-实分析.md` 为准，该文档中不存在一致收敛的定义。
- **修正建议**: P0：在主文档中补充一致收敛的定义，或更新 D006 中的 formal_math_path 以指向已包含定义的 visualization 文档。

## 定义: Power series
- **课程来源**: MIT 18.100A, Week 13: Uniform Convergence, Power Series, and Approximation, Advanced convergence and approximation, [JL] Sections 6.1 and 6.2
- **课程定义**: A power series (centered at 0) is a series of the form ∑_{n=0}^∞ a_n x^n for real coefficients a_n and variable x ∈ ℝ.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档在'概念深度分析：级数'的'直接外延'中提到：'幂级数：形如 ∑_{n=0}^∞ a_n x^n 的级数'。这是一个描述性说明，而非 Definition 块。
- **对齐判定**: 近似表述
- **差异分析**: 项目文档将幂级数作为级数的一种'直接外延'（实例类型）呈现，而非正式的数学定义块。
- **修正建议**: 建议将幂级数提升为正式定义：'形如 ∑ a_n (x − c)^n 的级数称为以 c 为中心的幂级数。'

## 定义: Radius of convergence
- **课程来源**: MIT 18.100A, Week 13: Uniform Convergence, Power Series, and Approximation, Advanced convergence and approximation, [JL] Sections 6.1 and 6.2
- **课程定义**: The radius of convergence R of a power series ∑ a_n x^n is R = 1 / limsup_{n→∞} |a_n|^{1/n} (with conventions R = 0 or R = ∞ when appropriate). The series converges absolutely for |x| < R and diverges for |x| > R.
- **项目对应路径**: `docs/03-分析学/01-实分析/01-实分析.md`
- **项目中的表述**: 文档中仅在知识矩阵中出现'收敛半径'一词，没有给出 Cauchy-Hadamard 公式或任何等价定义。
- **对齐判定**: 缺失
- **差异分析**: 项目文档缺少收敛半径的形式化定义。
- **修正建议**: P1：补充收敛半径的 Cauchy-Hadamard 定义或比值/根值判定关联定义。

---

## 统计汇总

| 指标 | 数量 | 百分比 |
|:-----|-----:|-------:|
| 总定义数 | 44 | 100.0% |
| 严格等价 | 11 | 25.0% |
| 近似表述 | 8 | 18.2% |
| 缺失 | 25 | 56.8% |

### 需要新建/补充的概念文档清单（按优先级）

**P0（核心定义，必须在下一迭代补齐）**：
1. Union, intersection, complement
2. Power set
3. Injective, surjective, bijective functions
4. Cardinality (size) of sets
5. Countable set
6. Archimedean property
7. Density of ℚ in ℝ
8. Absolute value
9. Triangle inequality
10. Subsequence
11. Monotone sequence
12. Limit superior (limsup)
13. Limit inferior (liminf)
14. Cauchy sequence
15. Absolute convergence
16. Conditional convergence
17. Cluster point (accumulation point)
18. Sequential criterion for limits
19. Uniform continuity
20. Lipschitz continuity
21. Relative (local) maximum and minimum
22. Taylor polynomial
23. Pointwise convergence of sequences of functions
24. Uniform convergence of sequences of functions
25. Radius of convergence

**GAP-3（近似表述，需要修正）**：
1. Field
2. Ordered field
3. Least upper bound (supremum)
4. Greatest lower bound (infimum)
5. p-series
6. Dirichlet function
7. Riemann integral
8. Power series
