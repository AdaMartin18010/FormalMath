---
course: Princeton-复分析

title: "Riemann面（Riemann Surfaces）"
level: "silver"
msc_primary: 30
target_courses:
  - "Princeton 复分析 Ch.6"
references:
  textbooks:
    - title: "Complex Analysis"
      author: "Elias M. Stein & Rami Shakarchi"
      edition: "1st"
      chapters: "Ch. 8"
      pages: "205-237"
    - title: "Functions of One Complex Variable I"
      author: "John B. Conway"
      edition: "2nd"
      chapters: "Ch. 6"
      pages: "120-138"
  lectures:
    - institution: "Princeton"
      course_code: "MAT 335"
      lecture: "Lecture 16-18"
      url: "https://web.math.princeton.edu/"
keywords:
  - "Riemann面"
  - "复流形"
  - "全纯映射"
  - "分歧覆盖"
  - "亏格"
  - "代数曲线"
review_status: "completed"
review_rounds: 0
created_at: "2026-04-18"
---

# Riemann面（Riemann Surfaces）

> **课程**: Princeton 复分析 | **章节**: Ch. 6 — Riemann 面的基本概念
> **学习目标**: 理解 Riemann 面的定义与基本例子；掌握全纯映射在 Riemann 面之间的推广；了解 Riemann-Hurwitz 公式与亏格的概念

---

## 一、核心定义

### 定义 7.1（Riemann 面 / Riemann Surface）

**严格陈述**: 一个 **Riemann 面** 是一个连通的 Hausdorff 拓扑空间 \(X\)，配备一个**复图册**（complex atlas）\(\{(U_\alpha, \varphi_\alpha)\}_{\alpha \in A}\)，满足：

1. \(\{U_\alpha\}\) 是 \(X\) 的开覆盖；
2. 每个 \(\varphi_\alpha: U_\alpha \to \mathbb{C}\) 是同胚（映到 \(\mathbb{C}\) 的开子集）；
3. **全纯相容性**：对任意 \(\alpha, \beta\)，转移函数
   $$\varphi_\beta \circ \varphi_\alpha^{-1}: \varphi_\alpha(U_\alpha \cap U_\beta) \to \varphi_\beta(U_\alpha \cap U_\beta)$$
   是全纯的。

**直观解释**: Riemann 面是"一维复流形"——局部上看起来就像复平面的一小块，但整体拓扑可以很复杂。复平面的开子集、Riemann 球面 \(\hat{\mathbb{C}} = \mathbb{C} \cup \{\infty\}\)、环面都是 Riemann 面。Riemann 面是研究多值复函数（如 \(\sqrt{z}\)、\(\log z\)）的自然定义域：通过在不同的"层"（sheet）上定义函数的单值分支，并将它们适当地粘合起来，多值函数就变成了 Riemann 面上的单值全纯函数。

---

### 定义 7.2（全纯映射 / Holomorphic Map）

**严格陈述**: 设 \(X, Y\) 为 Riemann 面。映射 \(f: X \to Y\) 称为**全纯的**（holomorphic），若对任意 \(p \in X\)，存在 \(p\) 处的坐标卡 \((U, \varphi)\) 和 \(f(p)\) 处的坐标卡 \((V, \psi)\)，使得局部表示

$$\psi \circ f \circ \varphi^{-1}: \varphi(U \cap f^{-1}(V)) \to \mathbb{C}$$

是全纯的。双射且双方全纯的映射称为**双全纯映射**（biholomorphic）或**同构**（isomorphism）。

**直观解释**: 全纯映射是复分析中全纯函数概念在 Riemann 面上的自然推广。定义不依赖于坐标卡的选取——若在一个坐标卡下局部表示全纯，则在所有相容的坐标卡下都全纯。这一"坐标无关性"是流形理论的精髓。

---

### 定义 7.3（分歧点与分歧覆盖 / Ramification）

**严格陈述**: 设 \(f: X \to Y\) 为 Riemann 面之间的非常值全纯映射。对 \(p \in X\)，存在坐标卡使得 \(f\) 的局部表示为 \(z \mapsto z^n\)（\(n \geq 1\)）。称 \(n\) 为 \(f\) 在 \(p\) 处的**重数**（multiplicity）或**分歧指数**（ramification index），记 \(e_p = n\)。若 \(e_p > 1\)，称 \(p\) 为**分歧点**（ramification point），\(f(p)\) 为**分歧值**（branch point）。

**直观解释**: 分歧点是映射"折叠"的地方。例如 \(f(z) = z^2\) 将单位圆盘映到自身，在原点 \(z = 0\) 处 \(e_0 = 2\)——两个不同的点 \(z\) 和 \(-z\) 被映射到同一个像 \(z^2\)。分歧覆盖是多对一的全纯映射，是研究 Riemann 面之间关系的核心工具。

> **双语对照**:
>
> ```lean4
> import Mathlib
>
> -- Riemann 面的局部坐标卡
> structure ComplexChart (X : Type*) [TopologicalSpace X] where
>   U : Opens X
>   φ : U → ℂ
>   φ_embedding : IsEmbedding φ
>   φ_open : IsOpenMap φ
>
> -- 复图册：全纯相容的坐标卡集合
> structure ComplexAtlas (X : Type*) [TopologicalSpace X] where
>   charts : Set (ComplexChart X)
>   covers : ⋃ (c ∈ charts), (c.U : Set X) = Set.univ
>   holomorphic_transition : ∀ c₁ c₂ ∈ charts,
>     AnalyticOn ℂ (c₂.φ ∘ c₁.φ.symm) (c₁.φ '' (c₁.U ∩ c₂.U))
>
> -- 全纯映射
> def HolomorphicMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
>   (A_X : ComplexAtlas X) (A_Y : ComplexAtlas Y) (f : X → Y) : Prop :=
>   ∀ x : X, ∃ c_X ∈ A_X.charts, ∃ c_Y ∈ A_Y.charts,
>     x ∈ c_X.U ∧ f x ∈ c_Y.U ∧
>     AnalyticOn ℂ (c_Y.φ ∘ f ∘ c_X.φ.symm)
>       (c_X.φ '' (c_X.U ∩ f ⁻¹' c_Y.U))
> ```

---

## 二、核心定理与完整证明

### 定理 7.1（紧 Riemann 面的亏格公式）

**定理陈述**: 设 \(X\) 为紧 Riemann 面，\(f: X \to \hat{\mathbb{C}}\) 为非常值亚纯函数，\(n = \deg(f)\) 为映射的次数（即一般点上的原像个数）。设 \(R = \sum_{p \in X} (e_p - 1)\) 为总分歧数。则 \(X\) 的拓扑亏格 \(g\) 满足 **Riemann-Hurwitz 公式**：

$$2g - 2 = -2n + R.$$

**证明思路**:

将 \(f\) 视为拓扑空间的 \(n\)-叶分歧覆盖。对 \(f\) 的每个分歧值 \(q_j\)，设其原像为 \(p_{j,1}, \ldots, p_{j,k_j}\)，重数分别为 \(e_{j,1}, \ldots, e_{j,k_j}\)。则 \(\sum_{i} e_{j,i} = n\)。

三角剖分 \(\hat{\mathbb{C}}\) 使得所有分歧值都是顶点。设该剖分有 \(V\) 个顶点、\(E\) 条边、\(F\) 个面。则 \(\hat{\mathbb{C}}\) 的 Euler 示性数为 \(V - E + F = 2\)。

将剖分提升到 \(X\)。每个非分歧点上有 \(n\) 个原像，每个分歧点 \(p\) 处有 \(e_p\) 个"局部层"合并。提升后的剖分满足

$$V_X = nV - \sum_{p} (e_p - 1), \quad E_X = nE, \quad F_X = nF.$$

（每个分歧值减少了 \(\sum (e_p - 1)\) 个顶点的提升）。因此

$$\chi(X) = V_X - E_X + F_X = n(V - E + F) - \sum_{p}(e_p - 1) = 2n - R.$$

由 \(\chi(X) = 2 - 2g\)，整理得 \(2g - 2 = -2n + R\)。\(\square\)

> **证明要点提示**:
>
> 1. **Euler 示性数的提升**: Riemann-Hurwitz 公式的核心是分歧覆盖下 Euler 示性数的变化规律。每个分歧点"减少"了 \(e_p - 1\) 个提升的顶点。
> 2. **亏格的代数意义**: 亏格 \(g\) 是紧 Riemann 面的最核心不变量。\(g = 0\) 时 \(X \cong \hat{\mathbb{C}}\)；\(g = 1\) 时 \(X\) 为环面（椭圆曲线）。

---

### 定理 7.2（开映射定理）

**定理陈述**: 设 \(f: X \to Y\) 为 Riemann 面之间的非常值全纯映射。则 \(f\) 是**开映射**：将 \(X\) 的开集映为 \(Y\) 的开集。

**证明**: 全纯函数的局部标准形式为 \(z \mapsto z^n\)（\(n \geq 1\)）。映射 \(z \mapsto z^n\) 将开集映为开集（因为非零复数的 \(n\) 次根存在，且 \(0\) 附近的小圆盘映为小圆盘）。由坐标卡的相容性，\(f\) 在开集上每一点附近都是开的，从而整体为开映射。\(\square\)

---

## 三、习题

### 习题 7.1

**题目**: 证明 Riemann 球面 \(\hat{\mathbb{C}} = \mathbb{C} \cup \{\infty\}\) 是紧 Riemann 面，并给出其标准图册。

**提示**: 用两个坐标卡覆盖：\(U_1 = \mathbb{C}\)（坐标 \(z\)）和 \(U_2 = \hat{\mathbb{C}} \setminus \{0\}\)（坐标 \(w = 1/z\)）。

**解答**: 

- \(U_1 = \mathbb{C}\)，\(\varphi_1(z) = z\)。
- \(U_2 = \hat{\mathbb{C}} \setminus \{0\}\)，\(\varphi_2(z) = 1/z\)（\(\varphi_2(\infty) = 0\)）。

转移函数：在 \(U_1 \cap U_2 = \mathbb{C} \setminus \{0\}\) 上，

$$\varphi_2 \circ \varphi_1^{-1}(z) = \frac{1}{z},$$

在 \(\mathbb{C} \setminus \{0\}\) 上全纯。\(\hat{\mathbb{C}}\) 作为拓扑空间同胚于二维球面 \(S^2\)，故紧致。\(\square\)

---

### 习题 7.2

**题目**: 构造 \(\sqrt{z}\) 的 Riemann 面，并证明它双全纯等价于 \(\mathbb{C} \setminus \{0\}\)。

**提示**: 用两层 \(\mathbb{C}\) 沿正实轴剪开后交叉粘合。

**解答**: 取两个 \(\mathbb{C}\) 的拷贝 \(S_1, S_2\)，各沿正实轴剪开。在 \(S_1\) 的上岸（辐角 \(0^+\)）粘合到 \(S_2\) 的下岸（辐角 \(2\pi^-\)），\(S_1\) 的下岸粘合到 \(S_2\) 的上岸。所得空间 \(X\) 上自然定义 \(\sqrt{z}\)：在 \(S_1\) 上用主分支（辐角 \((0, 2\pi)\)），在 \(S_2\) 上用另一分支（辐角 \((2\pi, 4\pi)\)）。映射 \(w = \sqrt{z}\) 建立了 \(X\) 与 \(\mathbb{C} \setminus \{0\}\) 之间的双全纯等价（\(z = w^2\)）。\(\square\)

---

### 习题 7.3

**题目**: 设 \(X\) 为紧 Riemann 面，\(f: X \to \hat{\mathbb{C}}\) 为非常值全纯映射。证明 \(f\) 必为满射。

**提示**: 用开映射定理和紧性。

**解答**: \(X\) 紧致且 \(f\) 连续，故 \(f(X)\) 为 \(\hat{\mathbb{C}}\) 的紧子集，从而是闭集。由开映射定理，\(f(X)\) 也是开集。\(\hat{\mathbb{C}}\) 连通，故非空既开又闭的子集必为整个 \(\hat{\mathbb{C}}\)。因此 \(f(X) = \hat{\mathbb{C}}\)。\(\square\)

---

### 习题 7.4

**题目**: 证明任何紧 Riemann 面上的亚纯函数都是有理函数（当 \(X = \hat{\mathbb{C}}\) 时），并说明对一般紧 Riemann 面不成立。

**提示**: 对 \(X = \hat{\mathbb{C}}\)，已在定理 6.1 中证明。对环面，Weierstrass \(\wp\)-函数是亚纯但非有理的函数。

**解答**: \(X = \hat{\mathbb{C}}\) 时已证（定理 6.1）。对环面 \(X = \mathbb{C}/\Lambda\)（\(\Lambda\) 为格），Weierstrass \(\wp\)-函数

$$\wp(z) = \frac{1}{z^2} + \sum_{\omega \in \Lambda \setminus \{0\}} \left(\frac{1}{(z-\omega)^2} - \frac{1}{\omega^2}\right)$$

在 \(X\) 上亚纯，但不是任何有理函数（因它在周期格上双周期）。\(\square\)

---

### 习题 7.5

**题目**: 计算映射 \(f(z) = z^n\)（\(n \geq 2\)）从 \(\hat{\mathbb{C}}\) 到 \(\hat{\mathbb{C}}\) 的分歧指数和总分歧数，并验证 Riemann-Hurwitz 公式。

**提示**: 分歧点在 \(z = 0\) 和 \(z = \infty\)。

**解答**: \(\deg(f) = n\)。在 \(z = 0\)，局部表示为 \(z \mapsto z^n\)，故 \(e_0 = n\)。在 \(z = \infty\)，令 \(w = 1/z\)，则 \(f = w^{-n}\)，故 \(e_\infty = n\)。其他点 \(e_p = 1\)。

总分歧数 \(R = (n-1) + (n-1) = 2n - 2\)。Riemann-Hurwitz 公式：

$$2g_X - 2 = -2n + R = -2n + (2n - 2) = -2.$$

故 \(g_X = 0\)，符合 \(\hat{\mathbb{C}}\) 的亏格。\(\square\)

---

## 四、Lean4 形式化框架

```lean4
import Mathlib

-- Riemann 面的定义（一维复流形）
structure RiemannSurface (X : Type*) [TopologicalSpace X]
  [ChartedSpace ℂ X] where
  atlas : Set (PartialHomeomorph X ℂ)
  chart_mem : ∀ x : X, ∃ c ∈ atlas, x ∈ c.source
  holomorphic_transition : ∀ c₁ c₂ ∈ atlas,
    AnalyticOn ℂ (c₂ ∘ c₁.symm) (c₁.target ∩ c₁.symm ⁻¹' c₂.source)

-- 紧 Riemann 面的亏格
def genus {X : Type*} [TopologicalSpace X] [CompactSpace X]
  (RS : RiemannSurface X) : ℕ :=
  -- Euler 示性数 χ = 2 - 2g
  (2 - EulerCharacteristic X) / 2
```

---

## 五、参考文献

1. Elias M. Stein & Rami Shakarchi, *Complex Analysis*, Princeton University Press, 2003. Ch. 8.
2. Otto Forster, *Lectures on Riemann Surfaces*, Springer, 1981. Ch. 1–2.
3. Simon Donaldson, *Riemann Surfaces*, Oxford University Press, 2011. Ch. 1–3.

---

## 相关文档

- [05-共形映射](05-共形映射.md)
- [06-整函数与亚纯函数](06-整函数与亚纯函数.md)
- [01-复数与解析函数](01-复数与解析函数.md)
- [Taylor定理](../MIT-18.100A-实分析/Taylor定理.md)

**文档状态**: 🟢 已完成 | **审校轮次**: 0/2
**最后更新**: 2026-04-18

## 交叉引用

- [相关: ANA-001-序列极限四则运算](../00-习题示例反例库/实分析/ANA-001-序列极限四则运算.md)
- [相关: 01-拓扑空间](../00-知识层次体系/L1-形式化定义层/05-拓扑学基础/01-拓扑空间.md)
