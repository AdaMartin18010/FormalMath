---
course: Harvard 232br 代数几何

title: "Harvard 232br - Hartshorne Chapter IV §1–§4 习题解答"
course_code: "Harvard Math 232br"
textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
source_textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
source_chapter: "Chapter IV - Curves, Sections 1–4"
source_exercise:
  - "IV.1.1"
  - "IV.1.2"
  - "IV.1.3"
  - "IV.2.1"
  - "IV.2.2"
  - "IV.3.1"
  - "IV.3.2"
  - "IV.4.1"
  - "IV.4.2"
difficulty: ⭐⭐⭐ to ⭐⭐⭐⭐
processed_at: '2026-04-18'
level: "silver"
target_courses:
  - "Harvard 232br"
msc_primary: 14

references:
  textbooks:
    - id: hartshorne_ag
      type: textbook
      title: Algebraic Geometry
      authors:
        - Robin Hartshorne
      publisher: Springer
      edition: 1st
      year: 1977
      isbn: 978-0387902449
      msc: 14-01
      chapters: ["IV.1", "IV.2", "IV.3", "IV.4"]
      url: ~
    - id: vakil_foag
      type: textbook
      title: Foundations of Algebraic Geometry
      authors:
        - Ravi Vakil
      publisher: self-published
      edition: draft
      year: 2024
      msc: 14-01
      url: "https://math.stanford.edu/~vakil/216blog/"
  databases:
    - id: stacks_project
      type: database
      name: Stacks Project
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
      consulted_at: 2026-04-18
review_status: "draft"
created_at: 2026-04-18
---

# Harvard 232br — Hartshorne Chapter IV §1–§4 习题解答

> 本节覆盖 Hartshorne 第四章第 1–4 节的核心习题，涉及曲线的基本理论：次数-亏格关系、Hurwitz 分歧公式、典范嵌入与椭圆曲线的群结构。除非特别说明，$k$ 均表示代数闭域，曲线指 $k$ 上的非奇异射影曲线。

---

## 习题 IV.1.1 — 曲线的低次有理函数存在性

### 题号与精确引用

**Hartshorne IV.1.1**

### 问题重述

设 $X$ 为亏格 $g$ 的曲线。证明存在非零有理函数 $f \in K(X)$，使得 $\deg(f) \leq g+1$。等价地，证明 $X$ 上存在一个次数不超过 $g+1$ 的 $g^1_d$（一维线性系）。

### 详细解答

**Step 1: 选取适当的除子**

取 $X$ 上 $g+2$ 个互不相同的点 $P_1, \dots, P_{g+2} \in X$。考虑除子 $D = P_1 + \dots + P_{g+2}$，其次数为 $\deg(D) = g+2$。

**Step 2: 应用 Riemann-Roch 定理**

由 Riemann-Roch 定理（Hartshorne IV.1.3，**定理 1.3**）：对任意除子 $D$ 有
$$\ell(D) - \ell(K - D) = \deg(D) + 1 - g.$$

这里 $\deg(D) = g+2$，故
$$\ell(D) - \ell(K - D) = (g+2) + 1 - g = 3.$$

因此 $\ell(D) \geq 3$（因为 $\ell(K-D) \geq 0$）。

**Step 3: 构造低次有理函数**

$\ell(D) \geq 3$ 意味着线性系 $|D|$ 的维数至少为 2。考虑 $D' = D - P_{g+2} = P_1 + \dots + P_{g+1}$，其次数为 $g+1$。

由 Riemann-Roch，
$$\ell(D') - \ell(K - D') = (g+1) + 1 - g = 2.$$

故 $\ell(D') \geq 2$。取 $f \in L(D') \setminus k$（存在因为 $\ell(D') \geq 2 > 1$），则 $(f) + D' \geq 0$，即 $f$ 的极点被 $D'$ 控制，因此 $\deg(f) \leq \deg(D') = g+1$。∎

**替代论证（更直接）**

取 $r \geq g+2$ 个不同的点 $P_1, \dots, P_r$。由 Riemann-Roch，$\ell(P_1 + \dots + P_r) = r + 1 - g \geq 3$。于是存在非常值函数 $f$ 仅以这些点为极点。若 $f$ 在所有 $P_i$ 处都无极点，则 $f \in H^0(X, \mathcal{O}_X) = k$，矛盾。故 $f$ 至少在一个 $P_i$ 处有极点。取 $r = g+2$，我们可以逐步去掉一个点直到极点次数不超过 $g+1$ 而函数仍非常值。

### 关键概念提示

- **$g^1_d$** 表示 $X$ 上次数为 $d$、维数为 1 的线性系（即一个到 $\mathbb{P}^1$ 的 $d$ 次态射）。
- **Riemann-Roch 定理** 是曲线理论的核心工具；它将空间的维数与除子的次数、曲线的亏格联系起来。
- 本题说明**任意曲线都可表示为 $\mathbb{P}^1$ 的有限覆盖**，且覆盖次数可被亏格控制。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 认为 $\ell(D) \geq 2$ 直接给出 $|D|$ 的维数 $\geq 1$ | 正确：$\dim|D| = \ell(D) - 1$，故 $\ell(D) \geq 2$ 当且仅当 $|D|$ 非空且维数至少 1。 |
| 忽略 $k$ 代数闭的条件 | Riemann-Roch 在任意域上成立，但 $L(D)$ 作为 $k$-向量空间的维数需要 $k$ 代数闭才能直接读出奇点个数。 |
| 混淆 $\deg(f)$ 与 $\deg((f)_\infty)$ | 对有理函数 $f$，$\deg(f) := \deg((f)_\infty) = \deg((f)_0)$，即极点除子（或零点除子）的次数。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Curves.RiemannRoch

open AlgebraicGeometry Scheme

-- 任意亏格 g 的曲线 X 上存在次数 ≤ g+1 的非常值有理函数
variable {k : Type*} [Field k] [IsAlgClosed k]
variable {X : Scheme} [IsCurve X] [IsProjective X] [IsNonsingular X]

-- 亏格定义
noncomputable def genus (X : Scheme) [IsCurve X] : ℕ :=
  sorry -- 通常定义为 dim H^0(X, Ω_X^1)

-- 存在低次有理函数（Riemann-Roch 推论）
theorem exists_low_degree_function (g : ℕ) (hg : genus X = g) :
    ∃ (f : X.functionField), f ≠ 0 ∧ f.deg ≤ g + 1 :=
  sorry
```

---

## 习题 IV.1.2 — 平面曲线的次数-亏格公式

### 题号与精确引用

**Hartshorne IV.1.2**

### 问题重述

设 $X \subset \mathbb{P}^2$ 为 $k$ 上次数 $d \geq 1$ 的非奇异平面曲线。证明 $X$ 的亏格为
$$g = \frac{(d-1)(d-2)}{2}.$$

### 详细解答

**Step 1: 利用伴随公式 (Adjunction Formula)**

由 Hartshorne II.8.20（或 V.1.5.1，曲面上的伴随公式），对 $\mathbb{P}^2$ 中的非奇异曲线 $X$ 有
$$\omega_X \cong \omega_{\mathbb{P}^2} \otimes \mathcal{O}(X)|_X.$$

**Step 2: 计算 $\omega_{\mathbb{P}^2}$ 与 $\mathcal{O}(X)$**

已知 $\omega_{\mathbb{P}^2} \cong \mathcal{O}_{\mathbb{P}^2}(-3)$（Hartshorne II.8.2）。

$X$ 是次数 $d$ 曲线，故 $\mathcal{O}(X) \cong \mathcal{O}_{\mathbb{P}^2}(d)$。

因此
$$\omega_X \cong \mathcal{O}_{\mathbb{P}^2}(-3) \otimes \mathcal{O}_{\mathbb{P}^2}(d)|_X = \mathcal{O}_X(d-3).$$

**Step 3: 计算 $H^0(X, \omega_X)$ 的维数**

$$g = h^0(X, \omega_X) = h^0(X, \mathcal{O}_X(d-3)).$$

由短正合列
$$0 \longrightarrow \mathcal{O}_{\mathbb{P}^2}(-d) \longrightarrow \mathcal{O}_{\mathbb{P}^2} \longrightarrow \mathcal{O}_X \longrightarrow 0$$

扭变 $\mathcal{O}(d-3)$ 得
$$0 \to \mathcal{O}_{\mathbb{P}^2}(-3) \to \mathcal{O}_{\mathbb{P}^2}(d-3) \to \mathcal{O}_X(d-3) \to 0.$$

取上同调，注意到 $H^0(\mathbb{P}^2, \mathcal{O}(-3)) = 0$（负次数），以及
$$H^0(\mathbb{P}^2, \mathcal{O}(d-3)) = \binom{d-1}{2} = \frac{(d-1)(d-2)}{2}$$
（当 $d \geq 3$；$d = 1, 2$ 时公式给出 $g = 0$，与事实一致）。

又 $H^1(\mathbb{P}^2, \mathcal{O}(-3)) = 0$（由 $\mathbb{P}^n$ 的上同调标准结果）。故
$$H^0(X, \mathcal{O}_X(d-3)) \cong H^0(\mathbb{P}^2, \mathcal{O}(d-3))$$

维数为 $\binom{d-1}{2} = \frac{(d-1)(d-2)}{2}$。∎

**验证低次情形**

- $d = 1$：$X \cong \mathbb{P}^1$，$g = 0$。公式给出 $(0)(-1)/2 = 0$。✓
- $d = 2$：$X \cong \mathbb{P}^1$（圆锥曲线同构于 $\mathbb{P}^1$），$g = 0$。公式给出 $(1)(0)/2 = 0$。✓
- $d = 3$：椭圆曲线，$g = 1$。公式给出 $(2)(1)/2 = 1$。✓
- $d = 4$：$g = 3$。公式给出 $(3)(2)/2 = 3$。✓

### 关键概念提示

- **伴随公式** 是计算曲线（或高维子簇）典范丛的核心工具。
- $\omega_{\mathbb{P}^n} \cong \mathcal{O}(-n-1)$ 是射影空间上同调计算的基石。
- 次数-亏格公式说明：平面曲线中，**亏格完全由次数决定**。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 直接断言 $h^0(X, \mathcal{O}_X(m)) = h^0(\mathbb{P}^2, \mathcal{O}(m))$ | 必须通过上同调长正合列验证 $H^1$ 项消失。 |
| 混淆 $\omega_X$ 与 $\Omega_X^1$ | 对曲线，二者相同；但对一般维数，$\omega_X = \det \Omega_X^1$（对非奇异簇）。 |
| 忽略 $d < 3$ 的验证 | 公式对所有 $d \geq 1$ 成立，但组合数 $\binom{d-1}{2}$ 在 $d=1,2$ 时需理解为 0。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Curves.Genus

open AlgebraicGeometry Scheme Projective

-- 次数 d 非奇异平面曲线的亏格公式
variable {k : Type*} [Field k] [IsAlgClosed k]

-- 将次数 d 平面曲线实现为 Proj(k[x,y,z]/(F))，其中 deg F = d
theorem plane_curve_genus (d : ℕ) (hd : d ≥ 1)
    (X : Scheme) [IsNonsingular X] (hX : X ≅ Proj (MvPolynomial (Fin 3) k ⧸ Ideal.span {F})) :
    genus X = (d - 1) * (d - 2) / 2 :=
  sorry
```

---

## 习题 IV.1.3 — 算术亏格与几何亏格

### 题号与精确引用

**Hartshorne IV.1.3**

### 问题重述

设 $X$ 为代数闭域 $k$ 上的非奇异射影曲线。证明 $X$ 的算术亏格 $p_a(X)$ 等于几何亏格 $p_g(X)$。更一般地，证明对任意射影曲线 $X$（允许奇异），有 $p_a(X) \geq p_g(X)$，且等号成立当且仅当 $X$ 非奇异。

### 详细解答

**Step 1: 回顾定义**

由 Hartshorne 第 III 章，对 $n$ 维射影簇 $X$，

- **算术亏格**：$p_a(X) = (-1)^n (\chi(\mathcal{O}_X) - 1)$。
  对曲线（$n=1$），$p_a(X) = 1 - \chi(\mathcal{O}_X) = 1 - h^0(X, \mathcal{O}_X) + h^1(X, \mathcal{O}_X)$。

- **几何亏格**：$p_g(X) = \dim_k H^0(X, \omega_X)$。
  对非奇异曲线，由 Serre 对偶（Hartshorne III.7），$H^1(X, \mathcal{O}_X) \cong H^0(X, \omega_X)^\vee$，故 $h^1(\mathcal{O}_X) = h^0(\omega_X) = p_g(X)$。

**Step 2: 非奇异曲线的情形**

设 $X$ 非奇异射影曲线。则 $X$ 连通（射影整曲线自动连通），故 $h^0(X, \mathcal{O}_X) = 1$。于是
$$p_a(X) = 1 - 1 + h^1(\mathcal{O}_X) = h^1(\mathcal{O}_X).$$

由 Serre 对偶，$h^1(\mathcal{O}_X) = h^0(\omega_X) = p_g(X)$。故
$$p_a(X) = p_g(X).$$

**Step 3: 一般射影曲线的比较**

设 $X$ 为任意射影曲线（可能有奇点）。设 $\pi: \tilde{X} \to X$ 为正规化（即非奇异模型）。由 Zariski 主定理，$\pi$ 是有限双有理态射。

有正合列（Hartshorne III.7，或 IV.1 的习题推导）：
$$0 \longrightarrow \mathcal{O}_X \longrightarrow \pi_* \mathcal{O}_{\tilde{X}} \longrightarrow \bigoplus_{P \in X_{\text{sing}}} \mathcal{O}_{\tilde{X}, \pi^{-1}(P)} / \mathcal{O}_{X,P} \longrightarrow 0.$$

记 $\delta_P = \dim_k (\pi_* \mathcal{O}_{\tilde{X}})_P / \mathcal{O}_{X,P}$ 为点 $P$ 处的 $\delta$-不变量。

取 Euler 示性数：
$$\chi(\pi_* \mathcal{O}_{\tilde{X}}) = \chi(\mathcal{O}_X) + \sum_{P} \delta_P.$$

因 $\pi$ 有限，$\chi(\pi_* \mathcal{O}_{\tilde{X}}) = \chi(\mathcal{O}_{\tilde{X}})$。于是
$$1 - p_a(\tilde{X}) = 1 - p_a(X) + \sum_P \delta_P,$$

即
$$p_a(X) = p_a(\tilde{X}) + \sum_P \delta_P = p_g(\tilde{X}) + \sum_P \delta_P.$$

**Step 4: 几何亏格的定义与不等式**

对奇异曲线，几何亏格定义为 $p_g(X) := p_g(\tilde{X}) = h^0(\tilde{X}, \omega_{\tilde{X}})$。因此
$$p_a(X) = p_g(X) + \sum_P \delta_P \geq p_g(X).$$

等号成立当且仅当所有 $\delta_P = 0$，即 $\pi_* \mathcal{O}_{\tilde{X}} = \mathcal{O}_X$，这意味着 $X$ 本身已是非奇异的（正规化是同构）。∎

### 关键概念提示

- **算术亏格** 是内蕴的射影不变量（通过 Euler 示性数定义），而 **几何亏格** 需要非奇异模型。
- **正规化** $\tilde{X}$ 消除了奇点，但改变了环的局部结构；$\delta_P$ 度量了奇点的“严重程度”。
- 对平面曲线，$\delta_P$ 可用 Milnor 数与分支数计算（Plücker 公式）。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 对奇异曲线直接套用 Serre 对偶 | Serre 对偶要求 $X$ 是 Cohen-Macaulay 且 proper；对一般奇异曲线，$h^1(\mathcal{O}_X)$ 可能不等于 $h^0(\omega_X)$。 |
| 认为 $p_a = p_g$ 对所有曲线成立 | 仅对非奇异曲线成立；奇异曲线有 $p_a > p_g$。 |
| 混淆正规化与解消 | 曲线情形下二者一致（一维非奇异 = 正规），但对高维簇，解消要求更强。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Curves.DeltaInvariant

open AlgebraicGeometry Scheme

variable {k : Type*} [Field k] [IsAlgClosed k]

-- 算术亏格 ≥ 几何亏格，等号成立当且仅当非奇异
theorem arithmetic_genus_ge_geometric_genus (X : Scheme) [IsProjective X] [IsCurve X] :
    let p_a := arithmeticGenus X
    let p_g := geometricGenus X
    p_a ≥ p_g ∧ (p_a = p_g ↔ IsNonsingular X) :=
  sorry
```

---

## 习题 IV.2.1 — Hurwitz 分歧公式

### 题号与精确引用

**Hartshorne IV.2.1**

### 问题重述

设 $f: X \to Y$ 为曲线之间的有限可分态射，次数为 $n = \deg(f)$。设 $R = \sum_{P \in X} (e_P - 1) \cdot P$ 为分歧除子，其中 $e_P$ 是 $f$ 在 $P$ 处的分歧指数。证明 **Hurwitz 公式**：
$$2g(X) - 2 = n \cdot (2g(Y) - 2) + \deg(R).$$

若 $f$ 还是纯不可分的，讨论公式应如何修改。

### 详细解答

**Step 1: 分离情形的准备**

设 $f: X \to Y$ 有限可分，次数为 $n$。考虑 $f$ 诱导的典则层的拉回关系。

**Step 2: 典则层的比较**

由 Hartshorne IV.2，有层同态 $f^* \Omega_Y \to \Omega_X$。对曲线的有限态射，$\Omega_X$ 是 $f^* \Omega_Y$ 的秩 1 局部自由层的修正：

$$\Omega_X \cong f^* \Omega_Y \otimes \mathcal{O}_X(R).$$

这里 $R$ 是分歧除子。取次数：
$$\deg(\Omega_X) = \deg(f^* \Omega_Y) + \deg(R).$$

**Step 3: 计算各项次数**

- $\deg(\Omega_X) = 2g(X) - 2$（由 Riemann-Roch，$\deg(K_X) = 2g - 2$）。
- $\deg(f^* \Omega_Y) = n \cdot \deg(\Omega_Y) = n(2g(Y) - 2)$（拉回的次数 = 次数 $\times$ 原除子次数）。
- $\deg(R) = \sum_P (e_P - 1)$。

代入得
$$2g(X) - 2 = n(2g(Y) - 2) + \deg(R).$$

**Step 4: 分歧除子的精细结构（可选深化）**

在特征 0 或特征不整除 $e_P$ 时，分歧是**驯顺的**（tame），$R = \sum (e_P - 1)P$ 如上所述。

在特征 $p > 0$ 且 $p \mid e_P$ 时，分歧是**野性的**（wild），Hurwitz 公式需要修正。设 $D_P$ 为高阶分歧群（higher ramification groups），则
$$\deg(R) = \sum_P \sum_{i \geq 0} (|G_i(P)| - 1),$$
其中 $G_i(P)$ 是 $P$ 处的第 $i$ 个高阶分歧群。

对纯不可分态射 $f: X \to Y$（特征 $p > 0$），$f$ 可分解为相对 Frobenius 的迭代。此时不存在通常意义下的分歧指数；代之，$\Omega_{X/Y}$ 处处为零化，且 Hurwitz 公式退化为：存在 $q = p^r$ 使得 $g(X) = g(Y)$（因为 $X \cong Y^{(q)}$ 作为抽象曲线），但微分形式的行为完全不同。

### 关键概念提示

- **分歧指数** $e_P$：局部地，$f$ 在 $P$ 附近形如 $t \mapsto u \cdot s^{e_P}$，其中 $t$ 是 $Y$ 上 $Q = f(P)$ 附近的局部参数，$s$ 是 $X$ 上 $P$ 附近的局部参数，$u$ 是单位。
- **Hurwitz 公式** 是计算曲线覆盖的亏格的核心工具；它将拓扑信息（分歧）与代数信息（典范除子）联系起来。
- **驯顺/野性分歧** 的区别仅在正特征出现，是特征 $p$ 代数几何的微妙之处。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 在正特征下直接套用 $R = \sum (e_P - 1)P$ | 野性分歧时需要计入高阶分歧群的贡献。 |
| 混淆 $\Omega_X$ 与 $K_X$ | $K_X$ 是典则除子（等价类），$\Omega_X$ 是微分层；$\deg(\Omega_X) = \deg(K_X)$。 |
| 忽略 $f$ 可分的假设 | 不可分态射没有通常的分歧理论，典则丛的计算方法不同。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Curves.Hurwitz

open AlgebraicGeometry Scheme

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {X Y : Scheme} [IsCurve X] [IsCurve Y] [IsNonsingular X] [IsNonsingular Y]

-- Hurwitz 公式：有限可分态射的亏格-分歧关系
theorem hurwitz_formula {f : X ⟶ Y} [IsFinite f] [IsSeparable f]
    (n : ℕ) (hn : morphismDegree f = n) :
    2 * genus X - 2 = n * (2 * genus Y - 2) + (ramificationDivisor f).deg :=
  sorry
```

---

## 习题 IV.2.2 — 超椭圆曲线的分歧覆盖

### 题号与精确引用

**Hartshorne IV.2.2**

### 问题重述

设 $X$ 为亏格 $g \geq 2$ 的曲线。称 $X$ 为**超椭圆的**（hyperelliptic），若存在次数 2 的态射 $f: X \to \mathbb{P}^1$。证明：

(a) 若 $X$ 超椭圆，则 $f$ 恰有 $2g + 2$ 个分歧点（作为 $\mathbb{P}^1$ 上的除子计数），且 $f$ 由 $X$ 上的唯一 $g^1_2$ 决定（即若 $f': X \to \mathbb{P}^1$ 也是次数 2 的，则 $f' = \phi \circ f$ 对某个 $\phi \in \operatorname{Aut}(\mathbb{P}^1)$）。

(b) 反之，给定 $\mathbb{P}^1$ 上 $2g+2$ 个不同点 $a_1, \dots, a_{2g+2}$，构造亏格 $g$ 的超椭圆曲线 $X$ 为
$$y^2 = \prod_{i=1}^{2g+2} (x - a_i)$$
（或其射影完备化），并验证 $X$ 非奇异且到 $x$-轴的投影给出次数 2 态射 $X \to \mathbb{P}^1$。

### 详细解答

**(a) 超椭圆曲线的分歧点个数与唯一性**

**分歧点个数**：设 $f: X \to \mathbb{P}^1$ 次数为 2。在特征 $\neq 2$ 时，$f$ 是 Galois 覆盖（因为次数 2），分歧全是驯顺的。分歧除子 $R$ 满足 $\deg(R) = \sum_P (e_P - 1)$。因次数为 2，每个分歧点处 $e_P = 2$，故 $e_P - 1 = 1$。

由 Hurwitz 公式：
$$2g - 2 = 2(0 - 2) + \deg(R) = -4 + \deg(R).$$

于是 $\deg(R) = 2g + 2$。每个分歧点贡献 1，故恰有 $2g + 2$ 个分歧点。

**唯一性**：设 $f, f': X \to \mathbb{P}^1$ 均为次数 2。对应的线性系分别为 $|D|$ 和 $|D'|$，其中 $\deg(D) = \deg(D') = 2$，$\ell(D) = \ell(D') = 2$。

由 Riemann-Roch，$\ell(K - D) = g - 1 > 0$（因 $g \geq 2$），故 $D$ 是特殊的。类似地 $D'$ 也是特殊的。

对超椭圆曲线，$|K_X|$ 是从 $g^1_2$ 拉回的（Hartshorne IV.5）。实际上，典范除子 $K$ 满足 $K \sim (g-1)D$（因典范映射经过二次曲线）。若有两个不同的 $g^1_2$，则它们给出两个到 $\mathbb{P}^1$ 的不同态射；但 $|K|$ 只有一个到 $\mathbb{P}^{g-1}$ 的典范映射，且对超椭圆曲线，这个映射分解为 $X \xrightarrow{f} \mathbb{P}^1 \xrightarrow{\nu} \mathbb{P}^{g-1}$，其中 $\nu$ 是 $(g-1)$-重 Veronese 嵌入。若有两个不同的 $f$，则 $\nu \circ f = \nu \circ f'$，由 $\nu$ 是嵌入（在像上），得 $f = f'$ 在相差 $\operatorname{Aut}(\mathbb{P}^1)$ 的意义下唯一。

**(b) 由分支点构造超椭圆曲线**

在仿射平面 $\mathbb{A}^2$ 中考虑曲线
$$C: \; y^2 = \prod_{i=1}^{2g+2} (x - a_i).$$

**非奇异性**：在 $y \neq 0$ 的点，$\partial/\partial y = 2y \neq 0$，故由隐函数定理，这些点非奇异。

在 $y = 0$ 的点，必有某个 $x = a_i$。此时 $\partial/\partial x = \prod_{j \neq i} (a_i - a_j) \neq 0$（因为 $a_i$ 互不相同），故这些点也非奇异。

在无穷远点：作射影化。令 $x = X/Z$，$y = Y/Z$，得
$$Y^2 Z^{2g} = \prod_{i=1}^{2g+2} (X - a_i Z).$$

无穷远点是 $Z = 0$，此时方程变为 $Y^2 Z^{2g} = X^{2g+2}$，即 $Z = 0$ 时 $X = 0$（若 $g \geq 1$），唯一无穷远点为 $[0:1:0]$（齐次坐标 $[X:Y:Z]$）。在此点，令 $u = X/Y$，$v = Z/Y$，方程变为
$$v^{2g} = \prod_{i=1}^{2g+2} (u - a_i v).$$

在 $(u, v) = (0, 0)$，右边 $= u^{2g+2} + \cdots$，最低次项分析表明该点是奇点当 $g > 1$？

实际上，射影化后需验证唯一的无穷远点是否非奇异。标准方法是考虑曲线的另一仿射卡 $X \neq 0$：令 $u = Z/X$，$w = Y/X$，则
$$w^2 u^{2g} = \prod_{i=1}^{2g+2} (1 - a_i u).$$

在 $u = 0$（无穷远），$w^2 \cdot 0 = 1$，矛盾。故无穷远点不在此卡中。改用 $Y \neq 0$：$v = Z/Y$，$t = X/Y$，得 $v^{2g} = \prod (t - a_i v)$。在 $v = 0$，$t = 0$，得 $0 = t^{2g+2}$，所以 $(t, v) = (0, 0)$ 是奇点。

这表明上述射影化不是非奇异的！标准修正：使用加权射影空间，或者引入两个无穷远点。实际上，超椭圆曲线的标准嵌入是
$$y^2 = f(x)$$
在加权射影空间 $\mathbb{P}(1, g+1, 1)$ 中，或者通过紧化得到两个无穷远点（当次数为偶数时）。

正确的射影完备化：令 $\deg(f) = 2g+2$（偶数），则令 $x = X/Z$，$y = Y/Z^{g+1}$，在加权射影空间 $\mathbb{P}(1, g+1, 1)$ 中，方程为
$$Y^2 = \prod_{i=1}^{2g+2} (X - a_i Z).$$

此曲线非奇异，且到 $[X:Z]$ 的映射给出 $X \to \mathbb{P}^1$ 的次数 2 态射。分歧点恰为 $Z = 1$，$X = a_i$ 的 $2g+2$ 个点，加上可能的无穷远点（若 $2g+2$ 为奇数则分歧；此处为偶数，故无穷远点不分歧）。

由 Hurwitz 公式反向验证：$2g - 2 = 2(-2) + (2g+2)$，成立。∎

### 关键概念提示

- **超椭圆对合**（hyperelliptic involution）是覆盖变换 $y \mapsto -y$，生成 $\operatorname{Aut}(X)$ 的一个 2 阶元。
- 当 $g = 2$ 时，所有曲线都是超椭圆的；$g = 3$ 时存在非超椭圆曲线（如非奇异四次平面曲线）。
- 加权射影空间是处理这类方程的标准工具，它比通常的射影空间更能保持非奇异性。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 直接在通常射影空间中完备化 $y^2 = f(x)$ | 通常射影化会引入奇点；需用加权射影空间或显式爆破。 |
| 忽略特征 2 的情形 | 特征 2 时，次数 2 覆盖是 Artin-Schreier 覆盖，不是 $y^2 = f(x)$ 的形式。 |
| 认为分歧点 = 零点 | 分歧点是投影映射的分歧位置；对 $y^2 = f(x)$，零点处分歧，但无穷远点可能不分歧（当 $\deg(f)$ 偶数时）。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Curves.Hyperelliptic

open AlgebraicGeometry Scheme

variable {k : Type*} [Field k] [IsAlgClosed k] (g : ℕ) (hg : g ≥ 2)

-- 超椭圆曲线：存在到 P^1 的次数 2 态射
def IsHyperelliptic (X : Scheme) [IsCurve X] : Prop :=
  ∃ (f : X ⟶ ℙ_k_1), morphismDegree f = 2

-- (a) 分歧点个数为 2g + 2
theorem hyperelliptic_branch_points (X : Scheme) [IsCurve X] (h : IsHyperelliptic X)
    (hgenus : genus X = g) [CharZero k] :
    (branchDivisor h.choose).deg = 2 * g + 2 :=
  sorry

-- (b) 由 2g+2 个点构造超椭圆曲线
def hyperellipticCurve (pts : Fin (2 * g + 2) → k) (hpts : Function.Injective pts) :
    {X : Scheme // IsNonsingular X ∧ genus X = g ∧ IsHyperelliptic X} :=
  sorry
```

---

## 习题 IV.3.1 — 典范线性系与基点子自由性

### 题号与精确引用

**Hartshorne IV.3.1**

### 问题重述

设 $X$ 为亏格 $g \geq 2$ 的非奇异曲线，$K_X$ 为典范除子。

(a) 证明典范线性系 $|K_X|$ 无基点（base-point free）。

(b) 证明典范映射 $\phi_K: X \to \mathbb{P}^{g-1}$ 是态射。当 $g = 2$ 时，描述 $\phi_K$ 的像。

### 详细解答

**(a) $|K_X|$ 无基点**

回忆：除子 $D$ 有基点 $P$ 若对所有 $D' \in |D|$ 有 $P \in \operatorname{Supp}(D')$，等价地 $L(D-P) = L(D)$。

设 $P \in X$。需证 $L(K - P) \subsetneq L(K)$，即 $\ell(K - P) < \ell(K) = g$。

由 Riemann-Roch：
$$\ell(K - P) - \ell(P) = (2g - 2 - 1) + 1 - g = g - 2.$$

故 $\ell(K - P) = g - 2 + \ell(P)$。

因 $g \geq 2$，$\ell(P) = 1$（否则存在次数 1 的非常值函数，意味着 $X \cong \mathbb{P}^1$，与 $g \geq 2$ 矛盾）。于是
$$\ell(K - P) = g - 2 + 1 = g - 1 < g = \ell(K).$$

因此 $P$ 不是 $|K|$ 的基点。由 $P$ 任意，$|K|$ 无基点。∎

**(b) 典范映射的性质**

因 $|K|$ 无基点，$\phi_K: X \to \mathbb{P}^{g-1}$ 是良定义的态射（Hartshorne II.7）。

**$g = 2$ 的情形**：

$|K|$ 是 $g^1_2$（次数 $2g - 2 = 2$，维数 $g - 1 = 1$）。故 $\phi_K: X \to \mathbb{P}^1$ 是次数 2 的态射。因 $g = 2$，$X$ 是超椭圆的，且 $\phi_K$ 就是超椭圆覆盖 $X \to \mathbb{P}^1$。

由 IV.2.2，$\phi_K$ 恰有 $2g + 2 = 6$ 个分歧点。$\phi_K$ 是满射（因次数 2 > 0），且作为有限态射，像是整个 $\mathbb{P}^1$。

### 关键概念提示

- **无基点** 是线性系定义态射的充要条件（Hartshorne II.7）。
- **$\ell(P) = 1$ 对 $g \geq 2$** 是常用论证：若 $\ell(P) \geq 2$，则存在次数 1 的非常值态射 $X \to \mathbb{P}^1$，迫使 $X \cong \mathbb{P}^1$。
- 对 $g = 2$，典范映射**不是嵌入**，而是 2:1 覆盖。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 忽略 $g \geq 2$ 的假设 | $g = 0$ 时 $K$ 负次数，$|K|$ 为空；$g = 1$ 时 $K \sim 0$，$|K|$ 是单点。 |
| 认为 $|K|$ 总是 very ample | 仅当 $X$ 非超椭圆时（$g \geq 3$）才是嵌入。 |
| 混淆 base-point free 与 very ample | base-point free $\Rightarrow$ 态射；very ample $\Rightarrow$ 嵌入。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Curves.Canonical

open AlgebraicGeometry Scheme

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {X : Scheme} [IsCurve X] [IsNonsingular X] (g : ℕ) (hg : genus X = g) (hgg : g ≥ 2)

-- (a) 典范线性系无基点
theorem canonical_base_point_free :
    IsBasePointFree (canonicalLinearSystem X) :=
  sorry

-- (b) 典范映射是态射（由无基点保证）
def canonicalMap : X ⟶ ℙ_k_(g - 1) :=
  sorry -- 由线性系诱导的态射
```

---

## 习题 IV.3.2 — 典范嵌入判据

### 题号与精确引用

**Hartshorne IV.3.2**

### 问题重述

设 $X$ 为亏格 $g \geq 3$ 的非超椭圆曲线。证明典范映射 $\phi_K: X \to \mathbb{P}^{g-1}$ 是闭嵌入（即 $|K_X|$ 是 very ample 的）。进一步，证明 $\phi_K(X)$ 是 $\mathbb{P}^{g-1}$ 中次数 $2g - 2$ 的曲线，且其齐次理想由二次型生成（当 $g \geq 4$ 时）。

### 详细解答

**Step 1: Very ample 的判别**

由 Hartshorne II.7，线性系 $|D|$ 是 very ample 当且仅当对任意闭点 $P, Q \in X$（$P = Q$ 允许），有
$$\ell(D - P - Q) = \ell(D) - 2.$$

取 $D = K$。需证：对任意 $P, Q \in X$，$\ell(K - P - Q) = g - 2$。

**Step 2: 应用 Riemann-Roch**

$$\ell(K - P - Q) - \ell(P + Q) = (2g - 2 - 2) + 1 - g = g - 3.$$

故
$$\ell(K - P - Q) = g - 3 + \ell(P + Q).$$

需证 $\ell(P + Q) = 1$（对任意 $P, Q$）。

**Step 3: 非超椭圆条件的使用**

若存在 $P \neq Q$ 使 $\ell(P + Q) \geq 2$，则 $|P + Q|$ 给出一个 $g^1_2$，即 $X$ 是超椭圆的，矛盾。

若存在 $P$ 使 $\ell(2P) \geq 2$，则 $|2P|$ 给出 $g^1_2$，同样矛盾。

因此对所有 $P, Q$，$\ell(P + Q) = 1$，从而
$$\ell(K - P - Q) = g - 3 + 1 = g - 2 = \ell(K) - 2.$$

故 $|K|$ 是 very ample，$\phi_K$ 是嵌入。∎

**Step 4: 像的次数**

$\phi_K(X)$ 是 $\mathbb{P}^{g-1}$ 中的曲线，其次数 = $\deg(K) = 2g - 2$（very ample 线性系的次数等于嵌入后曲线的次数）。

**Step 5: 理想的二次生成（Petri 定理概述）**

这是经典的 **Petri 定理**（Hartshorne IV.6 中提及，更完整的陈述见 Arbarello-Cornalba-Griffiths-Harris）：设 $X$ 为非超椭圆、非三角的曲线（$g \geq 4$），则 $\phi_K(X)$ 的齐次理想由二次型生成。

证明思路：设 $S = k[x_0, \dots, x_{g-1}]$ 为 $\mathbb{P}^{g-1}$ 的坐标环。考虑正合列
$$0 \to I_X \to S \to \bigoplus_{n \geq 0} H^0(X, \mathcal{O}_X(nK)) \to 0.$$

需证映射 $S_2 \to H^0(X, \mathcal{O}_X(2K))$ 的核生成理想。由维数计算：

- $\dim S_2 = \binom{g+1}{2}$
- $\dim H^0(2K) = 3g - 3$（由 Riemann-Roch，$\deg(2K) = 4g - 4$，$\ell(2K) = 4g - 4 + 1 - g = 3g - 3$，因 $g \geq 2$ 时 $\ell(K - 2K) = \ell(-K) = 0$）。

对 $g = 4$，$\dim S_2 = 10$，$\dim H^0(2K) = 9$，故核维数为 1，即一个二次型生成理想（$X$ 是二次曲面的完全交）。

对 $g \geq 5$，核维数 $\binom{g+1}{2} - (3g - 3) = \frac{g(g+1)}{2} - 3g + 3 = \frac{g^2 - 5g + 6}{2} = \frac{(g-2)(g-3)}{2}$，这些二次型生成理想。

### 关键概念提示

- **非超椭圆** 是典范嵌入的核心条件；超椭圆曲线的典范映射是 2:1 到有理正规曲线的映射，不是嵌入。
- **Very ample** = 分离点 + 分离切向量；Riemann-Roch 提供了验证这两者的数值工具。
- **Petri 定理** 是曲线模空间理论的基础：它说明一般曲线的典范嵌入由二次方程描述。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 未验证 $P = Q$ 的情形 | Very ample 需要同时验证 $\ell(K - 2P) = g - 2$，这排除了 $\ell(2P) \geq 2$ 的情形。 |
| 认为所有 $g \geq 3$ 的曲线典范嵌入 | $g = 3$ 的超椭圆曲线存在，其典范映射不是嵌入。 |
| 混淆 very ample 与 ample | Ample 仅要求某个倍数为 very ample；典范丛本身 very ample 是强得多的结论。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Curves.Canonical

open AlgebraicGeometry Scheme

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {X : Scheme} [IsCurve X] [IsNonsingular X] (g : ℕ) (hg : genus X = g) (hgg : g ≥ 3)

-- 非超椭圆曲线的典范嵌入
theorem canonical_embedding (hnonhyp : ¬ IsHyperelliptic X) :
    IsClosedEmbedding (canonicalMap X) :=
  sorry

-- 典范像的次数为 2g - 2
theorem canonical_image_degree :
    let C := canonicalMap X |>.image
    degree C = 2 * g - 2 :=
  sorry
```

---

## 习题 IV.4.1 — 椭圆曲线的群结构

### 题号与精确引用

**Hartshorne IV.4.1**

### 问题重述

设 $X$ 为椭圆曲线（亏格 1 的曲线），$O \in X$ 为选定的基点。利用 Riemann-Roch 证明：

(a) 对任意 $P, Q \in X$，存在唯一的 $R \in X$ 使得 $P + Q \sim R + O$（作为除子的线性等价）。

(b) 由 (a) 定义的运算 $(P, Q) \mapsto R$ 使 $X$ 成为以 $O$ 为单位元的交换群。

(c) 证明群结构等价于 $\operatorname{Pic}^0(X)$：映射 $P \mapsto [P - O]$ 给出群同构 $X \cong \operatorname{Pic}^0(X)$。

### 详细解答

**(a) 存在性与唯一性**

考虑除子 $D = P + Q - O$，其次数为 1。由 Riemann-Roch（$g = 1$）：
$$\ell(D + O) - \ell(K - D - O) = \deg(D + O) + 1 - 1 = 2.$$

因 $g = 1$，$K \sim 0$，故 $K - D - O = -P - Q + O \sim -P - Q + O$（等价的调整）。实际上直接用：

$\ell(P + Q - O) - \ell(K - P - Q + O) = 1 + 1 - 1 = 1$。

因 $K \sim 0$，$\ell(K - P - Q + O) = \ell(O - P - Q)$。若 $P + Q \neq O$（一般情形），$\deg(O - P - Q) = -1 < 0$，故 $\ell(O - P - Q) = 0$。

于是 $\ell(P + Q - O) = 1$。故存在唯一的有效除子 $R$ 使得 $R \sim P + Q - O$，即 $P + Q \sim R + O$。∎

**(b) 群公理的验证**

定义 $P \oplus Q = R$，其中 $R$ 由 (a) 唯一确定。

- **单位元**：$P \oplus O = R$ 其中 $P + O \sim R + O$，即 $P \sim R$，故 $R = P$（唯一有效代表）。

- **交换性**：$P + Q = Q + P$，故 $P \oplus Q = Q \oplus P$。

- **逆元**：对 $P$，需找 $P'$ 使 $P \oplus P' = O$，即 $P + P' \sim O + O = 2O$。由 Riemann-Roch，$\ell(2O - P) = 1$（因 $\deg(2O - P) = 1$），故存在唯一 $P'$ 使 $P' + O \sim 2O - P$？等等，需更仔细：

找 $P'$ 使 $P + P' \sim 2O$。由 (a) 的变形，$\ell(2O - P) = 1$，存在唯一 $P'$ 使 $P' \sim 2O - P$，即 $P + P' \sim 2O$。于是 $P \oplus P' = O$（因为 $P + P' \sim O + O$ 意味着运算结果是 $O$）。

- **结合性**：需证 $(P \oplus Q) \oplus R = P \oplus (Q \oplus R)$。用 Picard 群的解释：$P \oplus Q$ 对应 $[P - O] + [Q - O] = [P + Q - 2O] \in \operatorname{Pic}^0(X)$，而 $(P \oplus Q) \oplus R$ 对应 $[P + Q + R - 3O]$。由交换性和 (c) 的同构，结合性由 $\operatorname{Pic}^0(X)$ 的群结构保证。

**(c) 与 $\operatorname{Pic}^0(X)$ 的同构**

定义 $\sigma: X \to \operatorname{Pic}^0(X)$，$\sigma(P) = [P - O]$（除子类）。

- **同态**：$\sigma(P \oplus Q) = [(P \oplus Q) - O]$。由定义 $P + Q \sim (P \oplus Q) + O$，故 $P + Q - 2O \sim (P \oplus Q) - O$。左边 = $[P - O] + [Q - O] = \sigma(P) + \sigma(Q)$。故 $\sigma(P \oplus Q) = \sigma(P) + \sigma(Q)$。

- **单射**：若 $\sigma(P) = \sigma(Q)$，则 $P - O \sim Q - O$，即 $P \sim Q$。因 $X$ 是曲线，$P = Q$（不同点不线性等价，因 $\ell(P) = 1$，$L(P)$ 中只有常数函数）。

- **满射**：设 $[D] \in \operatorname{Pic}^0(X)$，$\deg(D) = 0$。写 $D = D_+ - D_-$ 为有效除子之差。由 Abel-Jacobi 的一般理论（或直接用 Riemann-Roch），对椭圆曲线，$\deg(D) = 0$ 的除子类都可写成 $[P - O]$。具体地，$\ell(D + O) = 1$（因 $\deg(D+O) = 1$，Riemann-Roch 对 $g=1$ 给出 $\ell(D+O) - \ell(K-D-O) = 1$，而 $K \sim 0$），故存在唯一 $P$ 使 $P \sim D + O$，即 $D \sim P - O$。∎

### 关键概念提示

- **椭圆曲线的群结构** 是代数几何中最优美的构造之一：几何（点的加法）与代数（Picard 群）完全统一。
- **$\operatorname{Pic}^0(X)$** 是次数 0 的除子类群；对椭圆曲线，它是代数群（即 $X$ 自身）。
- 对高亏格曲线，$\operatorname{Pic}^0(X)$ 是维数 $g$ 的 Abel 簇（Jacobi 簇），而 $X$ 嵌入其中（Abel-Jacobi 映射）。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 未固定基点 $O$ | 群结构依赖于 $O$ 的选择；不同基点给出同构的群。 |
| 混淆 $P + Q$（除子加法）与 $P \oplus Q$（群运算） | 除子加法 $P + Q$ 是形式的；群运算 $P \oplus Q$ 用线性等价归约为单点。 |
| 认为 $P + Q = R$（集合论） | 正确是 $P + Q \sim R + O$；$R$ 一般不等于 $P$ 或 $Q$。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.Curves.Elliptic

open AlgebraicGeometry Scheme

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {X : Scheme} [IsCurve X] [IsNonsingular X] (hE : genus X = 1) (O : X)

-- 椭圆曲线上的群结构
def ellipticGroupLaw : AddCommGroup X where
  add P Q :=
    let D := P + Q - O  -- 除子
    let R := uniqueEffectiveRepr D (by rw [degree_D]; simp; linarith)
    R
  zero := O
  -- 群公理由 Pic^0 的同构保证
  add_comm := sorry
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  neg := sorry
  add_neg_left := sorry

-- 与 Pic^0 的同构
def picZeroIso : X ≃+ PicZero X :=
  sorry
```

---

## 习题 IV.4.2 — Weierstrass ℘-函数与椭圆曲线的解析 uniformization

### 题号与精确引用

**Hartshorne IV.4.2**

### 问题重述

设 $\Lambda = \mathbb{Z}\omega_1 + \mathbb{Z}\omega_2 \subset \mathbb{C}$ 为格（lattice），$\omega_1, \omega_2 \in \mathbb{C}$ 在 $\mathbb{R}$ 上线性无关。定义 **Weierstrass ℘-函数**：
$$\wp(z) = \frac{1}{z^2} + \sum_{\omega \in \Lambda \setminus \{0\}} \left(\frac{1}{(z - \omega)^2} - \frac{1}{\omega^2}\right).$$

(a) 证明 $\wp(z)$ 是 $\Lambda$-双周期亚纯函数，在格点处有 2 阶极点。

(b) 证明 $\wp(z)$ 满足常微分方程
$$(\wp')^2 = 4\wp^3 - g_2 \wp - g_3,$$
其中
$$g_2 = 60 \sum_{\omega \neq 0} \frac{1}{\omega^4}, \quad g_3 = 140 \sum_{\omega \neq 0} \frac{1}{\omega^6}.$$

(c) 证明映射 $z \mapsto [\wp(z) : \wp'(z) : 1]$ 给出黎曼面同构 $\mathbb{C}/\Lambda \cong E$，其中 $E$ 是射影平面曲线 $y^2 = 4x^3 - g_2 x - g_3$ 的紧致化（椭圆曲线）。

### 详细解答

**(a) 双周期性与极点**

**收敛性**：对固定 $z \notin \Lambda$，项
$$\frac{1}{(z - \omega)^2} - \frac{1}{\omega^2} = \frac{\omega^2 - (z - \omega)^2}{\omega^2 (z - \omega)^2} = \frac{2z\omega - z^2}{\omega^2 (z - \omega)^2}.$$

当 $|\omega| \to \infty$，分子 $\sim 2z\omega$，分母 $\sim \omega^4$，故项 $\sim 2z/\omega^3$。因 $\sum_{\omega \neq 0} 1/|\omega|^3 < \infty$（格点上三维级数收敛），级数在 $\mathbb{C} \setminus \Lambda$ 的紧子集上绝对一致收敛。

**双周期性**：先证 $\wp$ 是偶函数：
$$\wp(-z) = \frac{1}{z^2} + \sum_{\omega \neq 0} \left(\frac{1}{(-z - \omega)^2} - \frac{1}{\omega^2}\right) = \frac{1}{z^2} + \sum_{\omega \neq 0} \left(\frac{1}{(z + \omega)^2} - \frac{1}{\omega^2}\right).$$

因 $\Lambda = -\Lambda$，求和指标可换为 $-\omega$，得 $\wp(-z) = \wp(z)$。

再证 $\wp'$ 是 $\Lambda$-周期的。形式求导：
$$\wp'(z) = -2 \sum_{\omega \in \Lambda} \frac{1}{(z - \omega)^3}.$$

显然 $\wp'(z + \lambda) = \wp'(z)$ 对任意 $\lambda \in \Lambda$（因 $(z + \lambda - \omega)^{-3} = (z - (\omega - \lambda))^{-3}$，且 $\omega \mapsto \omega + \lambda$ 是 $\Lambda$ 的双射）。

故 $\wp'$ 是 $\Lambda$-周期的。于是 $\wp(z + \omega_1) - \wp(z)$ 为常数（导数为零）。取 $z = -\omega_1/2$，利用偶性：
$$\wp(\omega_1/2) - \wp(-\omega_1/2) = 0.$$

故该常数为 0，即 $\wp(z + \omega_1) = \wp(z)$。同理 $\wp(z + \omega_2) = \wp(z)$。

**极点**：在 $z = 0$ 附近，$\wp(z) = 1/z^2 + O(z^2)$（因求和部分在 $z=0$ 全纯），故是 2 阶极点。由周期性，所有格点处都是 2 阶极点。

**(b) 微分方程**

在 $z = 0$ 附近展开：
$$\wp(z) = z^{-2} + a z^2 + b z^4 + O(z^6).$$

具体计算 Laurent 展开：对 $|z| < |\omega|$，
$$\frac{1}{(z - \omega)^2} = \frac{1}{\omega^2} \cdot \frac{1}{(1 - z/\omega)^2} = \frac{1}{\omega^2} \sum_{n=0}^{\infty} (n+1) \left(\frac{z}{\omega}\right)^n.$$

故
$$\frac{1}{(z-\omega)^2} - \frac{1}{\omega^2} = \sum_{n=1}^{\infty} \frac{(n+1) z^n}{\omega^{n+2}}.$$

对 $n$ 为奇数的项，求和 $\sum_{\omega \neq 0} 1/\omega^{n+2}$ 中 $\omega$ 与 $-\omega$ 抵消，故只有偶数 $n$ 有贡献。令 $n = 2m$：
$$\wp(z) = z^{-2} + \sum_{m=1}^{\infty} (2m+1) G_{2m+2} z^{2m},$$
其中 $G_k = \sum_{\omega \neq 0} \omega^{-k}$（Eisenstein 级数）。特别地，
$$\wp(z) = z^{-2} + 3G_4 z^2 + 5G_6 z^4 + O(z^6).$$

记 $g_2 = 60 G_4$，$g_3 = 140 G_6$。

计算：
$$\wp'(z) = -2z^{-3} + 6G_4 z + 20G_6 z^3 + O(z^5),$$
$$(\wp')^2 = 4z^{-6} - 24G_4 z^{-2} - 80G_6 + O(z^2),$$
$$4\wp^3 = 4z^{-6} + 36G_4 z^{-2} + 60G_6 + O(z^2),$$
$$-g_2 \wp = -60G_4 z^{-2} + O(z^2),$$
$$-g_3 = -140G_6.$$

于是
$$4\wp^3 - g_2 \wp - g_3 = 4z^{-6} - 24G_4 z^{-2} - 80G_6 + O(z^2) = (\wp')^2.$$

因此 $f(z) := (\wp')^2 - (4\wp^3 - g_2 \wp - g_3)$ 是 $\Lambda$-周期全纯函数（因 $f$ 无极点：$\wp$ 的极点被上述恒等式抵消），且在 $z=0$ 处 $f(0) = 0$。周期全纯函数在紧集 $\mathbb{C}/\Lambda$ 上有界，由 Liouville 定理 $f$ 为常数，又 $f(0) = 0$，故 $f \equiv 0$。∎

**(c) 黎曼面同构**

定义 $E$ 为射影曲线 $Y^2 Z = 4X^3 - g_2 X Z^2 - g_3 Z^3$（齐次化）。判别式 $\Delta = g_2^3 - 27g_3^2 \neq 0$（因 $\Lambda$ 非退化），故 $E$ 非奇异。

定义映射 $\phi: \mathbb{C}/\Lambda \to E$ 为
$$z \mapsto \begin{cases} [\wp(z) : \wp'(z) : 1] & z \notin \Lambda, \\ [0 : 1 : 0] & z \in \Lambda. \end{cases}$$

**良定义**：由 (b)，$[\wp : \wp' : 1]$ 满足 $E$ 的方程。

**全纯性**：在 $z = 0$ 附近，$\wp \sim z^{-2}$，$\wp' \sim -2z^{-3}$，故 $[\wp : \wp' : 1] = [z^3 \wp : z^3 \wp' : z^3] \sim [z : -2 : z^3] \to [0 : 1 : 0]$（射影坐标下乘以 $z^3$）。全纯延拓至 $[0:1:0]$。

**单射**：设 $\phi(z_1) = \phi(z_2)$。若 $z_1, z_2 \notin \Lambda$，则 $\wp(z_1) = \wp(z_2)$ 且 $\wp'(z_1) = \wp'(z_2)$。因 $\wp$ 是偶函数且周期为 $\Lambda$，$\wp(z_1) = \wp(z_2)$ 意味着 $z_2 = \pm z_1 + \lambda$（对某个 $\lambda \in \Lambda$）。若 $z_2 = z_1 + \lambda$，则 $\wp'(z_2) = \wp'(z_1)$，成立。若 $z_2 = -z_1 + \lambda$，则 $\wp'(z_2) = \wp'(-z_1) = -\wp'(z_1)$（奇函数），故需 $\wp'(z_1) = 0$。但 $\wp'(z_1) = 0$ 恰在 2-分点（half-lattice points），此时 $z_1 = -z_1 + \lambda'$，即 $2z_1 \in \Lambda$，仍给出 $z_2 = z_1 + \lambda''$。

**满射**：$\phi$ 是非常值全纯映射从紧黎曼面到紧黎曼面，故是满射（像既开又闭）。

**双全纯**：紧黎曼面间的双射全纯映射是双全纯。故 $\phi$ 是黎曼面同构。∎

### 关键概念提示

- **Weierstrass ℘-函数** 实现了椭圆曲线的**解析 uniformization**：每个复椭圆曲线都同构于某个 $\mathbb{C}/\Lambda$。
- **$g_2, g_3$** 是模形式（modular forms），权分别为 4 和 6；判别式 $\Delta = g_2^3 - 27g_3^2$ 是权 12 的尖点形式。
- **椭圆曲线的 $j$-不变量** $j = 1728 g_2^3 / \Delta$ 分类了复椭圆曲线的模空间。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 忽略 $g_2, g_3$ 的收敛性 | Eisenstein 级数 $G_k$（$k \geq 4$ 偶数）绝对收敛；$k=2$ 时不收敛。 |
| 认为任意 $g_2, g_3$ 给出椭圆曲线 | 需判别式 $\Delta \neq 0$；$\Delta = 0$ 时曲线有尖点或结点。 |
| 未验证 $z=0$ 处的全纯延拓 | 需用齐次坐标说明 $[\wp : \wp' : 1]$ 在极点处延拓为无穷远点 $[0:1:0]$。 |

### Lean4 代码占位

```lean4
import Mathlib.Analysis.Complex.Lattice
import Mathlib.NumberTheory.ModularForms.EisensteinSeries

open Complex

-- Weierstrass ℘-函数
def weierstrassP (Λ : Submodule ℤ ℂ) (h : IsLattice Λ) (z : ℂ) : ℂ :=
  ∑' ω : {ω // ω ∈ Λ ∧ ω ≠ 0}, (1 / (z - ω)^2 - 1 / ω^2)

-- 微分方程中的不变量
def g2 (Λ : Submodule ℤ ℂ) (h : IsLattice Λ) : ℂ :=
  60 * ∑' ω : {ω // ω ∈ Λ ∧ ω ≠ 0}, 1 / ω^4

def g3 (Λ : Submodule ℤ ℂ) (h : IsLattice Λ) : ℂ :=
  140 * ∑' ω : {ω // ω ∈ Λ ∧ ω ≠ 0}, 1 / ω^6

-- ℘ 满足 ODE
theorem weierstrassP_ode (Λ : Submodule ℤ ℂ) (h : IsLattice Λ) (z : ℂ) :
    let ℘ := weierstrassP Λ h
    deriv ℘ z ^ 2 = 4 * ℘ z ^ 3 - g2 Λ h * ℘ z - g3 Λ h :=
  sorry

-- 解析 uniformization
theorem uniformization (Λ : Submodule ℤ ℂ) (h : IsLattice Λ) :
    let E := ellipticCurve (g2 Λ h) (g3 Λ h) (by
      -- 需证判别式非零
      sorry)
    ℂ ⧸ Λ.toAddSubgroup ≃ E.toRiemannSurface :=
  sorry
```

---

**文档位置**: `docs/13-代数几何/Harvard-232br-习题解答/IV.1-IV.4-曲线基本理论.md`
**创建日期**: 2026-04-18
**覆盖习题**: IV.1.1, IV.1.2, IV.1.3, IV.2.1, IV.2.2, IV.3.1, IV.3.2, IV.4.1, IV.4.2（共 9 题）
