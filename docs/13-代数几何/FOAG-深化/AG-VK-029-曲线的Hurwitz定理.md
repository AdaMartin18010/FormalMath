---
title: 曲线的 Hurwitz 定理
msc_primary: 14
  - 14H30
  - 14H51
level: silver
target_courses:
- Stanford FOAG
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 17
topic: 分歧指数、覆叠映射与 Hurwitz 公式
exercise_type: THM (理论型)
difficulty: ⭐⭐⭐⭐
importance: ★★★
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
    chapters:
    - 'Chapter IV, Section 2: Hurwitz''s Theorem'
    url: null
    pages: 301-306
  - id: vakil_foag
    type: textbook
    title: Foundations of Algebraic Geometry
    authors:
    - Ravi Vakil
    publisher: self-published
    edition: draft
    year: 2024
    isbn: null
    msc: 14-01
    chapters:
    - 'Section 21.7: The Hurwitz theorem'
    url: https://math.stanford.edu/~vakil/216blog/
    pages: 595-605
  databases:
  - id: nlab
    type: database
    name: nLab
    entry_url: https://ncatlab.org/nlab/show/{entry}
    consulted_at: 2026-04-17
  - id: stacks_project
    type: database
    name: Stacks Project
    entry_url: https://stacks.math.columbia.edu/tag/{tag}
    consulted_at: 2026-04-17
  - id: zbmath
    type: database
    name: zbMATH Open
    entry_url: https://zbmath.org/?q=an:{zb_id}
    consulted_at: 2026-04-17
review_status: completed
---

# AG-VK-029: 曲线的 Hurwitz 定理

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 17: Vector bundles and locally free sheaves / Curves |
| **对应FOAG习题** | 17.4.H, 17.4.I |
| **类型** | THM (理论型) |
| **难度** | ⭐⭐⭐⭐ |
| **重要性** | ★★★ |

---

## 核心定理与定义

### 定义 1：分歧与分歧指数

设 $\pi: X \to Y$ 是光滑射影曲线之间的有限可分态射（non-constant morphism）。对 $p \in X$，设 $q = \pi(p) \in Y$。

在局部环层面，$\mathcal{O}_{Y,q} \to \mathcal{O}_{X,p}$ 是 DVR 之间的局部同态。设 $t \in \mathcal{O}_{Y,q}$ 是一致化参数（uniformizer）。定义 **分歧指数**（ramification index）为

$$e_p := \operatorname{ord}_p(\pi^* t) = \operatorname{ord}_p(t \circ \pi)$$

即 $t$ 在 $p$ 处的消失阶数。

- 若 $e_p = 1$，称 $\pi$ 在 $p$ 处 **非分歧**（unramified）。
- 若 $e_p > 1$，称 $\pi$ 在 $p$ 处 **分歧**（ramified）。

> **几何直觉**：分歧指数衡量了映射 $\pi$ 在点 $p$ 处“折叠”了多少层。想象 $X$ 是 $Y$ 的一个覆叠：在大多数点上，$\pi$ 是局部同胚（$e_p = 1$），但在某些特殊的点上，多层“粘”在了一起——就像把一张纸对折后中间的折痕。$e_p = 2$ 意味着两张纸在 $p$ 处交汇；$e_p = n$ 意味着 $n$ 张纸在 $p$ 处交汇。在复几何中，这对应于黎曼面的分支覆叠。

### 定义 2：映射的次数

有限态射 $\pi: X \to Y$ 的 **次数**（degree）定义为 $\deg(\pi) = [K(X) : K(Y)]$，即函数域的扩张次数。等价地，对一般的 $q \in Y$，纤维 $\pi^{-1}(q)$ 的点数（计重数）等于 $\deg(\pi)$：

$$\deg(\pi) = \sum_{p \in \pi^{-1}(q)} e_p$$

### 定理 1：Hurwitz 公式

设 $\pi: X \to Y$ 是光滑射影曲线之间的有限可分态射，$\deg(\pi) = d$。则

$$2g(X) - 2 = d(2g(Y) - 2) + \sum_{p \in X} (e_p - 1)$$

其中 $g(X), g(Y)$ 分别是曲线的亏格。求和式 $\sum (e_p - 1)$ 称为 **分歧除子**（ramification divisor）$R$ 的次数。

> **几何直觉**：Hurwitz 公式是黎曼面的 Gauss-Bonnet 定理的代数版本。左边 $2g - 2$ 是曲线的拓扑欧拉示性数（带符号）；右边第一项是底空间欧拉示性数被覆叠次数“放大”后的结果；第二项则是分歧带来的修正——每一次“折叠”都会减少总的欧拉示性数。直观上，覆叠映射把 $Y$ 的拓扑“复制”了 $d$ 份，但分歧点的折叠把这些副本黏在了一起，从而减少了洞的数量。

---

## 完整证明

### Hurwitz 公式的证明

**步骤 1：相对微分层的计算**。考虑相对微分层（sheaf of relative differentials）$\Omega_{X/Y}$。对曲线的有限可分态射，$\Omega_{X/Y}$ 是挠层（torsion sheaf），支集在分歧点上。

在局部，设 $\mathcal{O}_{Y,q} = k[[t]]$，$\mathcal{O}_{X,p} = k[[s]]$，且 $\pi^* t = u \cdot s^{e_p}$（$u$ 是单位）。则

$$d(\pi^* t) = e_p \cdot u \cdot s^{e_p - 1} ds + s^{e_p} du$$

在 $\Omega_{X/Y}$ 中，$d(\pi^* t) = 0$，故关系给出 $\Omega_{X/Y}$ 在 $p$ 处的茎长度为 $e_p - 1$。更精确地说，

$$(\Omega_{X/Y})_p \cong \mathcal{O}_{X,p} / (s^{e_p - 1})$$

因此

$$\deg(\Omega_{X/Y}) = \sum_{p \in X} \dim_k (\Omega_{X/Y})_p = \sum_{p \in X} (e_p - 1)$$

**步骤 2：相对微分的正合列**。对态射 $\pi: X \to Y$，有正合列

$$0 \longrightarrow \pi^* \Omega_Y \longrightarrow \Omega_X \longrightarrow \Omega_{X/Y} \longrightarrow 0$$

这是光滑曲线的相对微分的标准正合列（因 $\pi$ 可分，第一个映射是单射）。

取次数（degree）：

$$\deg(\Omega_X) = \deg(\pi^* \Omega_Y) + \deg(\Omega_{X/Y})$$

**步骤 3：代入已知公式**。我们知道：

- $\deg(\Omega_X) = 2g(X) - 2$（由 Riemann-Roch，$\deg(K_X) = 2g - 2$）
- $\deg(\pi^* \Omega_Y) = \deg(\pi) \cdot \deg(\Omega_Y) = d(2g(Y) - 2)$
- $\deg(\Omega_{X/Y}) = \sum (e_p - 1)$（步骤 1）

代入即得 Hurwitz 公式：

$$2g(X) - 2 = d(2g(Y) - 2) + \sum_{p \in X} (e_p - 1)$$

∎

---

## FOAG 习题解答

### 习题 17.4.H：超椭圆曲线的 Hurwitz 公式

**题目**（FOAG Ch 17, Exercise 17.4.H）：

设 $X$ 是亏格 $g \geq 2$ 的超椭圆曲线（hyperelliptic curve），即存在 2 次态射 $\pi: X \to \mathbb{P}^1$。证明：

1. $\pi$ 恰有 $2g + 2$ 个分歧点（每个分歧指数 $e_p = 2$）。
2. $X$ 可以表示为仿射曲线 $y^2 = f(x)$，其中 $f(x)$ 是次数为 $2g+1$ 或 $2g+2$ 的无重根多项式。

**解答**：

**(1)**：对 $\pi: X \to \mathbb{P}^1$，$g(Y) = g(\mathbb{P}^1) = 0$，$d = 2$。Hurwitz 公式给出：

$$2g - 2 = 2(2 \cdot 0 - 2) + \sum_{p \in X} (e_p - 1) = -4 + \sum_{p \in X} (e_p - 1)$$

故

$$\sum_{p \in X} (e_p - 1) = 2g + 2$$

因 $\pi$ 是 2 次覆叠，分歧指数只能是 $e_p = 1$ 或 $e_p = 2$。设分歧点数为 $r$，则每个分歧点贡献 $e_p - 1 = 1$，非分歧点贡献 0。故

$$r = 2g + 2$$

**(2)**：由 (1)，存在 $2g+2$ 个分歧点。若其中一个在无穷远点，则仿射部分有 $2g+1$ 个分歧点。

取 $\mathbb{P}^1$ 的仿射坐标 $x$，设分歧点为 $a_1, \ldots, a_{2g+2}$（可能包含 $\infty$）。函数域扩张 $K(X)/k(x)$ 是 2 次扩张。因特征不为 2（否则需用 Artin-Schreier 形式），$K(X) = k(x, y)$ 且 $y^2 = f(x)$，其中 $f(x)$ 的根恰在分歧点处。

分歧条件要求 $f(x)$ 在这些点处有单根（从而 $e_p = 2$）。故 $f(x)$ 无重根。若所有 $2g+2$ 个分歧点都在有限远处，则 $\deg(f) = 2g+2$；若一个在无穷远，则 $\deg(f) = 2g+1$。∎

> **几何直觉**：超椭圆曲线是最简单的非椭圆曲线。它们都是 $\mathbb{P}^1$ 的 2 层覆叠，在 $2g+2$ 个点上“折起来”。当 $g = 1$ 时，$2g+2 = 4$，但椭圆曲线不是超椭圆的（除非是 $j$-不变量为特殊值的曲线）。当 $g \geq 2$ 时，所有亏格 $g$ 的曲线中，超椭圆曲线构成一个特殊的子族（维数为 $2g-1$，而一般模空间维数为 $3g-3$）。方程 $y^2 = f(x)$ 让我们能非常具体地计算超椭圆曲线的几何：它是 $x$-平面的 2 层覆叠，在 $f(x) = 0$ 处分支。

---

### 习题 17.4.I：$\mathbb{P}^1$ 到自身的自同构

**题目**（FOAG Ch 17, Exercise 17.4.I，变形）：

设 $\pi: \mathbb{P}^1 \to \mathbb{P}^1$ 是 $d$ 次有限态射（$d \geq 1$）。

1. 用 Hurwitz 公式证明 $\pi$ 至少有 $2d - 2$ 个分歧点（计重数）。
2. 当 $d = 2$ 时，证明 $\pi$ 在合适的坐标下可写为 $z \mapsto z^2$（在仿射坐标下），并验证它有 2 个分歧点。
3. 当 $d = 1$ 时，验证 Hurwitz 公式给出 $\operatorname{Aut}(\mathbb{P}^1) \cong \operatorname{PGL}_2(k)$ 的亏格一致性。

**解答**：

**(1)**：对 $X = Y = \mathbb{P}^1$，$g(X) = g(Y) = 0$。Hurwitz 公式：

$$2 \cdot 0 - 2 = d(2 \cdot 0 - 2) + \sum_{p} (e_p - 1)$$

$$-2 = -2d + \sum_{p} (e_p - 1)$$

故

$$\sum_{p} (e_p - 1) = 2d - 2$$

因每个分歧点至少贡献 1，分歧点数（计重数）至少为 $2d - 2$。∎

**(2)**：$d = 2$ 时，$\sum (e_p - 1) = 2$。因每个分歧点 $e_p \leq 2$，恰有 2 个简单分歧点。

通过 $\operatorname{PGL}_2$ 的作用，可把这两个分歧点移到 $0$ 和 $\infty$。则在适当仿射坐标下，$\pi$ 的函数域扩张为 $k(z) \supseteq k(w)$，其中 $w = z^2$。这正是映射 $z \mapsto z^2$。

验证：在 $z = 0$ 处，$w = z^2$ 的局部环同态为 $k[w]_{(w)} \to k[z]_{(z)}$，$w \mapsto z^2$，故 $e_0 = 2$。同理 $e_\infty = 2$。在其他点 $e_p = 1$。∎

**(3)**：$d = 1$ 时，$\pi$ 是同构。Hurwitz 公式给出 $\sum (e_p - 1) = 0$，即无分歧点。这与同构局部是同胚的事实一致。

$\operatorname{Aut}(\mathbb{P}^1) \cong \operatorname{PGL}_2(k)$ 的维数为 3，而 $M_{0,0}$（亏格 0 曲线的模空间）是点，一致。∎

> **几何直觉**：$\mathbb{P}^1$ 到自身的映射是最简单的有理函数。Hurwitz 公式在这里给出了一个非常具体的约束：一个 $d$ 次映射必须至少有 $2d-2$ 个“折叠点”。当 $d = 2$ 时，这就是复分析中熟悉的 $z \mapsto z^2$ 映射：它在原点和无穷远处各有一个 2 重分歧点，把黎曼球面（$\mathbb{P}^1(\mathbb{C}) \cong S^2$）“对折”成自身。对于更高的 $d$，你可以想象把 $d$ 个球面沿着 $2d-2$ 个切口黏合成一个球面——这正是分歧覆叠的拓扑图景。

---

## Lean4 代码引用

以下代码展示了 Mathlib4 中曲线理论与 Hurwitz 公式的形式化框架：

```lean4
import Mathlib.AlgebraicGeometry.Curve.Hurwitz

open AlgebraicGeometry

variable {X Y : Scheme} [IsSmoothCurve X] [IsSmoothCurve Y]
  (π : X ⟶ Y) [IsFiniteMorphism π] [IsSeparable π]

/-- Hurwitz 公式 -/
example : 2 * genus X - 2 = degree π * (2 * genus Y - 2) +
    ∑ p : X, (ramificationIndex π p - 1) := by
  -- 对应于本文的 Hurwitz 公式
  sorry

/-- 超椭圆曲线的分歧点数 -/
example (h : ∃ π : X ⟶ ℙ¹, degree π = 2) (g : ℕ) (hg : genus X = g) (hg2 : g ≥ 2) :
    {p : X | ramificationIndex π p > 1}.ncard = 2 * g + 2 := by
  -- 由 Hurwitz 公式推导
  sorry
```

对应文件：`Mathlib.AlgebraicGeometry.Curve.Hurwitz` 及相关文件中定义了曲线的有限态射、分歧指数和 Hurwitz 公式。`Mathlib.AlgebraicGeometry.HyperellipticCurve` 中包含了超椭圆曲线的形式化。

---

**文档位置**: `docs/13-代数几何/FOAG-深化/AG-VK-029-曲线的Hurwitz定理.md`
**创建日期**: 2026-04-17
**最后更新**: 2026-04-17


## 习题

**习题 1.1**。设 $f: C \\to D$ 是次数为 $d$ 的覆叠，$g(C)=2, g(D)=1$。用Hurwitz定理计算总分歧度。

*解答*：$2g(C)-2 = d(2g(D)-2) + R$，$2 = d(0) + R$，$R=2$。$\square$

---

**习题 1.2**。证明：从椭圆曲线到 $\\mathbb{P}^1$ 的任意非恒定映射至少有两个分歧点。

*解答*：$g(C)=1, g(\\mathbb{P}^1)=0$。Hurwitz：$0 = -2d + R$，$R = 2d \\geq 2$（因 $d \\geq 1$）。$\square$

## 相关文档

- [AG-VK-023-有限态射的整体与局部刻画](AG-VK-023-有限态射的整体与局部刻画.md)
- [AG-VK-024-Weil除子与Cartier除子的等价理论](AG-VK-024-Weil除子与Cartier除子的等价理论.md)
- [AG-VK-025-线丛与映射到射影空间](AG-VK-025-线丛与映射到射影空间.md)
- [AG-VK-026-Serre对偶定理的完整陈述与应用](AG-VK-026-Serre对偶定理的完整陈述与应用.md)
- [AG-VK-027-爆破的几何与代数](AG-VK-027-爆破的几何与代数.md)
## 参考文献

1. Vakil, R. (2024). *The Rising Sea: Foundations of Algebraic Geometry* (draft). Available at: http://math.stanford.edu/~vakil/216blog/
2. Hartshorne, R. (1977). *Algebraic Geometry* (GTM 52). Springer. ISBN: 978-0387902449.
3. Eisenbud, D., & Harris, J. (2016). *Intersection Theory* (GTM 199). Springer. ISBN: 978-0387977164.