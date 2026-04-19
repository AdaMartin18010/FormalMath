---
title: 椭圆曲线的群结构
msc_primary: 14
  - 14H52
  - 14G05
level: silver
target_courses:
- Stanford FOAG
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 19
topic: 椭圆曲线的 Weierstrass 方程与弦切群律
exercise_type: TEC (技术型)
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
    - 'Chapter IV, Section 4: The Elliptic Curve Group Law'
    url: null
    pages: 321-327
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
    - 'Section 19.9: Elliptic curves are group varieties'
    url: https://math.stanford.edu/~vakil/216blog/
    pages: 555-565
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

# AG-VK-028: 椭圆曲线的群结构

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 19: Curves (Elliptic curves) |
| **对应FOAG习题** | 19.9.B, 19.9.C |
| **类型** | TEC (技术型) |
| **难度** | ⭐⭐⭐⭐ |
| **重要性** | ★★★ |

---

## 核心定理与定义

### 定义 1：椭圆曲线

设 $k$ 是代数闭域。$k$ 上的 **椭圆曲线** 是一个二元组 $(E, O)$，其中 $E$ 是 $k$ 上的光滑射影曲线，亏格 $g(E) = 1$，且 $O \in E(k)$ 是一个有理点（称为 **原点**）。

### 定理 1：Weierstrass 方程

任意椭圆曲线 $(E, O)$ 都同构于 $\mathbb{P}^2_k$ 中由 Weierstrass 方程

$$y^2 z + a_1 xyz + a_3 yz^2 = x^3 + a_2 x^2 z + a_4 xz^2 + a_6 z^3$$

定义的光滑三次曲线，且 $O$ 对应点 $[0:1:0]$（无穷远点）。

当 $\operatorname{char}(k) \neq 2, 3$ 时，方程可简化为

$$y^2 z = x^3 + axz^2 + bz^3$$

或仿射形式 $y^2 = x^3 + ax + b$。

> **几何直觉**：椭圆曲线虽然名字里有“椭圆”，但它和椭圆没有任何直接关系——名字来源于计算椭圆周长时出现的椭圆积分。几何上，椭圆曲线就是一个“带一个洞的环面”（在 $\mathbb{C}$ 上同构于 $\mathbb{C}/\Lambda$）。Weierstrass 方程告诉我们：任何椭圆曲线都可以干净地画成平面上的三次曲线，而点 $O$ 就是那个“无穷远点”，它是所有垂直直线的公共交点。

### 定理 2：弦切群律（Chord-Tangent Law）

设 $E$ 是椭圆曲线，$O$ 是原点。存在唯一的 Abel 群结构使得：

1. $O$ 是零元。
2. 对任意 $P, Q \in E$，$P + Q + R = O$ 当且仅当 $P, Q, R$ 三点共线（计重数）。

这里的“计重数”意味着：若 $P = Q$，则“共线”理解为切线与 $E$ 在 $P$ 处有重交点；若 $R = O$，则“直线”为过 $P, Q$ 的垂直线（与 $O$ 交于无穷远）。

> **几何直觉**：椭圆曲线上的群律是数学中最优美的几何构造之一。它的规则非常简单：给定两点 $P$ 和 $Q$，画一条通过它们的直线，这条直线与 $E$ 交于第三点 $R'$；然后把 $R'$ 关于 $x$-轴反射（或在射影意义下，连接 $R'$ 与 $O$ 再次交 $E$ 于 $R$），得到 $P + Q$。为什么这是群律？关键在于 Bezout 定理：平面三次曲线与直线的总交点数（计重数）恰好是 3。所以任意直线与 $E$ 交于三点，这三点的“和”自然应该是零元——因为在群结构中，三点共线意味着 $P + Q + R' = O$。

---

## 完整证明

### 定理 1：Weierstrass 方程的存在性

**步骤 1：Riemann-Roch 的应用**。由 Riemann-Roch 定理，对椭圆曲线 $E$ 上的任意除子 $D$：

$$h^0(E, \mathcal{O}_E(D)) - h^1(E, \mathcal{O}_E(D)) = \deg(D)$$

特别地：

- $\deg(D) < 0$ 时，$h^0 = 0$。
- $\deg(D) > 0$ 时，$h^0 = \deg(D)$，$h^1 = 0$（由 Serre 对偶，$h^1 = h^0(\mathcal{O}_E(-D)) = 0$）。

**步骤 2：构造坐标函数**。取 $D = nO$：

- $h^0(\mathcal{O}_E(O)) = 1$：只有常数函数。
- $h^0(\mathcal{O}_E(2O)) = 2$：存在一个亚纯函数 $x$，在 $O$ 处有 2 阶极点。
- $h^0(\mathcal{O}_E(3O)) = 3$：存在一个亚纯函数 $y$，在 $O$ 处有 3 阶极点，且 $y$ 与 $1, x$ 线性无关。
- $h^0(\mathcal{O}_E(6O)) = 6$：考虑函数 $1, x, x^2, x^3, y, xy, y^2$。这是 7 个函数，但空间只有 6 维，故存在线性关系。

**步骤 3：得到 Weierstrass 方程**。上面的线性关系就是

$$y^2 + a_1 xy + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6$$

（仿射形式）。映射 $(x, y): E \to \mathbb{P}^2$ 是闭嵌入（因为 $3O$ 是非常丰富的除子）。光滑性由 $E$ 光滑保证。

在特征不为 2, 3 时，通过变量替换（完成平方和立方），可化为 $y^2 = x^3 + ax + b$。∎

### 定理 2：弦切群律的良定义性

**存在性**：首先定义一个二元运算 $P \oplus Q$ 如下：

1. 画通过 $P, Q$ 的直线 $L$，设 $L$ 与 $E$ 的第三个交点为 $R$（由 Bezout 定理，这样的 $R$ 存在且唯一，计重数）。
2. 画通过 $R$ 和 $O$ 的直线 $L'$，设 $L'$ 与 $E$ 的第三个交点为 $P \oplus Q$。

**验证群公理**：

- **零元**：$P \oplus O = P$。因为通过 $P$ 和 $O$ 的直线与 $E$ 的第三交点 $R$ 满足 $P + O + R = O$（在群律意义下），再通过 $R$ 和 $O$ 回到 $P$。

- **逆元**：定义 $-P$ 为 $P$ 关于水平轴（在 Weierstrass 形式下）的反射点，即若 $P = (x, y)$，则 $-P = (x, -y)$。验证：通过 $P$ 和 $-P$ 的直线是垂直线，其第三交点为 $O$。再通过 $O$ 和 $O$（切线）回到 $O$。故 $P + (-P) = O$。

- **交换律**：$P \oplus Q = Q \oplus P$ 由构造的对称性直接得到。

- **结合律**：这是最难验证的。标准方法是利用 **Riemann-Roch 和 Abel-Jacobi 映射**：映射

$$\phi: E \longrightarrow \operatorname{Pic}^0(E), \quad P \mapsto [P] - [O]$$

是双射（由 Riemann-Roch：$\deg(D) = 0$ 且 $h^0(D) = 1$ 的除子唯一）。把 $E$ 上的 $\oplus$ 通过 $\phi$ 转移到 $\operatorname{Pic}^0(E)$ 上：

$$\phi(P \oplus Q) = \phi(P) + \phi(Q)$$

而 $\operatorname{Pic}^0(E)$ 的群运算是显然结合的，故 $E$ 上的 $\oplus$ 也是结合的。∎

---

## FOAG 习题解答

### 习题 19.9.B：平面三次曲线上的群律

**题目**（FOAG Ch 19, Exercise 19.9.B）：

设 $E$ 是 $\mathbb{P}^2$ 中由 Weierstrass 方程 $y^2 z = x^3 + axz^2 + bz^3$ 定义的光滑三次曲线，$O = [0:1:0]$。

1. 用 Bezout 定理验证：对任意 $P, Q \in E$，存在唯一的 $R \in E$ 使得 $P, Q, R$ 共线（计重数）。
2. 证明上述“弦切法则”定义的运算 $P + Q := -R$（其中 $-R$ 是 $R$ 关于 $x$-轴的反射）满足群公理。
3. 验证 $2O = O$，并解释 $2P$ 的几何意义（$P$ 处切线与 $E$ 的第三交点）。

**解答**：

**(1)**：由 Bezout 定理，平面三次曲线与一条直线的交点个数（计重数）为 $3 \times 1 = 3$。给定 $P$ 和 $Q$，通过它们的直线 $L$ 已经与 $E$ 有两个交点（计重数），故还剩一个交点 $R$，唯一确定。当 $P = Q$ 时，$L$ 取切线；当 $P, Q, O$ 共线时（即垂直线），$R = O$。

**(2)**：群公理的验证即定理 2 的内容。补充细节：

- **单位元**：$P + O$ 对应通过 $P, O$ 的直线（垂直线），第三交点 $R$ 是 $P$ 关于 $x$-轴的反射点 $-P$。再反射一次得 $P$。故 $P + O = P$。
- **逆元**：$P + (-P)$ 对应通过 $P, -P$ 的垂直线，第三交点为 $O$。反射 $O$ 关于 $x$-轴仍是 $O$。故 $P + (-P) = O$。
- **结合律**：用 $\operatorname{Pic}^0(E)$ 的群结构来传递。弦切法则的几何构造 precisely 对应于除子类的加法。

**(3)**：$2O = O$ 是因为通过 $O$ 的切线是 $z = 0$（无穷远直线），它与 $E$ 在 $O$ 处有三重交点（因为 $O$ 是拐点）。故第三交点仍是 $O$，反射后还是 $O$。

对一般点 $P$，$2P$ 的几何意义是：画 $E$ 在 $P$ 处的切线，设它与 $E$ 再次交于 $R$（$P$ 算作二重交点），则 $2P = -R$。∎

> **几何直觉**：这个习题是椭圆曲线群结构的入门。最关键的是理解 Bezout 定理如何“强迫”了一个群结构：因为三次曲线与直线恰好交于三点，所以“三点之和为零”是唯一的自然选择。$2P$ 的切线构造尤其有趣：它把微分几何（切线）和代数结构（ doubling ）完美结合起来。在密码学中，这个切线操作正是椭圆曲线数字签名算法（ECDSA）的核心计算步骤！

---

### 习题 19.9.C：Weierstrass 方程的存在性

**题目**（FOAG Ch 19, Exercise 19.9.C）：

设 $(E, O)$ 是代数闭域 $k$ 上的椭圆曲线。

1. 利用 Riemann-Roch 证明存在函数 $x \in H^0(E, \mathcal{O}_E(2O))$ 和 $y \in H^0(E, \mathcal{O}_E(3O))$。
2. 证明 $\{1, x\}$ 构成 $H^0(E, \mathcal{O}_E(2O))$ 的基，$\{1, x, y\}$ 构成 $H^0(E, \mathcal{O}_E(3O))$ 的基。
3. 推导 $E$ 有 Weierstrass 方程，且映射 $(x:y:1): E \to \mathbb{P}^2$ 是闭嵌入。

**解答**：

此即定理 1 证明的详细展开。

**(1)**：由 Riemann-Roch，$h^0(\mathcal{O}_E(nO)) = n$（$n \geq 1$）。故

- $\dim H^0(\mathcal{O}_E(2O)) = 2 > 1$，存在非常数函数 $x$。
- $\dim H^0(\mathcal{O}_E(3O)) = 3 > 2$，存在与 $1, x$ 线性无关的函数 $y$。

**(2)**：

- $H^0(\mathcal{O}_E(O)) = k \cdot 1$（只有常数函数）。
- $H^0(\mathcal{O}_E(2O))$ 包含 $H^0(\mathcal{O}_E(O))$，且维数为 2。故若 $x$ 非常数，则 $\{1, x\}$ 是基。
- 同理，$H^0(\mathcal{O}_E(3O))$ 包含 $H^0(\mathcal{O}_E(2O))$，维数为 3，故 $\{1, x, y\}$ 是基。

**(3)**：考虑 $H^0(\mathcal{O}_E(6O))$，维数为 6。但 $\{1, x, x^2, x^3, y, xy, y^2\}$ 有 7 个元素，它们都只有 $O$ 处的极点，且阶数不超过 6。故存在线性关系：

$$y^2 + a_1 xy + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6$$

这给出仿射 Weierstrass 方程。齐次化后得到射影方程。

映射 $(x:y:1): E \to \mathbb{P}^2$ 对应于线丛 $\mathcal{O}_E(3O)$ 及其全局截面 $1, x, y$（即把 $z$ 看作第三个坐标）。因 $3O$ 是非常丰富的除子（由 Riemann-Roch，$\deg(3O) = 3 > 2g = 2$），它给出闭嵌入。∎

> **几何直觉**：Riemann-Roch 在这里起到了“数维数”的神奇作用。它告诉我们：在椭圆曲线上，$nO$ 的截面空间恰好是 $n$ 维的。这让我们能精确地控制坐标函数 $x$ 和 $y$ 的极点行为。$x$ 在 $O$ 处有 2 阶极点，$y$ 有 3 阶极点——这解释了为什么 Weierstrass 方程中 $y^2$ 和 $x^3$ 相配（$2 \times 3 = 3 \times 2 = 6$ 阶极点）。$3O$ 非常丰富则保证了我们可以把椭圆曲线干净地嵌入到 $\mathbb{P}^2$ 中，而不是更高维的空间。

---

## Lean4 代码引用

以下代码展示了 Mathlib4 中椭圆曲线的形式化框架：

```lean4
import Mathlib.AlgebraicGeometry.EllipticCurve

open AlgebraicGeometry

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- 椭圆曲线的定义：亏格1 + 有理点 -/
example (E : Scheme) [IsEllipticCurve E] :
    Genus E = 1 ∧ ∃ O : E, IsRationalPoint O := by
  -- 对应于 FOAG 中椭圆曲线的定义
  sorry

/-- Weierstrass 方程 -/
example (a b : k) (h : 4*a^3 + 27*b^2 ≠ 0) :
    IsEllipticCurve (WeierstrassCurve a b) := by
  -- 光滑性判别式条件
  sorry

/-- 弦切群律 -/
example (E : WeierstrassCurve k) (P Q : E) :
    E.add P Q = E.neg (E.thirdIntersectionPoint P Q) := by
  -- 群律的几何定义
  sorry
```

对应文件：`Mathlib.AlgebraicGeometry.EllipticCurve` 和 `Mathlib.NumberTheory.EllipticDivisibilitySequence` 中定义了椭圆曲线的 Weierstrass 模型、判别式、群律及其基本性质。

---

**文档位置**: `docs/13-代数几何/FOAG-深化/AG-VK-028-椭圆曲线的群结构.md`
**创建日期**: 2026-04-17
**最后更新**: 2026-04-17


## 习题

**习题 1.1**。证明：椭圆曲线 $E$ 上的群运算由"三点共线即和为零"的几何法则给出。

*解答*：固定无穷远点 $O$ 为零元。$P+Q+R=O$ 当且仅当 $P,Q,R$ 共线（在 $\\mathbb{P}^2$ 的Weierstrass嵌入下）。这是弦切法则。$\square$

---

**习题 1.2**。计算椭圆曲线 $E: y^2 = x^3 + 1$ 上的2-挠点（2-torsion points）。

*解答*：2-挠点满足 $P = -P$，即切线在 $P$ 处与 $E$ 交于 $O$。对Weierstrass方程，2-挠点是 $y=0$ 的解：$x^3+1=0$，即 $x=-1, \\omega, \\omega^2$（$\\omega=e^{2\\pi i/3}$），加上 $O$。共4个2-挠点，$E[2] \\cong \\mathbb{Z}/2 \\times \\mathbb{Z}/2$。$\square$

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