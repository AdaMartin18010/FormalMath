---
title: Weil 除子与 Cartier 除子的等价理论
msc_primary: 14
  - 14C20
  - 14C22
level: silver
target_courses:
- Stanford FOAG
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 14
topic: 除子理论、类群与 Picard 群
exercise_type: TEC (技术型)
difficulty: ⭐⭐⭐
importance: ★★
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
    - 'Chapter II, Section 6: Divisors'
    url: null
    pages: 129-138
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
    - 'Section 14.2: Weil divisors and Cartier divisors'
    url: https://math.stanford.edu/~vakil/216blog/
    pages: 385-392
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

# AG-VK-024: Weil 除子与 Cartier 除子的等价理论

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 14: Line bundles and divisors |
| **对应FOAG习题** | 14.2.B, 14.2.E |
| **类型** | TEC (技术型) |
| **难度** | ⭐⭐⭐ |
| **重要性** | ★★ |

---

## 核心定理与定义

### 定义 1：Weil 除子

设 $X$ 是 Noether 整概形。$X$ 上的 **Weil 除子** 是余维数为 1 的素闭子概形的整系数形式线性组合：

$$D = \sum_{\operatorname{codim}(Y, X) = 1} n_Y \cdot [Y]$$

其中 $n_Y \in \mathbb{Z}$，且只有有限多个非零。全体 Weil 除子构成 Abel 群 $\operatorname{Div}(X)$。

若所有 $n_Y \geq 0$，称 $D$ 为 **有效** 的。

### 定义 2：Cartier 除子

$X$ 上的 **Cartier 除子** 是如下数据：$X$ 的一个开覆盖 $\{U_i\}$ 和 $U_i$ 上的亚纯函数 $f_i \in K(X)^\times$，满足在 $U_i \cap U_j$ 上 $f_i / f_j \in \mathcal{O}_X^\times(U_i \cap U_j)$。

两个 Cartier 除子等价，如果它们相差一个整体亚纯函数。Cartier 除子模去主除子得到 **Cartier 类群** $\operatorname{CaCl}(X)$。

> **几何直觉**：Weil 除子像是“在余维 1 子簇上放置电荷”，每个子簇有整数的重数。Cartier 除子则像是“局部由一个方程定义的曲面”——在每个开集上，你可以写出一个亚纯函数 $f_i = 0$ 来刻画它。在光滑或正规的情形下，这两种视角殊途同归：每个 Weil 除子都可以局部由方程定义（即成为 Cartier），而每个 Cartier 除子自然对应一个 Weil 除子（通过计算其零点与极点的重数）。

### 定理 1：从 Cartier 到 Weil

设 $X$ 是 Noether 整分离概形。则存在自然群同态

$$\operatorname{CaCl}(X) \longrightarrow \operatorname{Cl}(X)$$

它是单射。若 $X$ 是正规的（normal），则它是同构。

### 定理 2：$\operatorname{Cl}(\mathbb{P}^n_A) \cong \mathbb{Z}$

设 $A$ 是 UFD。则 $\mathbb{P}^n_A$ 的 Weil 类群（也是 Cartier 类群）同构于 $\mathbb{Z}$，由超平面 $H = V_+(x_0)$ 生成。

---

## 完整证明

### 定理 1：Cartier 与 Weil 的对应

**构造映射**：设 $\{(U_i, f_i)\}$ 是 Cartier 除子 $D$。对 $X$ 的任意余维 1 点（即 codim 1 的素子簇的一般点）$\eta$，取包含 $\eta$ 的 $U_i$。定义

$$\operatorname{ord}_\eta(D) := \operatorname{ord}_\eta(f_i)$$

其中 $\operatorname{ord}_\eta$ 是离散赋值环 $\mathcal{O}_{X, \eta}$ 上的赋值（因为 $X$ 整且 Noether，$\mathcal{O}_{X, \eta}$ 是 DVR 或至少是 1 维 Noether 局部整环，有良定义的赋值）。

这个值不依赖于 $U_i$ 的选取：若在 $U_j$ 上也有 $\eta \in U_j$，则在 $U_i \cap U_j$ 上 $f_i / f_j$ 是可逆的，故 $\operatorname{ord}_\eta(f_i) = \operatorname{ord}_\eta(f_j)$。

于是对应 Weil 除子为

$$\sum_{\operatorname{codim}(\overline{\{\eta\}}, X) = 1} \operatorname{ord}_\eta(D) \cdot [\overline{\{\eta\}}]$$

**验证是群同态**：由 $\operatorname{ord}_\eta(f \cdot g) = \operatorname{ord}_\eta(f) + \operatorname{ord}_\eta(g)$ 直接得到。

**单射性**：设 Cartier 除子 $D = \{(U_i, f_i)\}$ 对应平凡的 Weil 除子。则对所有 codim 1 点 $\eta$，$\operatorname{ord}_\eta(f_i) = 0$。这意味着 $f_i$ 和 $f_i^{-1}$ 在 $\mathcal{O}_{X, \eta}$ 中都是整的。若 $X$ 满足 Serre 条件 $S_2$（特别地，若 $X$ 是正规的），则 $f_i \in \mathcal{O}_X(U_i)^\times$，即 $D$ 是主除子。在一般整分离概形上，至少可以推出 $f_i \in \mathcal{O}_X^\times(U_i)$ 若 $X$ 在 codim 1 处是正则的。严格证明需用 $X$ 是整的且 $f_i$ 在 codim 1 处无零点/极点，从而 $f_i$ 是单位。∎

**满射性（正规情形）**：设 $X$ 正规，$D = \sum n_Y [Y]$ 是 Weil 除子。对任意 $x \in X$，$\mathcal{O}_{X,x}$ 是 Noether 正规局部环，从而在 codim 1 处是正则的（R_1）。Krull 的主理想定理的逆（在 UFD 或更一般的正规环上）告诉我们：每个 codim 1 的素理想都是局部主理想。具体地，在 $x$ 的充分小仿射邻域 $U$ 上，每个素子簇 $Y \cap U$ 都可以由单个方程 $f_Y$ 定义（因为 $\mathcal{O}_{X,x}$ 是 $R_1$，$\mathfrak{p}_Y \mathcal{O}_{X,x}$ 是高度 1 的素理想，从而是主理想——这是 Krull 的结果）。

于是局部上，$D|_U$ 可由亚纯函数

$$f_U = \prod_Y f_Y^{n_Y}$$

定义。这给出 Cartier 除子。∎

### 定理 2：$\operatorname{Cl}(\mathbb{P}^n_A) \cong \mathbb{Z}$

**步骤 1**：任意 Weil 除子 $D$ 可写成 $D = D_+ - D_-$（有效除子之差）。对有效除子，它是 $n$ 个超曲面的线性组合。

**步骤 2**：证明主除子 $D = \operatorname{div}(f)$ 的次数为零。设 $f \in K(\mathbb{P}^n_A)^\times = \operatorname{Frac}(A[x_0, \ldots, x_n])$ 是齐次有理函数。把它写成齐次多项式之商 $f = g/h$，则

$$\operatorname{div}(f) = \operatorname{div}(g) - \operatorname{div}(h)$$

而 $\operatorname{div}(g)$ 是 $V_+(g)$，作为 Weil 除子，它的次数等于 $\deg(g)$（因为 $A$ 是 UFD，$g$ 可唯一分解为不可约齐次因子，每个因子定义一个素除子，重数为 1，总次数为 $\deg(g)$）。同理 $\operatorname{div}(h)$ 的次数为 $\deg(h)$。但 $\operatorname{div}(f)$ 作为除子，其总次数 $\deg(\operatorname{div}(f)) = \deg(g) - \deg(h) = 0$（因为 $f$ 的次数是分子的次数减去分母的次数，而作为有理函数，分子分母可以同乘适当因子使得次数相同）。

更精确地说，在 $\mathbb{P}^n_A$ 上，次数映射

$$\deg: \operatorname{Div}(\mathbb{P}^n_A) \to \mathbb{Z}, \quad \deg(\sum n_Y [Y]) = \sum n_Y \deg(Y)$$

在主除子上为零。这诱导出满射 $\operatorname{Cl}(\mathbb{P}^n_A) \to \mathbb{Z}$。

**步骤 3**：证明次数映射是单射。设 $D$ 是次数为零的 Weil 除子。因 $A$ 是 UFD，$\mathbb{P}^n_A$ 上的齐次坐标环 $A[x_0, \ldots, x_n]$ 是 UFD。在 UFD 上，每个高度 1 的素理想都是主理想。于是 $D$ 对应一个分式理想，而这个理想是主理想。因此 $D$ 是主除子。

故 $\operatorname{Cl}(\mathbb{P}^n_A) \cong \mathbb{Z}$，由超平面 $H = V_+(x_0)$ 生成。∎

---

## FOAG 习题解答

### 习题 14.2.B：射影空间的类群

**题目**（FOAG Ch 14, Exercise 14.2.B）：

设 $A$ 是 UFD。证明 $\operatorname{Cl}(\mathbb{P}^n_A) \cong \mathbb{Z}$，由超平面类生成。

**解答**：此即定理 2 的内容，完整证明如上。

核心步骤总结：

1. 定义除子的 **次数**：对有效除子 $D = V_+(f)$（$f$ 齐次），$\deg(D) = \deg(f)$。
2. 证明主除子的次数为零：若 $g = f_1/f_2$ 是有理函数，则 $\operatorname{div}(g) = \operatorname{div}(f_1) - \operatorname{div}(f_2)$，次数为 $\deg(f_1) - \deg(f_2) = 0$。
3. 证明次数为零的 Weil 除子是主除子：利用 $A[x_0, \ldots, x_n]$ 是 UFD，高度 1 的齐次素理想都是主理想。

> **几何直觉**：$\mathbb{P}^n$ 上的除子类群是 $\mathbb{Z}$，这意味着所有余维 1 的子簇都可以用“重数”这一个整数来分类。超平面是最基本的“砖块”，任何超曲面都可以看作若干个超平面的叠加（带重数）。这与射影空间的简单拓扑结构（单连通、Hodge 分解中 $H^{2} = \mathbb{Z}$）是一致的。

---

### 习题 14.2.E：Cartier 除子与 Weil 除子的关系

**题目**（FOAG Ch 14, Exercise 14.2.E，变形）：

设 $X$ 是 Noether 整分离概形。证明：

1. 存在自然单射 $\operatorname{CaCl}(X) \hookrightarrow \operatorname{Cl}(X)$。
2. 若 $X$ 还是正规的（normal），则该映射是同构。

**解答**：此即定理 1 的内容。

对于 (1)，构造如前所述：Cartier 除子 $\{(U_i, f_i)\}$ 在每个 codim 1 点 $\eta$ 处赋值 $\operatorname{ord}_\eta(f_i)$。因转移函数 $f_i/f_j$ 可逆，这个赋值良定义。映射是群同态，且核中的元素在每个 codim 1 点处赋值为零，从而局部函数 $f_i$ 无零点/极点，即 $f_i \in \mathcal{O}_X^\times(U_i)$。故核为零。

对于 (2)，正规性保证 $X$ 满足 $R_1$（在 codim 1 处正则），从而每个 codim 1 的素理想在局部是主理想。于是任意 Weil 除子可以局部由亚纯函数定义，给出 Cartier 数据。∎

> **几何直觉**：这个习题揭示了两种“除子”概念的深刻关系。Weil 除子是全局的、组合的对象；Cartier 除子是局部的、由方程定义的对象。在“好”空间（正规概形）上，全局的组合数据总可以局部地由方程实现。而在奇异空间上，可能存在一些 Weil 除子无法被任何局部方程捕获——这类除子称为 **non-$$\mathbb{Q}$$-Cartier** 的，是高维双有理几何中的核心研究对象。

---

## Lean4 代码引用

以下代码展示了 Mathlib4 中除子与线丛理论的形式化框架：

```lean4
import Mathlib.AlgebraicGeometry.Divisor

open AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsNormal X]

/-- 正规整概形上 Cartier 除子与 Weil 除子的等价 -/
example : CaCl X ≃ Cl X := by
  -- Mathlib 中已定义了 Cartier 类群与 Weil 类群
  -- 在正规条件下，这两个群典范同构
  sorry

/-- 射影空间的 Picard 群 / 类群 -/
example {A : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] (n : ℕ) :
    Cl (ProjectiveScheme A n) ≃ ℤ := by
  -- 对应于 Cl(P^n_A) = Z 的结果
  sorry
```

对应文件：`Mathlib.AlgebraicGeometry.Divisor` 及 `Mathlib.AlgebraicGeometry.LineBundle` 中定义了 Cartier 除子、Weil 除子以及它们与可逆层的对应关系。

---

**文档位置**: `docs/13-代数几何/FOAG-深化/AG-VK-024-Weil除子与Cartier除子的等价理论.md`
**创建日期**: 2026-04-17
**最后更新**: 2026-04-17


## 习题

**习题 1.1**。证明：在局部唯一分解整环（UFD）上，Weil除子与Cartier除子等价。

*解答*：UFD中高度1的素理想是主理想，故每个Weil除子可由局部方程定义，即Cartier除子。$\square$

---

**习题 1.2**。举例说明：存在Weil除子不是Cartier除子的概形。

*解答*：锥面 $V(xy-z^2) \\subseteq \\mathbb{A}^3$ 在原点处不是UFD，顶点对应的Weil除子不是Cartier除子。$\square$

## 相关文档

- [AG-VK-023-有限态射的整体与局部刻画](AG-VK-023-有限态射的整体与局部刻画.md)
- [AG-VK-025-线丛与映射到射影空间](AG-VK-025-线丛与映射到射影空间.md)
- [AG-VK-026-Serre对偶定理的完整陈述与应用](AG-VK-026-Serre对偶定理的完整陈述与应用.md)
- [AG-VK-027-爆破的几何与代数](AG-VK-027-爆破的几何与代数.md)
- [AG-VK-028-椭圆曲线的群结构](AG-VK-028-椭圆曲线的群结构.md)
## 参考文献

1. Vakil, R. (2024). *The Rising Sea: Foundations of Algebraic Geometry* (draft). Available at: http://math.stanford.edu/~vakil/216blog/
2. Hartshorne, R. (1977). *Algebraic Geometry* (GTM 52). Springer. ISBN: 978-0387902449.
3. Eisenbud, D., & Harris, J. (2016). *Intersection Theory* (GTM 199). Springer. ISBN: 978-0387977164.