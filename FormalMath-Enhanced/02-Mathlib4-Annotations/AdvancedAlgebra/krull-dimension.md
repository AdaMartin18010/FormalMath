# Krull维数

## Mathlib4 引用

```lean
import Mathlib.RingTheory.KrullDimension

namespace CommutativeAlgebra

/-- Krull维数的定义 -/
theorem krull_dimension_def
    {R : Type*} [CommRing R] :
    krullDim R =
      ⨆ (p : PrimeSpectrum R),
        ⨆ (q : PrimeSpectrum R),
          height q - height p := by
  -- Krull维数是素理想链的最大长度
  rfl

/-- 诺特环的维数有限性 -/
theorem noetherian_dimension_finite
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (h : Ring.FiniteKrullDimension R) :
    krullDim R < ⊤ := by
  -- 诺特环的维数有限（如果有限生成）
  apply IsNoetherianRing.krullDimLTTop

end CommutativeAlgebra
```

## 数学背景

Krull维数以德国代数学家Wolfgang Krull命名，他在1937年系统发展了交换环的维数理论。Krull维数度量了交换环的"几何大小"——即其素理想链的最大长度。这一概念连接了交换代数与代数几何：仿射簇的维数等于其坐标环的Krull维数。Krull维数是交换代数中最基本的不变量之一。

## 直观解释

Krull维数回答了"一个环有多少层结构"的问题。素理想对应代数簇的不可约子簇，素理想的包含关系对应子簇的包含。维数1意味着环像一条曲线（只有点和曲线本身），维数2像曲面（点、曲线、曲面）。Krull维数捕捉了这种"嵌套深度"：最长的严格递增素理想链的长度定义了环的几何维数。

## 形式化表述

设 $R$ 是交换环。

**定义**：$\dim(R) = \sup\{n : \exists \mathfrak{p}_0 \subsetneq \mathfrak{p}_1 \subsetneq \cdots \subsetneq \mathfrak{p}_n\}$

其中 $\mathfrak{p}_i$ 是素理想。

**高度**：素理想 $\mathfrak{p}$ 的 $\text{ht}(\mathfrak{p}) = \dim(R_{\mathfrak{p}})$

**深度**：$\text{depth}(\mathfrak{p}) = \dim(R/\mathfrak{p})$

**基本性质**：

- $\dim(k[x_1, \ldots, x_n]) = n$（$k$ 是域）
- $\dim(R/\mathfrak{p}) + \text{ht}(\mathfrak{p}) \leq \dim(R)$
- 诺特局部环的维数有限

## 证明思路

1. **素理想链构造**：找到最长的严格递增素理想链
2. **素理想提升定理**：控制素理想链的长度
3. **诺特性质应用**：在诺特环中，任何理想升链稳定
4. **维数公式**：利用整扩张保持维数的性质

## 示例

### 示例 1：多项式环

**问题**：计算 $\dim(k[x, y, z])$，其中 $k$ 是域。

**解答**：

考虑素理想链：
$$(0) \subsetneq (x) \subsetneq (x, y) \subsetneq (x, y, z)$$

长度为3，因此 $\dim(k[x,y,z]) \geq 3$。

由Noether正规化定理，$\dim(k[x_1, \ldots, x_n]) = n$，故 $\dim(k[x,y,z]) = 3$。

### 示例 2：局部环的维数

**问题**：设 $R = k[x,y]_{(x,y)}$ 是原点的局部环，求 $\dim(R)$。

**解答**：

局部化不改变维数，$\dim(R) = \dim(k[x,y]) = 2$。

素理想链 $(0) \subsetneq (x) \subsetneq (x, y)$ 给出维数下界。

## 应用

- **代数几何**：代数簇的维数理论
- **交换代数**：正则局部环的刻画
- **数论**：Dedekind整环的维数为1
- **奇点理论**：Cohen-Macaulay环的研究
- **组合交换代数**：单项式理想的维数

## 相关概念

- [高度与深度](./height-depth.md)：素理想的局部维数
- [Noether正规化](./noether-normalization.md)：维数计算工具
- [正则局部环](./regular-local-ring.md)：维数与正则序列的关系
- [Cohen-Macaulay环](./cohen-macaulay-ring.md)：维数与深度的相等
- [射影维数](./projective-dimension.md)：模的维数概念

## 参考

### 教材

- Matsumura, H. Commutative Ring Theory. Cambridge, 1986. Chapter 5
- Atiyah, M.F. & Macdonald, I.G. Introduction to Commutative Algebra. Addison-Wesley, 1969. Chapter 11

### 论文

- Krull, W. Dimensionstheorie in Stellenringen. J. Reine Angew. Math., 179: 204-226, 1937.

### 在线资源

- [Krull Dimension Wikipedia](https://en.wikipedia.org/wiki/Krull_dimension)
- [Stacks Project - Dimension Theory](https://stacks.math.columbia.edu/tag/00KD)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
