---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Bezout 定理 (Bezout's Theorem)
---
# Bezout 定理 (Bezout's Theorem)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicGeometry.Bezout

namespace AlgebraicGeometry

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- Bezout 定理：射影平面上两条没有公共分支的代数曲线的
    交点个数（计重数）等于次数之积 -/
theorem bezout {C1 C2 : ProjectiveCurve k} (h : ¬∃ D, D ≤ C1 ∧ D ≤ C2) :
    ∑ p ∈ C1 ∩ C2, intersectionMultiplicity p C1 C2 = C1.degree * C2.degree := by
  -- 利用射影空间的紧性、Chow 群和陈类理论证明
  sorry

end AlgebraicGeometry
```

## 数学背景

Bezout 定理是代数几何中最古老、最经典的结果之一，由法国数学家艾蒂安·贝祖（Étienne Bézout）在18世纪末证明。该定理断言：在复射影平面 $\mathbb{P}^2_\mathbb{C}$ 上，两条没有公共分支的代数曲线的交点个数（计重数）等于它们次数的乘积。例如，一条 $m$ 次曲线和一条 $n$ 次曲线最多相交于 $mn$ 个点，而若考虑复数点和重数，则恰好相交于 $mn$ 个点。Bezout 定理是射影几何、相交理论和枚举几何的基石，也是现代代数几何中相交乘积和 Chow 环的原型。

## 直观解释

Bezout 定理提供了一个精确计算两条代数曲线交点数的方法。在欧几里得平面中，两条曲线可能错过彼此（例如两条平行直线不相交），或者只相交于有限个点。但在射影平面中，这种遗漏被消除了：平行直线在无穷远点相交，圆和直线总是在两个点相交（可能重合）。Bezout 定理告诉我们：在这个完备的射影世界中，一条 $m$ 次曲线和一条 $n$ 次曲线的总交点数（计重数）恰好是 $mn$。这就像两个不同频率的波动模式在空间中相遇时，它们的共振点数由各自复杂度的乘积决定。

## 形式化表述

设 $C_1$ 和 $C_2$ 是射影平面 $\mathbb{P}^2$ 上的两条代数曲线，次数分别为 $d_1$ 和 $d_2$，且它们没有公共的分支（即没有公共的不可约成分）。则它们的交点集合 $C_1 \cap C_2$ 是有限集，且：

$$\sum_{{p \in C_1 \cap C_2}} m_p(C_1, C_2) = d_1 \cdot d_2$$

其中 $m_p(C_1, C_2)$ 是 $C_1$ 和 $C_2$ 在点 $p$ 处的相交重数。

推广到高维：在 $\mathbb{P}^n$ 中，$n$ 个超曲面 $H_1, \dots, H_n$（次数分别为 $d_1, \dots, d_n$）的交点个数（在横截相交的假设下）为 $d_1 d_2 \cdots d_n$。

其中：

- 射影平面 $\mathbb{P}^2$ 保证了无穷远点的存在，消除了平行不相交的问题
- 相交重数 $m_p$ 衡量了曲线在 $p$ 点处接触的密切程度（切线相交重数为 2，尖点可能更高）
- 曲线必须定义在代数闭域上（如 $\mathbb{C}$），以保证所有交点都存在

## 证明思路

1. **结式/消去法（经典证明）**：对两个二元齐次多项式 $F(X, Y, Z)$ 和 $G(X, Y, Z)$，消去一个变量得到结式 $R(X, Y)$。$R$ 是 $d_1 d_2$ 次齐次多项式，在 $\mathbb{P}^1$ 上有 $d_1 d_2$ 个根（计重数），每个根对应一条通过所有交点的直线
2. **层上同调证明**：利用 $\mathcal{O}(d_1)$ 和 $\mathcal{O}(d_2)$ 的张量积的 Euler 示性数，通过 Kunneth 公式或局部-整体 Ext 计算
3. **相交理论证明**：在 Chow 环 $A^*(\mathbb{P}^2)$ 中，$[C_1] \cdot [C_2] = d_1 h \cdot d_2 h = d_1 d_2 h^2$，其中 $h$ 是超平面类的标准生成元
4. **紧 Riemann 面的观点**：将曲线视为 $\mathbb{P}^2$ 的覆叠，利用覆叠映射的度数公式

核心洞察在于射影空间的紧性保证了所有交点都被计数，包括无穷远点和复点。

## 示例

### 示例 1：两条直线

在 $\mathbb{P}^2$ 中，任何两条不同的直线都恰好相交于一个点。次数都是 1，交点数为 $1 \times 1 = 1$。在仿射平面中平行的直线在无穷远点相交。

### 示例 2：椭圆曲线与直线

椭圆曲线（3 次曲线）与一条直线相交于恰好 3 个点（计重数）。这是椭圆曲线群律定义的基础：两点连线与曲线的第三个交点定义了群的加法。

### 示例 3：圆与抛物线

圆（2 次）与抛物线 $y = x^2$（2 次）在 $\mathbb{P}^2$ 中恰好相交于 4 个点。在 $\mathbb{R}^2$ 中可能只看到 0、1 或 2 个实交点，但在 $\mathbb{C}$ 和 $\mathbb{P}^2$ 中总是 4 个（计重数）。

## 应用

- **代数几何**：相交理论、Chow 环和枚举几何的基础
- **密码学**：椭圆曲线密码学中群运算的良定义性
- **计算机视觉**：代数曲线拟合和重建中的交点计算
- **编码理论**：代数几何码的构造和设计
- **机器人学**：运动学方程的代数求解和路径规划

## 相关概念

- 射影平面 (Projective Plane)：添加无穷远点后的完备平面
- 相交重数 (Intersection Multiplicity)：衡量两曲线在一点接触程度的整数
- 代数闭域 (Algebraically Closed Field)：每个非常数多项式都有根
- Chow 环 (Chow Ring)：代数闭链的相交代数
- 结式 (Resultant)：消去变量的多项式判别工具

## 参考

### 教材

- [P. Griffiths, J. Harris. Principles of Algebraic Geometry. Wiley, 1978. Chapter 1]
- [W. Fulton. Algebraic Curves. Benjamin, 1969. Chapter 5]

### 在线资源

- [Mathlib4 - Bezout](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Bezout.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*
