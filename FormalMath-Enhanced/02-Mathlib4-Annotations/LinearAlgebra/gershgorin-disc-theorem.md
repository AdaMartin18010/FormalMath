---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Gershgorin 圆盘定理 (Gershgorin Disc Theorem)
---
# Gershgorin 圆盘定理 (Gershgorin Disc Theorem)

## Mathlib4 引用

```lean
import Mathlib.LinearAlgebra.Eigenspace.Basic

namespace Matrix

variable {𝕜 : Type*} [Field 𝕜] [IsROrC 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- Gershgorin 圆盘定理：矩阵的每个特征值至少落在某一个 Gershgorin 圆盘内 -/
theorem gershgorin_disc {A : Matrix n n 𝕜} {λ : 𝕜} (hλ : ∃ v, v ≠ 0 ∧ A *ᵥ v = λ • v) :
    ∃ i : n, |λ - A i i| ≤ ∑ j in (Finset.univ.erase i), |A i j| := by
  -- 从特征向量的最大分量出发，利用特征方程推导
  sorry

end Matrix
```

## 数学背景

Gershgorin 圆盘定理由俄罗斯/苏联数学家 Semyon Aronovich Gershgorin 于1931年提出，是矩阵特征值定位理论中最优美且实用的结果之一。该定理无需实际计算特征值，仅凭矩阵元素的绝对值就能给出特征值所在区域的一个简单估计。这一定理在数值线性代数、控制理论、电路分析和量子化学中具有广泛应用。

## 直观解释

Gershgorin 圆盘定理提供了一种非常直观的特征值定位方法。想象一个城市的地图，每个十字路口对应矩阵的一个对角元，而通向其他路口的道路宽度对应非对角元的绝对值。Gershgorin 定理说：城市的所有热点（特征值）必定位于以某个十字路口为中心、以该路口所有 outgoing 道路总宽度为半径的某个圆盘内。这是一个极其强大的定性结论。

## 形式化表述

设 $A = (a_{ij})$ 是一个 $n \times n$ 复方阵。定义第 $i$ 个 Gershgorin 圆盘为：

$$D_i = \left\{ z \in \mathbb{C} : |z - a_{ii}| \leq \sum_{j \neq i} |a_{ij}| \right\}, \quad i = 1, 2, \dots, n$$

Gershgorin 圆盘定理断言：矩阵 $A$ 的每一个特征值 $\lambda$ 都至少落在某一个圆盘 $D_i$ 中。

若 $k$ 个圆盘构成一个连通区域，且与其他圆盘不相交，则该区域恰好包含 $k$ 个特征值（计重数）。

其中：

- $a_{ii}$ 是圆盘中心（第 $i$ 个对角元）
- $R_i = \sum_{j \neq i} |a_{ij}|$ 是第 $i$ 个圆盘的半径（第 $i$ 行非对角元绝对值之和）

## 证明思路

1. **取特征向量**：设 $v$ 是特征值 $\lambda$ 对应的特征向量，取 $|v_i| = \max_j |v_j|$
2. **特征方程**：由 $(Av)_i = \lambda v_i$ 得 $\sum_j a_{ij} v_j = \lambda v_i$
3. **整理**：$(\lambda - a_{ii}) v_i = \sum_{j \neq i} a_{ij} v_j$
4. **取模与放缩**：$|\lambda - a_{ii}| \cdot |v_i| \leq \sum_{j \neq i} |a_{ij}| \cdot |v_j| \leq \sum_{j \neq i} |a_{ij}| \cdot |v_i|$
5. **约去 $|v_i|$**：因 $v_i \neq 0$，得 $|\lambda - a_{ii}| \leq R_i$

核心洞察在于特征向量的最大分量对应的行天然提供了特征值的位置约束。

## 示例

### 示例 1：2x2 矩阵

设 $A = \begin{pmatrix} 4 & 1 \ 2 & 3 \end{pmatrix}$。
$D_1$：中心 4，半径 1。$D_2$：中心 3，半径 2。
两个圆盘相交，特征值在 $D_1 \cup D_2$ 中。实际特征值为 5 和 2，分别落在两个圆盘中。

### 示例 2：严格对角占优矩阵

若 $|a_{ii}| > \sum_{j \neq i} |a_{ij}|$ 对所有 $i$ 成立，则所有 Gershgorin 圆盘都不包含原点，因此矩阵可逆。这是判断矩阵非奇异的快速充分条件。

### 示例 3：摄动分析

设 $A$ 是某物理系统的哈密顿量矩阵。Gershgorin 圆盘可以给出系统能级（特征值）在给定参数摄动下的变化范围，而无需重新对角化。

## 应用

- **数值线性代数**：迭代法收敛性分析和预处理技术设计
- **控制理论**：系统稳定性判据和极点配置
- **电路分析**：振荡电路和滤波器的特征频率范围估计
- **量子化学**：Hückel 理论和分子轨道能量的定性分析
- **振动分析**：机械系统固有频率的范围估计和模态分析

## 相关概念

- 特征值 (Eigenvalue)：矩阵变换下的不变方向上的缩放因子
- 特征向量 (Eigenvector)：对应特征值的非零不变方向
- 严格对角占优 (Strictly Diagonally Dominant)：$|a_{ii}| > \sum_{j \neq i} |a_{ij}|$
- 谱半径 (Spectral Radius)：特征值模的最大值
- 圆盘定理 (Disc Theorem)：Brauer 卵形等更精细的特征值定位结果

## 参考

### 教材

- [R. A. Horn, C. R. Johnson. Matrix Analysis. Cambridge, 2nd edition, 2013. Chapter 6]
- [G. Golub, C. Van Loan. Matrix Computations. Johns Hopkins, 4th edition, 2013. Section 7.1]

### 在线资源

- [Mathlib4 - Eigenspace](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Eigenspace/Basic.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*