---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: 射影 Nullstellensatz (Projective Nullstellensatz)
---
# 射影 Nullstellensatz (Projective Nullstellensatz)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal

namespace ProjectiveNullstellensatz

variable {R : Type*} [CommRing R] [IsDomain R]
  {A : Type*} [CommRing A] [Algebra R A]
  [GradedAlgebra (stdDegree R)]

-- 注：Mathlib4 中射影 Nullstellensatz 的相关内容
-- 主要分布在 ProjectiveSpectrum 与 GradedAlgebra 模块中。
-- 以下给出标准的射影 Nullstellensatz 表述框架。

/-- 射影 Nullstellensatz 的主要结论：
    若 I 是齐次理想且 V_p(I) ≠ ∅，则 I_p(V_p(I)) = √I -/
theorem projective_nullstellensatz {I : HomogeneousIdeal (stdDegree R)}
    (h : ProjectiveVariety I ≠ ∅) :
    projectiveVanishingIdeal (projectiveVariety I) = I.radical := by
  -- Mathlib4 中射影 Nullstellensatz 的完整形式化仍在发展中。
  -- 参见 AlgebraicGeometry.ProjectiveSpectrum 相关文件。
  sorry

end ProjectiveNullstellensatz
```

## 数学背景

射影 Nullstellensatz 是代数几何中连接射影代数簇与齐次理想的根本定理，是仿射 Nullstellensatz（Hilbert Nullstellensatz）在射影空间中的自然推广。David Hilbert 于1893年证明了仿射情形，而射影情形则通过研究仿射锥（affine cone）与齐次理想的对应关系导出。该定理建立了射影空间 $\mathbb{P}^n$ 中代数子簇与多项式环中根式齐次理想之间的一一对应（除去 irrelevant ideal），为古典代数几何和现代概型理论奠定了基础。

## 直观解释

射影 Nullstellensatz 告诉我们：**射影空间中的几何对象（代数簇）与多项式环中的代数对象（齐次理想）之间存在一种精密的词典**。与仿射情形不同，射影空间中的点是“方向”而非“位置”，因此需要用到齐次多项式（所有项次数相同）才能良定义地讨论零点。定理的核心是：给定一组齐次方程，其解集对应的理想恰好是生成这组方程的理想的根式；反之，给定一个根式齐次理想，也存在唯一一个代数簇作为其零点集。

## 形式化表述

设 $k$ 为代数闭域，$S = k[x_0, x_1, \ldots, x_n]$ 为分次多项式环，$S_+ = (x_0, \ldots, x_n)$ 为 irrelevant ideal。

对射影空间 $\mathbb{P}^n_k$ 的子集 $X$，定义其齐次理想为：

$$I(X) = \{f \in S : f \text{ 齐次且 } f(P) = 0 \text{ 对所有 } P \in X\}$$

对齐次理想 $I \subseteq S$，定义其射影零点集为：

$$V_p(I) = \{P \in \mathbb{P}^n_k : f(P) = 0 \text{ 对所有齐次 } f \in I\}$$

**射影 Nullstellensatz**：

1. 对射影子簇 $X \subseteq \mathbb{P}^n$，有 $V_p(I(X)) = X$
2. 对齐次理想 $I \subseteq S$：
   - 若 $V_p(I) = \emptyset$，则存在 $N$ 使得 $S_+^N \subseteq I$
   - 若 $V_p(I) \neq \emptyset$，则 $I(V_p(I)) = \sqrt{I}$

## 证明思路

1. **仿射锥构造**：对射影子集 $X \subseteq \mathbb{P}^n$，构造其在 $\mathbb{A}^{n+1}$ 中的仿射锥 $C(X) = \{0\} \cup \pi^{-1}(X)$，其中 $\pi: \mathbb{A}^{n+1} \setminus \{0\} \to \mathbb{P}^n$ 为自然投影
2. **理想对应**：证明 $I_p(X) = I_a(C(X))$，即射影理想等于仿射锥的仿射理想
3. **应用仿射 Nullstellensatz**：对 $C(X)$ 应用 Hilbert Nullstellensatz
4. **齐次性处理**：利用齐次理想的根仍是齐次理想这一性质，将结论投影回射影空间

核心在于通过仿射锥这座“桥梁”，把射影问题转化为已解决的仿射问题。

## 示例

### 示例 1：射影直线

$\mathbb{P}^1_k$ 中的点对应于 $k^2$ 中过原点的直线。一个齐次多项式 $f(x_0, x_1)$ 的零点集是有限个点，除非 $f$ 恒为零。

### 示例 2：射影平面曲线

$\mathbb{P}^2_k$ 中，齐次多项式 $f(x,y,z) = x^2 + y^2 - z^2$ 定义了一条二次曲线（圆锥曲线）。其理想 $I = (x^2 + y^2 - z^2)$ 是素理想，故 $V_p(I)$ 是不可约簇。

### 示例 3：空簇与 irrelevant ideal

理想 $I = (x_0, x_1, \ldots, x_n) = S_+$ 的射影零点集为空，因为在射影空间中没有全坐标为零的点。此时 $V_p(S_+) = \emptyset$，而 $\sqrt{S_+} = S_+$，符合射影 Nullstellensatz 的第一种情形。

## 应用

- **代数簇分类**：射影簇与齐次理想的对应使得几何问题可以代数化
- **概型理论**：射影概型 $\text{Proj}(S)$ 的构造依赖于齐次理想的零点理论
- **相交理论**：Bézout 定理、Chow 群与相交乘积的研究基础
- **不变量理论**：射影几何中不变量与模空间的构造
- **弦理论与镜像对称**：Calabi-Yau 流形的代数几何描述

## 相关概念

- 仿射 Nullstellensatz (Affine Nullstellensatz)：Hilbert 在仿射空间中的对应定理
- 齐次理想 (Homogeneous Ideal)：由齐次多项式生成的理想
- 仿射锥 (Affine Cone)：射影簇在仿射空间中的提升
- Irrelevant Ideal：$(x_0, \ldots, x_n)$，对应空射影簇
- Proj 构造 (Proj Construction)：从分次环构造射影概型

## 参考

### 教材

- [Hartshorne. Algebraic Geometry. Springer, 1977. Chapter I, Section 2]
- [Shafarevich. Basic Algebraic Geometry 1. Springer, 3rd edition, 2013. Chapter 1]

### 在线资源

- [Mathlib4 文档 - ProjectiveSpectrum][https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Scheme.html]
- **注意**：Mathlib4 中射影 Nullstellensatz 的完整独立定理声明目前仍在发展中，现有材料分散于 ProjectiveSpectrum 和 GradedAlgebra 模块。

---

*最后更新：2026-04-15 | 版本：v1.0.0*
