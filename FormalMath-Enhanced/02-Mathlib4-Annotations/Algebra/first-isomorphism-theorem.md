---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# 群同态基本定理 (First Isomorphism Theorem)

## Mathlib4 引用

```lean
import Mathlib.GroupTheory.QuotientGroup

namespace QuotientGroup

variable {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
variable {H : Type*} [Group H]

/-- 群同态基本定理：$G/\ker(\varphi) \cong \text{im}(\varphi)$ -/
noncomputable def quotientKerEquivRange (φ : G →* H) :
    (G ⧸ MonoidHom.ker φ) ≃* MonoidHom.range φ :=
  MulEquiv.trans (quotientKerEquivOfSurjective φ (fun _ ↦ by aesop))
    (rangeEquiv_eq φ)

end QuotientGroup
```

## 数学背景

群同态基本定理（也称为第一同构定理）是抽象代数中的核心定理，由 Emmy Noether 在 20 世纪初系统化地整理和表述。该定理建立了群同态、商群和同构之间的深刻联系，是理解群结构的根本工具。

## 直观解释

这个定理告诉我们：**商掉同态的核，就得到同态的像**。可以想象为将群 $G$ 通过同态 $\varphi$ "投影"到群 $H$ 时，那些映射到单位元的元素（即核）被"压缩"成一个点，而不同的陪集对应像中不同的元素。

直观上，这就像是拍摄照片时，镜头（同态）将三维世界（群 $G$）映射到二维平面（群 $H$），而所有映射到同一个像素点的三维点构成核的一个陪集。

## 形式化表述

设 $\varphi: G \to H$ 是群同态，则：

$$G / \ker(\varphi) \cong \text{im}(\varphi)$$

其中：

- $\ker(\varphi) = \{g \in G : \varphi(g) = e_H\}$ 是同态的核
- $\text{im}(\varphi) = \{\varphi(g) : g \in G\}$ 是同态的像
- $\cong$ 表示群同构

## 证明思路

1. **良定性**：验证映射 $\bar{\varphi}: g\ker(\varphi) \mapsto \varphi(g)$ 是良定义的
2. **同态性**：证明 $\bar{\varphi}$ 保持群运算
3. **单射性**：若 $\bar{\varphi}(g_1\ker) = \bar{\varphi}(g_2\ker)$，则 $g_1\ker = g_2\ker$
4. **满射性**：像中每个元素都有原像

关键在于核的陪集恰好对应像中的不同元素。

## 示例

### 示例 1：行列式映射

考虑 $\det: GL_2(\mathbb{R}) \to \mathbb{R}^\times$（可逆矩阵到非零实数）。

- 核：$\ker(\det) = SL_2(\mathbb{R})$（行列式为 1 的矩阵，特殊线性群）
- 像：$\text{im}(det) = \mathbb{R}^\times$（满射）

结论：$GL_2(\mathbb{R}) / SL_2(\mathbb{R}) \cong \mathbb{R}^\times$

### 示例 2：模 $n$ 同态

考虑 $\varphi: \mathbb{Z} \to \mathbb{Z}_n$，$\varphi(k) = k \bmod n$。

- 核：$\ker(\varphi) = n\mathbb{Z}$（$n$ 的倍数）
- 像：$\text{im}(\varphi) = \mathbb{Z}_n$（满射）

结论：$\mathbb{Z}/n\mathbb{Z} \cong \mathbb{Z}_n$

### 示例 3：符号同态

考虑符号同态 $\text{sgn}: S_n \to \{1, -1\}$。

- 核：$\ker(\text{sgn}) = A_n$（交错群，偶置换）
- 像：$\text{im}(\text{sgn}) = \{1, -1\}$

结论：$S_n / A_n \cong \mathbb{Z}_2$

## 应用

- **分类定理**：用于分类有限群的结构
- **表示理论**：研究群的线性表示
- **伽罗瓦理论**：连接域扩张与群论
- **代数拓扑**：基本群和同调群的研究

## 相关概念

- [群同态 (Group Homomorphism)](./group-homomorphism.md)：保持群结构的映射
- [正规子群 (Normal Subgroup)](./normal-subgroup.md)：作为核的子群
- [商群 (Quotient Group)](./quotient-group.md)：通过正规子群构造的群
- [第二同构定理 (Second Isomorphism Theorem)](./second-isomorphism-theorem.md)
- [第三同构定理 (Third Isomorphism Theorem)](./third-isomorphism-theorem.md)

## 参考

### 教材

- [Dummit & Foote. Abstract Algebra. Wiley, 3rd edition, 2004. Section 3.3]
- [Aluffi. Algebra: Chapter 0. AMS, 2009. Section II.7]

### 历史文献

- [Noether. Abstrakter Aufbau der Idealtheorie in algebraischen Zahl- und Funktionenkörpern. 1927]

### 在线资源

- [Mathlib4 文档 - QuotientGroup](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/QuotientGroup.html)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
