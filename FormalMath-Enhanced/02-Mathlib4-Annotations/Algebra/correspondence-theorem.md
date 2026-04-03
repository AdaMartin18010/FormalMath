# 正规子群对应定理 (Correspondence Theorem)

## Mathlib4 引用

```lean
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace QuotientGroup

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

/-- 正规子群对应定理：商群的子群与包含N的子群一一对应 -/
theorem correspondence_theorem :
    Subgroup (G ⧸ N) ≃ { H : Subgroup G // N ≤ H } where
  toFun H' := ⟨H'.comap (mk' N), by simp⟩
  invFun H := H.1.map (mk' N)
  left_inv := by
    intro H'
    ext x
    simp
  right_inv := by
    intro H
    ext x
    simp [H.2]

end QuotientGroup
```

## 数学背景

正规子群对应定理，也称为格同构定理或第四同构定理，由Richard Dedekind在19世纪末系统化阐述。该定理揭示了商群结构与原群结构之间的深刻联系，是群论中理解商结构的重要工具。它为研究群的层次结构提供了理论基础。

## 直观解释

正规子群对应定理告诉我们：**在商群中的子群与原群中包含正规子群的子群之间存在完美的一一对应**。

想象一面镜子（正规子群N），镜子前的物体（包含N的子群）在镜子中都有唯一的像（商群的子群），反之亦然。这种对应不仅保持包含关系，还保持正规性——商群中的正规子群对应原群中的正规子群。

## 形式化表述

设 $G$ 是群，$N \trianglelefteq G$ 是正规子群，则存在双射：

$$\{ H \leq G : N \subseteq H \} \longleftrightarrow \{ K \leq G/N \}$$

其中：

- $H \mapsto H/N$ （向下映射）
- $\pi^{-1}(K) \mapsfrom K$ （向上映射，$\pi: G \to G/N$ 是自然投影）

且此对应保持：

- 包含关系：$H_1 \subseteq H_2 \Leftrightarrow H_1/N \subseteq H_2/N$
- 正规性：$H \trianglelefteq G \Leftrightarrow H/N \trianglelefteq G/N$

## 证明思路

1. **构造映射**：定义从原群子群到商群子群的映射 $H \mapsto H/N$
2. **良定义性**：验证若 $N \leq H$ 则 $H/N$ 确实是 $G/N$ 的子群
3. **单射性**：证明不同的 $H$ 对应不同的 $H/N$
4. **满射性**：证明商群的每个子群都是某个 $H/N$ 的形式
5. **保持正规性**：验证正规子群在此对应下保持正规性

核心洞察是商映射的核恰好是 $N$，这使得包含 $N$ 的子群信息能完整传递到商群中。

## 示例

### 示例 1：整数群商群

考虑 $G = \mathbb{Z}$，$N = 6\mathbb{Z}$。

包含 $6\mathbb{Z}$ 的子群为 $d\mathbb{Z}$，其中 $d$ 整除 6：

- $6\mathbb{Z}$，$3\mathbb{Z}$，$2\mathbb{Z}$，$\mathbb{Z}$

商群 $\mathbb{Z}/6\mathbb{Z} \cong \mathbb{Z}_6$ 的子群为：

- $\{0\}$，$\{0, 3\}$，$\{0, 2, 4\}$，$\mathbb{Z}_6$

对应关系：$d\mathbb{Z}/6\mathbb{Z} \cong \mathbb{Z}_{6/d}$

### 示例 2：对称群 $S_4$

设 $G = S_4$，$N = V_4$（Klein四元群，正规子群）。

$G/N \cong S_3$。$S_3$ 的子群对应 $S_4$ 中包含 $V_4$ 的子群：

- $\{e\} \leftrightarrow V_4$
- $A_3 \leftrightarrow A_4$
- $S_3$（3个共轭）$\leftrightarrow$ 3个 $D_8$（二面体群）
- $S_3 \leftrightarrow S_4$

## 应用

- **群结构分析**：通过商群结构理解原群的子群格
- **正规子群判定**：将正规子群的判定从复杂群转移到简单商群
- **合成列理论**：用于构造群的合成列
- **伽罗瓦理论**：对应域扩张的中间域

## 相关概念

- [正规子群 (Normal Subgroup)](./normal-subgroup.md)：左右陪集相等的子群
- [商群 (Quotient Group)](./quotient-group.md)：由正规子群构造的新群
- [同构定理 (Isomorphism Theorem)](./isomorphism-theorem.md)：群论基本同构结果
- [子群格 (Subgroup Lattice)](./subgroup-lattice.md)：群的所有子群构成的格
- [伽罗瓦对应 (Galois Correspondence)](./galois-correspondence.md)：域论中的对应定理

## 参考

### 教材

- [M. Artin. Algebra. Pearson, 2nd edition, 2010. Chapter 2]
- [Dummit & Foote. Abstract Algebra. Wiley, 3rd edition, 2004. Section 3.3]

### 历史文献

- [Dedekind. Über die Theorie der ganzen algebraischen Zahlen. 1871]

### 在线资源

- [Mathlib4 文档 - QuotientGroup](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/QuotientGroup/Basic.html)
- [Groupprops - Correspondence theorem](https://groupprops.subwiki.org/wiki/Correspondence_theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
