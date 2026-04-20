---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: 正规子群对应定理 (Normal Subgroup Correspondence)
---
# 正规子群对应定理 (Normal Subgroup Correspondence)

## Mathlib4 引用

```lean
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace NormalSubgroupCorrespondence

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

/-- 正规子群对应定理 -/
theorem normal_correspondence :
    { H : Subgroup G // N ≤ H ∧ H.Normal } ≃
    { K : Subgroup (G ⧸ N) // K.Normal } := by
  refine {
    toFun := fun H => ⟨H.1.map (QuotientGroup.mk' N), by sorry⟩,
    invFun := fun K => ⟨K.1.comap (QuotientGroup.mk' N), by sorry⟩,
    left_inv := sorry,
    right_inv := sorry
  }

/-- 商群的正规子群提升 -/
theorem quotient_normal_lift {K : Subgroup (G ⧸ N)} (hK : K.Normal) :
    ∃! H : Subgroup G, N ≤ H ∧ H.Normal ∧ H.map (QuotientGroup.mk' N) = K := by
  -- 对应的双射性
  sorry

end NormalSubgroupCorrespondence
```

## 数学背景

正规子群对应定理（也称为第四同构定理或格同构定理的正规子群版本）是群论中的基本结构定理，它建立了群的商群结构与原群包含核的正规子群结构之间的一一对应。这一定理是理解商群构造的基石，揭示了商群 $G/N$ 的正规子群与原群 $G$ 中包含 $N$ 的正规子群之间存在典范的双射，并且这个双射保持包含关系、交、并等格运算。它是格同构定理（Lattice Isomorphism Theorem）的特例，在线性代数（向量空间商）、环论（理想商）和模论中有直接类比，是抽象代数的通用语言。

### 商群的构造

**定义（正规子群）**：设 $G$ 是群，$N \leq G$ 是子群。$N$ 称为**正规的**（normal），记作 $N \trianglelefteq G$，如果对所有 $g \in G$，$gNg^{-1} = N$（等价地，$gN = Ng$）。

**定义（商群）**：若 $N \trianglelefteq G$，则 $G$ 关于 $N$ 的**商群**（quotient group）定义为左陪集的集合：

$$G/N = \{gN : g \in G\}$$

群运算为 $(gN)(hN) = (gh)N$。$N$ 的正规性保证这个运算是良定义的。

**自然投影**：映射 $\pi: G \to G/N$，$\pi(g) = gN$ 是满同态，且 $\ker(\pi) = N$。

### 子群在投影下的像与原像

对同态 $\varphi: G \to H$，有标准操作：
- **像**（image）：对 $S \leq G$，$\varphi(S) = \{\varphi(s) : s \in S\} \leq H$；
- **原像**（preimage）：对 $T \leq H$，$\varphi^{-1}(T) = \{g \in G : \varphi(g) \in T\} \leq G$。

## 正规子群对应定理的陈述

**定理（正规子群对应定理）**：设 $G$ 是群，$N \trianglelefteq G$ 是正规子群，$\pi: G \to G/N$ 是自然投影。则映射：

$$\Phi: \{H \leq G : N \leq H \text{ 且 } H \trianglelefteq G\} \to \{K \leq G/N : K \trianglelefteq G/N\}$$

$$\Phi(H) = \pi(H) = H/N$$

是双射，其逆为 $\Phi^{-1}(K) = \pi^{-1}(K)$。

更精确地，这个对应满足：
1. $\Phi$ 和 $\Phi^{-1}$ 互逆；
2. $H_1 \leq H_2 \iff \Phi(H_1) \leq \Phi(H_2)$（保持包含）；
3. $\Phi(H_1 \cap H_2) = \Phi(H_1) \cap \Phi(H_2)$（保持交）；
4. $\Phi(\langle H_1 \cup H_2 \rangle) = \langle \Phi(H_1) \cup \Phi(H_2) \rangle$（保持并的闭包，即生成的子群）；
5. $[H_2 : H_1] = [\Phi(H_2) : \Phi(H_1)]$（保持指数，当有限时）。

## 证明

### 对应映射的良定义性

**引理1**：若 $N \leq H \leq G$ 且 $H \trianglelefteq G$，则 $\pi(H) = H/N \trianglelefteq G/N$。

**证明**：设 $hN \in H/N$，$gN \in G/N$。则：

$$(gN)(hN)(gN)^{-1} = ghg^{-1} N$$

由于 $H \trianglelefteq G$，$ghg^{-1} \in H$，故 $ghg^{-1} N \in H/N$。因此 $H/N \trianglelefteq G/N$。 $\square$

**引理2**：若 $K \trianglelefteq G/N$，则 $\pi^{-1}(K) \trianglelefteq G$ 且 $N \leq \pi^{-1}(K)$。

**证明**：$\pi^{-1}(K)$ 是同态下正规子群的原像，故正规。$N = \ker(\pi) = \pi^{-1}(\{eN\}) \leq \pi^{-1}(K)$（因为 $\{eN\} \leq K$）。 $\square$

### 双射性的证明

**证明**：设 $\mathcal{H} = \{H \leq G : N \leq H, H \trianglelefteq G\}$，$\mathcal{K} = \{K \leq G/N : K \trianglelefteq G/N\}$。

定义 $\Phi: \mathcal{H} \to \mathcal{K}$，$\Phi(H) = H/N$；$\Psi: \mathcal{K} \to \mathcal{H}$，$\Psi(K) = \pi^{-1}(K)$。

**验证 $\Psi \circ \Phi = \text{id}_{\mathcal{H}}$**：

$$(\Psi \circ \Phi)(H) = \pi^{-1}(H/N) = \{g \in G : gN \in H/N\}$$

若 $g \in H$，则 $gN \in H/N$，故 $g \in \pi^{-1}(H/N)$。反之，若 $gN \in H/N$，则 $gN = hN$ 对某个 $h \in H$，故 $h^{-1}g \in N \leq H$，因此 $g = h(h^{-1}g) \in H$。所以 $\pi^{-1}(H/N) = H$。

**验证 $\Phi \circ \Psi = \text{id}_{\mathcal{K}}$**：

$$(\Phi \circ \Psi)(K) = \pi(\pi^{-1}(K))$$

由于 $\pi$ 是满射，$\pi(\pi^{-1}(K)) = K$。具体地，$k \in K \Rightarrow k = gN$ 对某个 $g \in G \Rightarrow g \in \pi^{-1}(K) \Rightarrow gN \in \pi(\pi^{-1}(K))$。

因此 $\Phi$ 是双射，$\Psi = \Phi^{-1}$。 $\square$

### 格性质的保持

**包含关系的保持**：$H_1 \leq H_2 \Rightarrow H_1/N \subseteq H_2/N \Rightarrow H_1/N \leq H_2/N$。反之，若 $H_1/N \leq H_2/N$，取 $h \in H_1$，则 $hN \in H_1/N \leq H_2/N$，故 $hN = h'N$ 对某个 $h' \in H_2$，$h^{-1}h' \in N \leq H_2$，$h = h'(h'^{-1}h) \in H_2$。

**交的保持**：$\pi(H_1 \cap H_2) \subseteq \pi(H_1) \cap \pi(H_2)$ 是显然的。反之，若 $gN \in \pi(H_1) \cap \pi(H_2)$，则存在 $h_1 \in H_1$，$h_2 \in H_2$ 使得 $gN = h_1N = h_2N$。于是 $h_1^{-1}h_2 \in N \leq H_1$，$h_2 = h_1(h_1^{-1}h_2) \in H_1$，故 $h_2 \in H_1 \cap H_2$，$gN = h_2N \in \pi(H_1 \cap H_2)$。

## 例子

### 例子1：整数模子群

设 $G = \mathbb{Z}$，$N = 6\mathbb{Z}$。$G/N = \mathbb{Z}/6\mathbb{Z} = \{0, 1, 2, 3, 4, 5\}$。

包含 $6\mathbb{Z}$ 的 $\mathbb{Z}$ 的子群是 $d\mathbb{Z}$，其中 $d | 6$，即 $6\mathbb{Z}$，$3\mathbb{Z}$，$2\mathbb{Z}$，$\mathbb{Z}$。

$\mathbb{Z}/6\mathbb{Z}$ 的子群：$\{0\}$，$\{0, 3\}$，$\{0, 2, 4\}$，$\mathbb{Z}/6\mathbb{Z}$。

对应关系：
- $6\mathbb{Z} \leftrightarrow \{0\}$
- $3\mathbb{Z} \leftrightarrow \{0, 3\} = \langle 3 \rangle$
- $2\mathbb{Z} \leftrightarrow \{0, 2, 4\} = \langle 2 \rangle$
- $\mathbb{Z} \leftrightarrow \mathbb{Z}/6\mathbb{Z}$

由于 $\mathbb{Z}$ 是Abel群，所有子群都正规，对应定理给出了包含 $6\mathbb{Z}$ 的子群与 $\mathbb{Z}/6\mathbb{Z}$ 的所有子群之间的双射。

### 例子2：对称群

设 $G = S_4$，$N = V_4 = \{e, (12)(34), (13)(24), (14)(23)\}$（Klein四元群）。$V_4 \trianglelefteq S_4$，且 $S_4/V_4 \cong S_3$。

$S_3$ 的正规子群：$\{e\}$，$A_3 = \langle (123) \rangle$，$S_3$。

对应到 $S_4$ 中包含 $V_4$ 的正规子群：
- $\{e\} \leftrightarrow V_4$
- $A_3 \leftrightarrow A_4$（交错群）
- $S_3 \leftrightarrow S_4$

这与已知结果一致：$A_4/V_4 \cong A_3$（3阶循环群），$S_4/V_4 \cong S_3$。

### 例子3：直积群

设 $G = \mathbb{Z} \times \mathbb{Z}$，$N = \{(2m, 2n) : m, n \in \mathbb{Z}\} = 2\mathbb{Z} \times 2\mathbb{Z}$。$G/N \cong \mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/2\mathbb{Z}$（Klein四元群）。

$G/N$ 的正规子群（所有子群都正规，因为是Abel群）：$\{(0,0)\}$，三个2阶子群 $\langle (1,0) \rangle$，$\langle (0,1) \rangle$，$\langle (1,1) \rangle$，以及 $G/N$ 本身。

对应到 $G$ 中包含 $N$ 的子群：
- $\{(0,0)\} \leftrightarrow 2\mathbb{Z} \times 2\mathbb{Z}$
- $\langle (1,0) \rangle \leftrightarrow \mathbb{Z} \times 2\mathbb{Z}$
- $\langle (0,1) \rangle \leftrightarrow 2\mathbb{Z} \times \mathbb{Z}$
- $\langle (1,1) \rangle \leftrightarrow \{(m,n) : m \equiv n \pmod{2}\}$
- $G/N \leftrightarrow \mathbb{Z} \times \mathbb{Z}$

## 应用

### 1. 群的分解和合成列

正规子群对应定理是理解群合成列（composition series）和可解列（solvable series）的基础。Jordan-Hölder定理断言任何有限群的两个合成列有相同的合成因子（在同构和重排意义下）。正规子群对应定理允许我们通过商群来研究原群的合成列结构。

### 2. 同调代数中的长正合列

在群同调中，对短正合列 $1 \to N \to G \to G/N \to 1$，有长正合列连接 $H_*(N)$、$H_*(G)$ 和 $H_*(G/N)$。正规子群对应定理帮助理解中间群 $G$ 的结构如何通过 $N$ 和 $G/N$ 来重构。

### 3. 格同构定理的基础

正规子群对应定理是更一般的格同构定理的基础。对任意同态 $\varphi: G \to H$，有对应定理建立 $\{G \text{ 中包含 } \ker\varphi \text{ 的子群}\}$ 与 $\{\varphi(G) \text{ 的子群}\}$ 之间的双射。正规子群版本是当 $H = G/N$、$\varphi = \pi$ 时的特例。

### 4. Galois对应

在Galois理论中，域扩张的Galois群与子域格之间存在反序同构。正规子群对应于正规扩张，商群对应于中间域的Galois群。正规子群对应定理在Galois理论中表现为：对Galois扩张 $E/F$，中间域 $K$（$F \subseteq K \subseteq E$）对应于 $\text{Gal}(E/F)$ 的子群，而正规中间域对应于正规子群，且 $\text{Gal}(K/F) \cong \text{Gal}(E/F)/\text{Gal}(E/K)$。

---

*最后更新：2026-04-03 | 版本：v1.0.0*
