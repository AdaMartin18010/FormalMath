---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: Sylow 定理 (Sylow Theorems)
---
# Sylow 定理 (Sylow Theorems)

## Mathlib4 引用

```lean
import Mathlib.GroupTheory.Sylow

namespace SylowTheorems

variable {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime]

/-- Sylow 第一定理：对每个整除 |G| 的素数幂 pⁿ，G 存在阶为 pⁿ 的子群 -/
theorem exists_subgroup_card_pow_prime {n : ℕ} (h : p ^ n ∣ Nat.card G) :
    ∃ H : Subgroup G, Nat.card H = p ^ n := by
  -- 参见 Mathlib4 GroupTheory.Sylow
  sorry

/-- Sylow 第二定理：有限群的所有 Sylow p-子群互相共轭 -/
theorem sylow_conjugate [Finite (Sylow p G)] (P Q : Sylow p G) :
    ∃ g : G, Q = (P.map (MulAut.conj g).toMonoidHom) := by
  -- 参见 Mathlib4 Sylow.isPretransitive_of_finite
  sorry

/-- Sylow 第三定理：Sylow p-子群的个数 n_p ≡ 1 (mod p) -/
theorem card_sylow_modEq_one [Finite (Sylow p G)] :
    Nat.card (Sylow p G) ≡ 1 [MOD p] := by
  -- 参见 Mathlib4 card_sylow_modEq_one
  sorry

end SylowTheorems
```

## 数学背景

Sylow 定理是有限群论的三块基石，由挪威数学家 Peter Ludwig Mejdell Sylow 于1872年证明。这些定理深刻揭示了有限群中 $p$-子群的结构：对任意整除群阶的素数 $p$，都存在某种“最大”的 $p$-子群（Sylow $p$-子群），它们的个数和共轭关系都受到严格约束。Sylow 定理为分类有限单群、研究群的可解性和对称性提供了不可或缺的工具。

## 直观解释

Sylow 定理可以形象地比作在有限群中“寻找最大素数幂部队”：

- **第一定理**：只要素数幂 $p^n$ 能整除群的“总人数”$|G|$，就必定存在一支人数恰好为 $p^n$ 的“小分队”。
- **第二定理**：所有人数最多的 $p$-小分队彼此之间可以通过群内部的“重组”（共轭作用）互相转化，本质上是同构的。
- **第三定理**：这类最大 $p$-小分队的总数 $n_p$ 满足两个约束：$n_p$ 整除 $|G|/p^n$，且 $n_p \equiv 1 \pmod{p}$。

## 形式化表述

设 $G$ 为有限群，$|G| = p^n \cdot m$，其中 $p$ 为素数且 $p \nmid m$。

1. **存在性**：$G$ 存在阶为 $p^n$ 的子群，称为 **Sylow $p$-子群**。
2. **共轭性**：$G$ 的任意两个 Sylow $p$-子群 $P, Q$ 互相共轭，即存在 $g \in G$ 使得 $Q = gPg^{-1}$。
3. **计数性**：设 $n_p$ 为 Sylow $p$-子群的个数，则：
   - $n_p \mid m$
   - $n_p \equiv 1 \pmod{p}$

## 证明思路

1. **第一定理**：对集合 $X = G^{p^n}$ 的某特定子集构造群作用，利用轨道-稳定子定理证明存在大小为 $p^n$ 的轨道，对应子群。
2. **第二定理**：考虑 Sylow $p$-子群 $P$ 在所有 Sylow $p$-子群集合上的共轭作用。由轨道公式，轨道大小整除 $|P| = p^n$。结合第三定理的计数信息，轨道大小只能为 1，从而所有 Sylow 子群共轭。
3. **第三定理**：让固定 Sylow 子群 $P$ 在所有 Sylow 子群集合 $Syl_p(G)$ 上共轭作用。利用 $p$-群作用的不动点公式：$|Syl_p(G)| \equiv |Fix(P)| \pmod{p}$，而 $Fix(P) = \{P\}$，故 $n_p \equiv 1 \pmod{p}$。

## 示例

### 示例 1：对称群 $S_3$

$|S_3| = 6 = 2 \cdot 3$。

- Sylow 2-子群：阶为 2，共 3 个（$\langle(12)\rangle, \langle(13)\rangle, \langle(23)\rangle$），$n_2 = 3 \equiv 1 \pmod{2}$。
- Sylow 3-子群：阶为 3，共 1 个（$\langle(123)\rangle$），$n_3 = 1 \equiv 1 \pmod{3}$，且为正规子群。

### 示例 2：阶为 15 的群

$|G| = 15 = 3 \cdot 5$。

- $n_3 \equiv 1 \pmod{3}$ 且 $n_3 \mid 5$，故 $n_3 = 1$。
- $n_5 \equiv 1 \pmod{5}$ 且 $n_5 \mid 3$，故 $n_5 = 1$。
- 两个 Sylow 子群都正规，因此 $G \cong \mathbb{Z}_3 \times \mathbb{Z}_5 \cong \mathbb{Z}_{15}$，即 15 阶群必为循环群。

### 示例 3：阶为 21 的群

$|G| = 21 = 3 \cdot 7$。

- $n_7 \equiv 1 \pmod{7}$ 且 $n_7 \mid 3$，故 $n_7 = 1$（Sylow 7-子群正规）。
- $n_3 \equiv 1 \pmod{3}$ 且 $n_3 \mid 7$，故 $n_3 = 1$ 或 $7$。
- 当 $n_3 = 1$ 时 $G$ 为循环群；当 $n_3 = 7$ 时 $G$ 为非交换群（存在半直积结构）。

## 应用

- **有限单群分类**：确定群的正规子群结构
- **群的可解性**：Burnside $p^a q^b$ 定理证明某些阶的群必可解
- **伽罗瓦理论**：伽罗瓦群的结构分析与多项式根式可解性
- **组合设计**：Steiner 系统与传递群作用
- **编码理论**：某些纠错码的构造依赖特定 $p$-群结构

## 相关概念

- $p$-子群 ($p$-Subgroup)：阶为素数幂的子群
- 正规子群 (Normal Subgroup)：左右陪集相等的子群
- 共轭作用 (Conjugation Action)：群在自身子群集合上的内自同构作用
- 轨道-稳定子定理 (Orbit-Stabilizer Theorem)：群作用的基本计数工具
- 半直积 (Semidirect Product)：由正规子群与补子群构造的群扩张

## 参考

### 教材

- [Dummit & Foote. Abstract Algebra. Wiley, 3rd edition, 2004. Section 4.5]
- [Artin. Algebra. Pearson, 2nd edition, 2010. Chapter 7]

### 历史文献

- [Sylow. Théorèmes sur les groupes de substitutions. Mathematische Annalen, 1872]

### 在线资源

- [Mathlib4 文档 - Sylow][https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Sylow.html]

---

*最后更新：2026-04-15 | 版本：v1.0.0*
