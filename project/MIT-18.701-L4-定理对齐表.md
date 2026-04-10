---
msc_primary: 20-01
title: MIT 18.701 Algebra I L4定理级对齐表
processed_at: '2026-04-10'
course_code: MIT 18.701
course_name: Algebra I
instructor: Michael Artin (教材)
textbook: "Michael Artin, Algebra (2nd Edition)"
alignment_level: L4 (定理级)
version: v1.0
---

# MIT 18.701 Algebra I L4定理级对齐表

**课程代码**: MIT 18.701  
**课程名称**: Algebra I  
**主教材**: Michael Artin, "Algebra" (2nd Edition)  
**对齐等级**: L4（定理证明级完整性验证）  
**版本**: v1.0

---

## 目录

1. [概述与文档用途](#1-概述与文档用途)
2. [定理对齐总表](#2-定理对齐总表)
3. [拉格朗日定理详解](#3-拉格朗日定理详解)
4. [同态基本定理详解](#4-同态基本定理详解)
5. [第一同构定理详解](#5-第一同构定理详解)
6. [对应定理详解](#6-对应定理详解)
7. [Sylow第一定理详解](#7-sylow第一定理详解)
8. [轨道-稳定化子定理详解](#8-轨道-稳定化子定理详解)
9. [类方程详解](#9-类方程详解)
10. [有限Abel群结构定理详解](#10-有限abel群结构定理详解)
11. [证明技巧总结](#11-证明技巧总结)
12. [Lean4形式化对应](#12-lean4形式化对应)
13. [教学建议](#13-教学建议)

---

## 1. 概述与文档用途

### 1.1 文档目标

本文档提供MIT 18.701 Algebra I课程核心定理的**证明完整性验证**，确保FormalMath资源与MIT课程标准在L4（定理证明级）完全对齐。

### 1.2 完整性等级说明

| 等级 | 符号 | 含义 |
|-----|------|------|
| 完整 | ✅ | 定理陈述完整，证明详细，所有步骤可验证 |
| 框架 | ⚠️ | 定理陈述完整，证明框架存在，部分细节待补充 |
| 待补充 | ⏳ | 定理陈述存在，证明缺失或待建设 |
| 待建设 | 🔧 | 概念存在，但文档或形式化尚未创建 |

### 1.3 优先级说明

| 优先级 | 含义 | 说明 |
|-------|------|------|
| P0 | 最高优先级 | 群论基础核心定理，必须先完成 |
| P1 | 高优先级 | 群论进阶定理，构建理论体系必需 |
| P2 | 中优先级 | 重要结构定理，可在基础完成后建设 |

### 1.4 证明完整性评估维度

| 维度 | 描述 | 评估标准 |
|-----|------|---------|
| **陈述完整性** | 定理条件、结论是否完整 | 与Artin教材一致 |
| **证明详细度** | 证明步骤是否详尽 | 每一步可验证 |
| **思路清晰度** | 证明思路是否清晰呈现 | 有明确的策略说明 |
| **形式化支持** | 是否有Lean4形式化 | Lean4代码存在性 |

### 1.5 参考文档

- **MIT 18.701 L3定义对齐表**: `project/MIT-18.701-L3-定义对齐表.md`
- **MIT 18.701语义级对齐手册**: `project/MIT-18.701-语义级对齐手册.md`
- **拉格朗日定理完整证明**: `docs/02-代数结构/02-核心理论/群论/定理证明/拉格朗日定理-完整证明.md`
- **同态基本定理完整证明**: `docs/02-代数结构/02-核心理论/群论/定理证明/同态基本定理-完整证明.md`

---

## 2. 定理对齐总表

### 2.1 核心定理对齐汇总

| 定理名称 | Artin章节 | FormalMath文档 | 证明完整性 | Lean4形式化 | 优先级 |
|---------|----------|----------------|------------|-------------|--------|
| **拉格朗日定理** | Ch 2.4 | `docs/02-代数结构/02-核心理论/群论/定理证明/拉格朗日定理-完整证明.md` | ⚠️ 框架 | ✅ 有 | P0 |
| **同态基本定理** | Ch 2.10 | `docs/02-代数结构/02-核心理论/群论/定理证明/同态基本定理-完整证明.md` | ⚠️ 框架 | 🔧 待建设 | P0 |
| **第一同构定理** | Ch 2.10 | `docs/02-代数结构/02-核心理论/群论/同构定理.md` | ⚠️ 框架 | 🔧 待建设 | P0 |
| **对应定理** | Ch 2.10 | `docs/02-代数结构/02-核心理论/群论/对应定理.md` | ⚠️ 框架 | 🔧 待建设 | P1 |
| **Sylow第一定理** | Ch 6.4 | `docs/02-代数结构/02-核心理论/群论/Sylow定理.md` | ⚠️ 框架 | 🔧 待建设 | P1 |
| **轨道-稳定化子定理** | Ch 6.8 | `docs/02-代数结构/02-核心理论/群论/群作用.md` | ⚠️ 框架 | 🔧 待建设 | P1 |
| **类方程** | Ch 6.9 | `docs/02-代数结构/02-核心理论/群论/类方程.md` | ⚠️ 框架 | 🔧 待建设 | P1 |
| **有限Abel群结构定理** | Ch 14.7 | `docs/02-代数结构/02-核心理论/群论/有限Abel群.md` | 🔧 待建设 | 🔧 待建设 | P2 |

### 2.2 对齐统计汇总

| 完整性等级 | 数量 | 百分比 |
|-----------|------|--------|
| 完整 (✅) | 0 | 0% |
| 框架 (⚠️) | 7 | 87.5% |
| 待建设 (🔧) | 1 | 12.5% |

**优先级分布**:
| 优先级 | 数量 | 百分比 |
|-------|------|--------|
| P0 (最高) | 3 | 37.5% |
| P1 (高) | 4 | 50% |
| P2 (中) | 1 | 12.5% |

**Lean4形式化状态**:
| 状态 | 数量 | 百分比 |
|------|------|--------|
| 有形式化 | 1 | 12.5% |
| 待建设 | 7 | 87.5% |

**结论**: FormalMath与MIT 18.701在7个核心定理上已有框架，证明详细度待补充，Lean4形式化大部分待建设。

---

## 3. 拉格朗日定理详解

### 3.1 Artin教材原文

> **Theorem 2.4.9 (Lagrange's Theorem)**: Let $H$ be a subgroup of a finite group $G$. The order of $H$ divides the order of $G$:
> $$|G| = [G:H] \cdot |H|$$
> where $[G:H]$ is the index of $H$ in $G$, the number of left cosets.

### 3.2 FormalMath对应陈述

```markdown
**定理（拉格朗日定理）**:

设 $G$ 是有限群，$H \leq G$ 是子群。则：
$$|G| = [G:H] \cdot |H|$$

特别地，$|H|$ 整除 $|G|$。
```

### 3.3 定理陈述对比

| 要素 | Artin | FormalMath | 差异说明 |
|-----|-------|------------|---------|
| 条件 | $H$ 是 $G$ 的子群 | $H \leq G$ | 符号等价 |
| 结论 | $|G| = [G:H] \cdot |H|$ | 一致 | 严格等价 |
| 推论 | $|H|$ 整除 $|G|$ | 一致 | 严格等价 |

### 3.4 证明思路

**Artin教材证明策略**:
1. 证明所有陪集大小相等：$|aH| = |H|$
2. 证明陪集构成 $G$ 的划分
3. 设 $[G:H] = r$，则 $G = a_1H \cup \cdots \cup a_rH$（不交并）
4. 故 $|G| = r \cdot |H| = [G:H] \cdot |H|$

**FormalMath证明框架**:
- 完整证明见 `docs/02-代数结构/02-核心理论/群论/定理证明/拉格朗日定理-完整证明.md`
- 框架已存在，需补充详细步骤

### 3.5 Lean4形式化对应

```lean4
-- 拉格朗日定理（Mathlib中已存在）
import Mathlib

open Subgroup

-- 拉格朗日定理：子群的阶整除群的阶
 theorem lagrange_theorem {G : Type*} [Group G] [Fintype G] 
    (H : Subgroup G) [Fintype H] :
    Fintype.card H ∣ Fintype.card G := by
  -- Mathlib中已实现的证明
  exact Subgroup.card_subgroup_dvd_card H
```

---

## 4. 同态基本定理详解

### 4.1 Artin教材原文

> **Theorem 2.10.3 (First Isomorphism Theorem - Homomorphism Fundamental Theorem)**:
> Let $\varphi: G \to G'$ be a surjective group homomorphism with kernel $N$.
> Then $G/N$ is isomorphic to $G'$.
> The map $\bar{\varphi}: G/N \to G'$ defined by $\bar{\varphi}(aN) = \varphi(a)$ is an isomorphism.

### 4.2 FormalMath对应陈述

```markdown
**定理（同态基本定理 / 第一同构定理）**:

设 $\varphi: G \to G'$ 是群的满同态，$N = \ker \varphi$。则：
$$G/N \cong G'$$

同构映射为 $\bar{\varphi}: G/N \to G'$，$\bar{\varphi}(aN) = \varphi(a)$。
```

### 4.3 定理陈述对比

| 要素 | Artin | FormalMath | 差异说明 |
|-----|-------|------------|---------|
| 条件 | 满同态 $\varphi: G \to G'$ | 一致 | 严格等价 |
| 核 | $N = \ker \varphi$ | 一致 | 严格等价 |
| 结论 | $G/N \cong G'$ | 一致 | 严格等价 |
| 同构映射 | $\bar{\varphi}(aN) = \varphi(a)$ | 一致 | 严格等价 |

### 4.4 证明思路

**Artin教材证明策略**:
1. 验证 $\bar{\varphi}$ 是良定义的（与代表元选取无关）
2. 验证 $\bar{\varphi}$ 是同态
3. 验证 $\bar{\varphi}$ 是双射
   - 满射：由 $\varphi$ 满射得到
   - 单射：若 $\bar{\varphi}(aN) = \bar{\varphi}(bN)$，则 $\varphi(a) = \varphi(b)$，故 $a^{-1}b \in N$，即 $aN = bN$

**FormalMath证明框架**:
- 完整证明见 `docs/02-代数结构/02-核心理论/群论/定理证明/同态基本定理-完整证明.md`
- 框架已存在，需补充详细步骤

### 4.5 Lean4形式化对应

```lean4
-- 同态基本定理（待建设）
import Mathlib

open Subgroup QuotientGroup

-- 同态基本定理：G/ker(φ) ≅ im(φ)
theorem first_isomorphism_theorem {G G' : Type*} [Group G] [Group G']
    (φ : G →* G') :
    G ⧸ (ker φ) ≃* (φ.range) := by
  -- 证明待补充
  sorry
```

---

## 5. 第一同构定理详解

### 5.1 Artin教材原文

同态基本定理（Theorem 2.10.3）也称为第一同构定理。Artin在Ch 2.10中统一陈述了同态基本定理。

### 5.2 FormalMath对应陈述

见第4节同态基本定理。

---

## 6. 对应定理详解

### 6.1 Artin教材原文

> **Theorem 2.10.5 (Correspondence Theorem)**: Let $\varphi: G \to G'$ be a surjective group homomorphism with kernel $N$. There is a bijective correspondence between subgroups of $G'$ and subgroups of $G$ that contain $N$:
> $$\{\text{subgroups } H' \subseteq G'\} \longleftrightarrow \{\text{subgroups } H \subseteq G \mid N \subseteq H\}$$
> This correspondence is defined by $H = \varphi^{-1}(H')$ and $H' = \varphi(H)$.

### 6.2 FormalMath对应陈述

```markdown
**定理（对应定理）**:

设 $\varphi: G \to G'$ 是群的满同态，$N = \ker \varphi$。则在 $G'$ 的子群与 $G$ 中包含 $N$ 的子群之间存在一一对应：

$$H' \mapsto \varphi^{-1}(H'), \quad H \mapsto \varphi(H)$$

此外，$H' \trianglelefteq G'$ 当且仅当 $\varphi^{-1}(H') \trianglelefteq G$。
```

---

## 7. Sylow第一定理详解

### 7.1 Artin教材原文

> **Theorem 6.4.1 (First Sylow Theorem)**: Let $G$ be a finite group of order $n = p^em$, where $p$ is a prime not dividing $m$. Then $G$ contains a subgroup of order $p^e$, a Sylow $p$-subgroup.

### 7.2 FormalMath对应陈述

```markdown
**定理（Sylow第一定理）**:

设 $G$ 是有限群，$|G| = p^e m$，其中 $p$ 是素数且 $p \nmid m$。则 $G$ 包含一个阶为 $p^e$ 的子群（称为Sylow $p$-子群）。
```

---

## 8. 轨道-稳定化子定理详解

### 8.1 Artin教材原文

> **Theorem 6.8.4 (Orbit-Stabilizer Theorem)**: Let $S$ be a $G$-set and $s$ an element of $S$. The map $G \to \mathcal{O}_s$ defined by $g \mapsto gs$ induces a bijection $G/G_s \to \mathcal{O}_s$, where $G_s$ is the stabilizer of $s$.
> Hence $|G| = |G_s| \cdot |\mathcal{O}_s|$.

### 8.2 FormalMath对应陈述

```markdown
**定理（轨道-稳定化子定理）**:

设群 $G$ 作用在集合 $S$ 上，$s \in S$。则：
$$|G| = |G_s| \cdot |\mathcal{O}_s|$$

其中 $G_s = \{g \in G : gs = s\}$ 是稳定化子，$\mathcal{O}_s = \{gs : g \in G\}$ 是轨道。
```

---

## 9. 类方程详解

### 9.1 Artin教材原文

> **Theorem 6.9.1 (Class Equation)**: Let $G$ be a finite group. Then
> $$|G| = |Z(G)| + \sum_{\text{nontrivial orbits}} |\mathcal{O}_s|$$
> where $Z(G)$ is the center of $G$ and the sum is over nontrivial conjugacy classes.

### 9.2 FormalMath对应陈述

```markdown
**定理（类方程）**:

设 $G$ 是有限群。则：
$$|G| = |Z(G)| + \sum_{i} [G : C_G(g_i)]$$

其中 $Z(G)$ 是中心，$g_i$ 是非平凡共轭类的代表元，$C_G(g_i)$ 是中心化子。
等价地：
$$|G| = |Z(G)| + \sum_{\text{非平凡轨道}} |\mathcal{O}_s|$$
```

---

## 10. 有限Abel群结构定理详解

### 10.1 Artin教材原文

> **Theorem 14.7.3 (Structure Theorem for Finite Abelian Groups)**: Every finite abelian group $V$ is a direct sum of cyclic groups of prime power orders:
> $$V \cong C_{p_1^{e_1}} \oplus C_{p_2^{e_2}} \oplus \cdots \oplus C_{p_k^{e_k}}$$
> where $p_i$ are primes (not necessarily distinct).

### 10.2 FormalMath对应陈述

```markdown
**定理（有限Abel群结构定理）**:

每个有限Abel群 $G$ 都可以分解为素数幂阶循环群的直和：
$$G \cong C_{p_1^{e_1}} \times C_{p_2^{e_2}} \times \cdots \times C_{p_k^{e_k}}$$

其中 $p_i$ 是素数（可以重复）。

**不变因子分解**：也可以表示为
$$G \cong C_{d_1} \times C_{d_2} \times \cdots \times C_{d_r}$$
其中 $d_1 | d_2 | \cdots | d_r$。
```

---

## 11. 证明技巧总结

### 11.1 群论证明常用技巧

| 技巧 | 适用场景 | 示例定理 |
|-----|---------|---------|
| **计数论证** | 有限群 | 拉格朗日定理 |
| **构造同构** | 商群结构 | 同态基本定理 |
| **对应关系** | 子群结构 | 对应定理 |
| **轨道分析** | 群作用 | 轨道-稳定化子定理、类方程 |
| **归纳法** | 有限群结构 | Sylow定理 |

### 11.2 证明结构模板

**证明同构的标准步骤**:
1. 定义映射 $\varphi: G \to H$
2. 验证良定义性
3. 验证同态性
4. 验证单射性
5. 验证满射性

**证明子群阶数的标准步骤**:
1. 利用陪集划分
2. 计算陪集数量
3. 利用计数公式

---

## 12. Lean4形式化对应

### 12.1 Mathlib中已有的群论形式化

```lean4
-- 拉格朗日定理
#check Subgroup.card_subgroup_dvd_card

-- 商群结构
#check QuotientGroup

-- 群同态
#check MonoidHom

-- 正规子群
#check Subgroup.Normal

-- 同态核
#check MonoidHom.ker

-- 同态像
#check MonoidHom.range
```

### 12.2 待建设的Lean4形式化

| 定理 | Mathlib状态 | 优先级 |
|-----|-------------|--------|
| 拉格朗日定理 | ✅ 存在 | P0 |
| 同态基本定理 | ⚠️ 部分 | P0 |
| 对应定理 | 🔧 待建设 | P1 |
| Sylow定理 | ✅ 存在 | P1 |
| 轨道-稳定化子定理 | ✅ 存在 | P1 |

---

## 13. 教学建议

### 13.1 学习路径

```
群定义 (L3)
│
├─ 拉格朗日定理 (L4-P0) ← 陪集计数
│
├─ 同态与同构 (L3)
│   └─ 同态基本定理 (L4-P0)
│   └─ 对应定理 (L4-P1)
│
├─ 群作用 (L3)
│   └─ 轨道-稳定化子定理 (L4-P1)
│   └─ 类方程 (L4-P1)
│
└─ Sylow理论 (L4-P1)
    └─ Sylow第一定理
    └─ Sylow第二、三定理

进阶：
└─ 有限Abel群结构定理 (L4-P2)
```

### 13.2 常见误区

❌ **错误**: 认为所有子群都满足 $|H|$ 整除 $|G|$  
✅ **纠正**: 这是拉格朗日定理的推论，只对子群成立

❌ **错误**: 混淆同态基本定理和第一同构定理  
✅ **纠正**: 它们是同一个定理的不同表述

❌ **错误**: 认为 $|G|/|H|$ 总是整数  
✅ **纠正**: 仅当 $H$ 是子群时，拉格朗日定理保证整除

---

**对齐完成**: MIT 18.701 L4定理级对齐 **框架建设完成**  
**统计**: 8个核心定理，7个已有框架，1个待建设  
**下一步**: 补充P0优先级定理的完整证明细节  
**最后更新**: 2026年4月10日
