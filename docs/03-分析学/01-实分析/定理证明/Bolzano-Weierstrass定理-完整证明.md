---
title: Bolzano-Weierstrass 定理
course: MIT 18.100A Real Analysis
difficulty: 核心定理
importance: 极高
prerequisites: [区间套定理, 单调收敛定理, 子列概念]
related: [单调收敛定理, 紧致性, 序列紧致]
tags: [实分析, 子列, 收敛性, 核心定理]
date: 2026-04-10
---

# Bolzano-Weierstrass 定理

## 定理陈述

**定理（Bolzano-Weierstrass）**：设 $\{x_n\}$ 是 $\mathbb{R}$ 中的**有界数列**，则 $\{x_n\}$ 必存在**收敛子列**。

等价表述：若存在 $M > 0$ 使得 $|x_n| \leq M$ 对所有 $n \in \mathbb{N}$ 成立，则存在严格递增的指标序列 $n_1 < n_2 < n_3 < \cdots$ 使得 $\{x_{n_k}\}_{k=1}^\infty$ 收敛。

---

## 证明思路

本证明采用**区间二分法**（Bisection Method），这是分析学中构造性证明的经典范例：

1. **初始区间**：由有界性，所有项落在某闭区间 $[a, b]$ 内

2. **区间套构造**：反复二分区间，选择包含无穷多项的那一半

3. **选取子列**：在每个选定的子区间中选取数列的一项，保证指标递增

4. **应用区间套定理**：区间长度趋于0，子列成为柯西列从而收敛

**替代方法**：单调子列法（利用"每个数列都有单调子列"这一引理）

---

## 详细证明（区间二分法）

### 步骤1：确定初始区间

**给定**：$\{x_n\}$ 有界，即存在 $M > 0$ 使得 $|x_n| \leq M$ 对所有 $n$ 成立

**构造**：令 $I_0 = [-M, M]$，则 $x_n \in I_0$ 对所有 $n$ 成立

**观察**：$I_0$ 包含数列的**全部无穷多项**（整个数列）

---

### 步骤2：区间套的递归构造

**递归定义**：假设已构造闭区间 $I_{k-1} = [a_{k-1}, b_{k-1}]$，其满足：
- $I_{k-1}$ 包含 $\{x_n\}$ 的**无穷多项**
- 区间长度 $|I_{k-1}| = b_{k-1} - a_{k-1} = \frac{2M}{2^{k-1}}$

**二分操作**：将 $I_{k-1}$ 分为两个等长子区间：
$$I_{k-1}^L = \left[a_{k-1}, \frac{a_{k-1}+b_{k-1}}{2}\right], \quad I_{k-1}^R = \left[\frac{a_{k-1}+b_{k-1}}{2}, b_{k-1}\right]$$

**选择原则**：
- 若 $I_{k-1}^L$ 包含无穷多项，则令 $I_k = I_{k-1}^L$
- 否则 $I_{k-1}^R$ 必包含无穷多项，令 $I_k = I_{k-1}^R$

**关键事实**：
- 两个子区间的并包含原区间的所有项
- 若 $I_{k-1}$ 包含无穷多项，则至少一个子区间也包含无穷多项（鸽巢原理）

---

### 步骤3：区间套的性质

**得到区间序列**：$I_0 \supseteq I_1 \supseteq I_2 \supseteq \cdots$

**长度计算**：
$$|I_k| = \frac{|I_0|}{2^k} = \frac{2M}{2^k} = \frac{M}{2^{k-1}} \to 0 \quad (k \to \infty)$$

**区间套定理的条件**：
1. 每个 $I_k$ 是非空闭区间 ✓
2. $I_{k+1} \subseteq I_k$（嵌套性）✓
3. $|I_k| \to 0$（长度趋于零）✓

**应用区间套定理**：存在唯一的 $c \in \mathbb{R}$ 使得 
$$\bigcap_{k=0}^\infty I_k = \{c\}$$

---

### 步骤4：构造收敛子列

**递归选取子列项**：

**基础步**：在 $I_0 = [-M, M]$ 中任取一项，记为 $x_{n_1}$

**归纳步**：假设已选取 $x_{n_1}, x_{n_2}, \ldots, x_{n_k}$，其中：
- $n_1 < n_2 < \cdots < n_k$
- $x_{n_j} \in I_{j-1}$ 对 $j = 1, \ldots, k$

**下一步**：由于 $I_k$ 包含无穷多项，必存在指标 $n_{k+1} > n_k$ 使得 $x_{n_{k+1}} \in I_k$

**构造完成**：得到严格递增的指标序列 $n_1 < n_2 < n_3 < \cdots$ 和子列 $\{x_{n_k}\}$

---

### 步骤5：证明子列收敛于 $c$

**关键观察**：由构造，$x_{n_k} \in I_{k-1}$ 且 $c \in I_{k-1}$（对所有 $k$）

**估计距离**：
$$|x_{n_k} - c| \leq |I_{k-1}| = \frac{2M}{2^{k-1}} = \frac{M}{2^{k-2}}$$

**极限分析**：
$$\lim_{k \to \infty} |x_{n_k} - c| \leq \lim_{k \to \infty} \frac{M}{2^{k-2}} = 0$$

**结论**：$\lim_{k \to \infty} x_{n_k} = c$

**证毕** ∎

---

## 替代证明（单调子列法）

### 引理：每个数列都有单调子列

**定义（峰顶）**：称 $x_m$ 是一个**峰顶**（peak），如果对所有 $n > m$ 有 $x_n \leq x_m$。

**情形分析**：

**情形1**：数列有无穷多个峰顶
- 设 $x_{n_1}, x_{n_2}, x_{n_3}, \ldots$ 是峰顶，其中 $n_1 < n_2 < n_3 < \cdots$
- 由峰顶定义：$x_{n_1} \geq x_{n_2} \geq x_{n_3} \geq \cdots$
- 得到**单调递减子列**

**情形2**：数列只有有限个峰顶
- 设 $N$ 是最后一个峰顶的指标（若无峰顶则 $N = 0$）
- 对任意 $n > N$，$x_n$ 不是峰顶，故存在 $m > n$ 使 $x_m > x_n$
- 递归构造：取 $n_1 = N+1$，选 $n_2 > n_1$ 使 $x_{n_2} > x_{n_1}$，依此类推
- 得到**单调递增子列**

### 完成 Bolzano-Weierstrass 定理的证明

1. 由引理，$\{x_n\}$ 有单调子列 $\{x_{n_k}\}$
2. 由有界性，$\{x_{n_k}\}$ 也有界
3. 由**单调收敛定理**，$\{x_{n_k}\}$ 收敛

**证毕** ∎

---

## 证明对比

| 特征 | 区间二分法 | 单调子列法 |
|-----|-----------|-----------|
| **核心工具** | 区间套定理 | 单调收敛定理 |
| **构造性** | 强（给出子列构造算法） | 中等（需分情形讨论） |
| **极限值** | 区间套的唯一点 | 子列的上/下确界 |
| **复杂度** | 稍复杂 | 较简洁 |
| **推广性** | 易推广到 $\mathbb{R}^n$ | 需额外处理 |

---

## 关键洞察（Key Insights）

### 1. 序列紧致的本质

Bolzano-Weierstrass 定理刻画了 $\mathbb{R}$ 的**序列紧致性**（sequential compactness）：
- 有界闭集 = 序列紧致（在度量空间中）
- 这是有限维空间的特性，在无穷维空间中失效

### 2. 紧致性的等价刻画

对于 $\mathbb{R}$ 的子集，以下条件等价：
- 有界且闭（拓扑紧致）
- 序列紧致（Bolzano-Weierstrass 性质）
- 有限覆盖紧致（Heine-Borel 性质）

### 3. 与完备性的关系

Bolzano-Weierstrass 定理依赖于实数的完备性：
- 区间套定理 ← 完备性
- 单调收敛定理 ← 完备性
- 柯西准则 ← 完备性

### 4. 构造性 vs 存在性

区间二分法给出了**算法**：
- 实际可计算子列的收敛速度：$|x_{n_k} - c| = O(2^{-k})$
- 指数级收敛！

---

## 与 Lean4 形式化的对应

### Mathlib 中的表述

```lean4
import Mathlib

open Filter Topology

-- Bolzano-Weierstrass 定理：有界序列有收敛子列
theorem bolzano_weierstrass {x : ℕ → ℝ} (h : Bornology.IsBounded (Set.range x)) :
    ∃ c, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 c) := by
  -- 使用紧致性论证
  have : IsCompact (closure (Set.range x)) := by
    apply isCompact_closure_of_bddAbove_bddBelow
    · -- 证明有上界
      simpa using h.subset (Set.subset_range _)
    · -- 证明有下界
      simpa using h.subset (Set.subset_range _)
  -- 紧致集 = 序列紧致
  rw [isCompact_iff_isSeqCompact] at this
  -- 序列紧致蕴含存在收敛子列
  exact this x (fun n => subset_closure (Set.mem_range_self n))
```

### 关键对应点

| 数学概念 | Lean4 对应 |
|---------|-----------|
| 有界数列 | `Bornology.IsBounded (Set.range x)` |
| 收敛子列 | `∃ φ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 c)` |
| 序列紧致 | `IsSeqCompact` |
| 紧致 | `IsCompact` |
| 闭包 | `closure` |

### 形式化技巧

```lean4
-- 区间套定理的形式化
theorem nested_intervals (I : ℕ → Set ℝ) 
    (hI : ∀ n, IsClosed (I n)) (hnested : ∀ n, I (n+1) ⊆ I n)
    (hlen : Tendsto (fun n => diam (I n)) atTop (𝓝 0)) :
    ∃! x, ∀ n, x ∈ I n := ...
```

---

## 常见误区（Common Pitfalls）

### ❌ 误区1：混淆子列与原数列的收敛性

**错误**："Bolzano-Weierstrass 说所有有界数列都收敛"

**纠正**：只保证**存在**收敛**子列**，原数列可能发散。

**反例**：$x_n = (-1)^n$ 有界但不收敛，但有收敛子列 $x_{2k} \to 1$

---

### ❌ 误区2：区间二分法中指标构造不严谨

**错误证明**：
> "在每个区间选一点，得到子列..."

**漏洞**：未确保指标严格递增 $n_1 < n_2 < n_3 < \cdots$。必须从第 $k$ 个区间选指标大于 $n_{k-1}$ 的项。

---

### ❌ 误区3：忽视唯一性

**问题**：区间套定理说交是**单点集**，但 Bolzano-Weierstrass 不排除不同构造得到不同子列收敛到不同极限。

**事实**：不同子列可能收敛到不同极限。例：$x_n = (-1)^n$ 有子列收敛到 $1$ 和子列收敛到 $-1$。

---

### ❌ 误区4：将有界性替换为有上界/有下界

**错误**：认为"有上界的数列有收敛子列"

**反例**：$x_n = -n$ 有上界（上界为 $-1$），但所有子列发散到 $-\infty$

---

### ❌ 误区5：在有理数域中应用

**错误**：认为定理在 $\mathbb{Q}$ 中成立

**反例**：取 $\{x_n\}$ 为 $\sqrt{2}$ 的有理逼近序列（如截断十进制展开）。数列在 $\mathbb{Q}$ 中有界，但无在 $\mathbb{Q}$ 中收敛的子列。

---

## 应用示例

### 例1：证明闭区间上连续函数有界

**证明框架**：
1. 反设 $f$ 在 $[a,b]$ 上无界
2. 则对每个 $n$，存在 $x_n \in [a,b]$ 使 $|f(x_n)| > n$
3. 由 Bolzano-Weierstrass，$\{x_n\}$ 有子列 $x_{n_k} \to c \in [a,b]$
4. 由连续性，$f(x_{n_k}) \to f(c)$，但 $|f(x_{n_k})| > n_k \to \infty$，矛盾！

### 例2：构造不收敛但有收敛子列的数列

**例**：$x_n = \sin(n)$
- 有界性：$|x_n| \leq 1$
- 不收敛（可通过密度论证证明）
- Bolzano-Weierstrass 保证存在收敛子列

---

## 参考文献

1. **Rudin, W.** *Principles of Mathematical Analysis*, Theorem 2.42
2. **Abbott, S.** *Understanding Analysis*, Theorem 2.5.5
3. **Tao, T.** *Analysis I*, Theorem 6.1.12
4. **Lean4 Mathlib**: `Mathlib.Topology.MetricSpace.Basic`, `Mathlib.Topology.Compactness`

---

*文档版本: 1.0 | 创建日期: 2026-04-10 | 对应课程: MIT 18.100A*
