---
msc_primary: 55

  - 55T10
msc_secondary: ['55R20', '18G40']
keywords: ['Leray-Serre', '纤维丛', '纤维化', '纤维同调', '基空间']
version: 1.0
---

# Leray-Serre谱序列

**纤维丛的同调计算 — 从整体到局部的分解**

---

## 1. 概念深度解析

### 1.1 代数直观

**Leray-Serre谱序列**计算纤维丛的总空间同调：

- 输入：纤维丛 $F \to E \xrightarrow{\pi} B$
- 输出：$H^*(E)$ 的近似

**核心思想**：
$$E_2^{p,q} = H^p(B, \mathcal{H}^q(F)) \Rightarrow H^{p+q}(E)$$

### 1.2 几何背景

纤维丛 $F \to E \to B$ 将空间分解为：

- 基空间 B：控制"水平"结构
- 纤维 F：控制"垂直"结构
- 总空间 E：整体结构

### 1.3 形式定义

#### 定理 1.1 (Leray-Serre)

设 $F \to E \xrightarrow{\pi} B$ 是纤维丛，B单连通。

存在第一象限上同调谱序列：
$$E_2^{p,q} = H^p(B, H^q(F)) \Rightarrow H^{p+q}(E)$$

微分：$d_r: E_r^{p,q} \to E_r^{p+r, q-r+1}$

---

## 2. 属性与关系

### 2.1 基本性质

**定理 2.1 (边缘同态)**
有正合列：
$$0 \to H^1(B) \to H^1(E) \to H^1(F) \xrightarrow{d_2} H^2(B) \to H^2(E)$$

**定理 2.2 (乘积结构)**
谱序列有多项式结构，微分满足莱布尼茨法则。

### 2.2 特殊情况

**情形1：平凡丛** $E = B \times F$
$$E_2 = E_\infty, \quad H^*(E) = H^*(B) \otimes H^*(F)$$

**情形2：道路纤维化** $\Omega X \to PX \to X$
$$E^2_{p,q} = H_p(X, H_q(\Omega X)) \Rightarrow H_{p+q}(PX) = \begin{cases} \mathbb{Z} & p+q=0 \\ 0 & \text{otherwise} \end{cases}$$

### 2.3 Wang序列

**定理 2.3 (Wang序列)**
对球丛 $S^n \to E \to B$：
$$\cdots \to H^k(E) \to H^{k-n}(B) \xrightarrow{\cup e} H^{k+1}(B) \to H^{k+1}(E) \to \cdots$$
其中 $e$ 是Euler类。

---

## 3. 示例与习题

### 3.1 具体计算示例

#### 示例 3.1 (S¹-丛)

$S^1 \to S^3 \to S^2$（Hopf纤维化）

$E_2$页：

- $E_2^{0,0} = E_2^{0,1} = E_2^{2,0} = E_2^{2,1} = \mathbb{Z}$
- 其余为零

微分：$d_2: E_2^{0,1} \to E_2^{2,0}$ 是同构。

结果：$H^*(S^3)$ 正确计算。

#### 示例 3.2 ($\mathbb{C}P^n$ 的循环空间)

使用道路纤维化计算 $H^*(\Omega \mathbb{C}P^n)$。

### 3.2 习题

#### 习题 1

用Leray-Serre谱序列计算 $H^*(\mathbb{C}P^2)$。

#### 习题 2

对Hopf纤维化 $S^1 \to S^{2n+1} \to \mathbb{C}P^n$，计算谱序列。

#### 习题 3

证明：若纤维和基空间是有限CW复形，则总空间也是。

#### 习题 4

用Wang序列计算球丛的上同调。

#### 习题 5

设 $E$ 是 $B$ 上的向量丛。用Thom同构和Leray-Serre比较。

---

## 4. 形式化实现 (Lean 4)

```lean4
import Mathlib.AlgebraicTopology.FiberBundle
import Mathlib.Algebra.Homology.SpectralSequence

-- ============================================
-- Leray-Serre谱序列
-- ============================================

/-- Leray-Serre谱序列 -/
def LeraySerreSpectralSequence {B F E : TopCat} (p : E ⟶ B) [IsFiberBundle F p] :
    SpectralSequence (ModuleCat ℤ) where
  E 2 (p, q) := ModuleCat.of ℤ (H^p B (H^q F))
  d r := sorry
  -- ...

/-- Leray-Serre收敛定理 -/
theorem leray_serre_convergence {B F E : TopCat} (p : E ⟶ B) [IsFiberBundle F p]
    [SimplyConnectedSpace B] :
    (LeraySerreSpectralSequence p).Convergence (fun n => ModuleCat.of ℤ (H^n E)) := by
  sorry

-- ============================================
-- Wang序列
-- ============================================

theorem wang_sequence {B E : TopCat} (p : E ⟶ B) {n : ℕ}
    (h : ∀ b, p ⁻¹' {b} ≅ TopCat.of (Sphere n)) (k : ℤ) :
    ∃ (e : H^0 B (H^n (Sphere n)) → H^(n+1) B),
    Exact (H^k E) (H^(k-n) B) ∧
    Exact (H^(k-n) B) (H^(k+1) B) := by
  sorry
```

---

## 5. 应用与拓展

### 5.1 在代数拓扑中的应用

**球面的同伦群计算**：道路纤维化方法。

**示性类**：Euler类、Stiefel-Whitney类的解释。

### 5.2 在代数几何中的应用

**Leray谱序列**：对态射 $f: X \to Y$，
$$E_2^{p,q} = H^p(Y, R^q f_* \mathcal{F}) \Rightarrow H^{p+q}(X, \mathcal{F})$$

---

## 6. 思维表征

```mermaid
graph TD
    A[纤维丛] --> B[E2=Hp(B, Hq(F))]
    B --> C[微分]
    C --> D[E∞]
    D --> E[H*(E)]

    F[Hopf纤维化] --> G[S1 → S3 → S2]
    G --> H[谱序列计算]
```

---

**维护者**: FormalMath项目组
**创建日期**: 2026年4月8日
**难度等级**: ⭐⭐⭐⭐⭐
