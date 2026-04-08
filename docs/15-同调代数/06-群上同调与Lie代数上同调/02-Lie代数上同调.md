---
msc_primary: 17B56
msc_secondary: ['18G99', '17B55']
keywords: ['Lie代数上同调', 'Chevalley-Eilenberg', '外代数', '中心扩张', 'Whitehead引理']
version: 1.0
---

# Lie代数上同调

**Lie代数的同调理论 — 从Chevalley-Eilenberg到表示论**

---

## 1. 概念深度解析

### 1.1 代数直观

**Lie代数上同调** $H^n(\mathfrak{g}, M)$ 是群上同调的Lie代数版本：

- Chevalley-Eilenberg复形
- 与de Rham上同调的关系
- Whitehead引理

### 1.2 范畴论语境

$$H^n(\mathfrak{g}, M) = \text{Ext}^n_{U(\mathfrak{g})}(k, M)$$
其中 $U(\mathfrak{g})$ 是泛包络代数。

### 1.3 形式定义

#### 定义 1.1 (Chevalley-Eilenberg复形)

$$C^n(\mathfrak{g}, M) = \text{Hom}_k(\Lambda^n \mathfrak{g}, M)$$
$$(\delta \omega)(x_0, ..., x_n) = \sum (-1)^i x_i \cdot \omega(...) + \sum_{i<j} (-1)^{i+j} \omega([x_i, x_j], ...)$$

---

## 2. 属性与关系

### 2.1 低维解释

**定理 2.1**

- $H^0(\mathfrak{g}, M) = M^{\mathfrak{g}}$
- $H^1(\mathfrak{g}, M) = \text{导子}/\text{内导子}$
- $H^2(\mathfrak{g}, M) = \{\text{Lie代数扩张}\}$

### 2.2 Whitehead引理

**定理 2.2 (Whitehead)**
设 $\mathfrak{g}$ 是半单Lie代数，M是有限维表示。
$$H^1(\mathfrak{g}, M) = H^2(\mathfrak{g}, M) = 0$$

---

## 3. 示例与习题

### 3.1 习题

#### 习题 1

计算 $H^*(\mathfrak{sl}_2, \mathbb{C})$。

#### 习题 2

证明Whitehead引理。

#### 习题 3

证明 $H^n(\mathfrak{g}, k) \cong H^n_{dR}(G)$ 对紧Lie群G。

---

## 4. 形式化实现 (Lean 4)

```lean4
import Mathlib.Algebra.Lie.Cohomology

variable {k : Type*} [CommRing k] {g : Type*} [LieRing g] [LieAlgebra k g]
  {M : Type*} [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M]

-- ============================================
-- Lie代数上同调
-- ============================================

def LieAlgebraCohomology (n : ℕ) : Type _ :=
  LieAlgebra. Cohomology k g M n
```

---

**维护者**: FormalMath项目组
**创建日期**: 2026年4月8日
**难度等级**: ⭐⭐⭐⭐
