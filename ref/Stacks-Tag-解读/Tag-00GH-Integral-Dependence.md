---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 00GH - 整依赖（Integral Dependence）

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 00GH |
| **章节** | Chapter 10: Commutative Algebra, Section 10.36: Finite and integral ring extensions |
| **类型** | 定义 (Definition) |
| **重要性** | ★★★★★ (核心基础) |
| **位置** | Algebra, Definition 10.36.1 |

## 2. 定理/定义原文

### 英文原文

**Definition 10.36.1.** Let $\varphi : R \to S$ be a ring map.

1. An element $s \in S$ is **integral over $R$** if there exists a monic polynomial $P(x) \in R[x]$ such that $P^\varphi(s) = 0$, where $P^\varphi(x) \in S[x]$ is the image of $P$ under $\varphi : R[x] \to S[x]$.

2. The ring map $\varphi$ is **integral** if every $s \in S$ is integral over $R$.

### 中文翻译

**定义 10.36.1.** 设 $\varphi : R \to S$ 是一个环同态。

1. 元素 $s \in S$ 称为**在 $R$ 上整的**（integral over $R$），如果存在一个首一多项式 $P(x) \in R[x]$ 使得 $P^\varphi(s) = 0$，其中 $P^\varphi(x) \in S[x]$ 是 $P$ 在同态 $\varphi : R[x] \to S[x]$ 下的像。

2. 环同态 $\varphi$ 称为**整的**（integral），如果每个 $s \in S$ 都在 $R$ 上整。

## 3. 概念依赖图

```
                    整依赖 (Integral Dependence)
                           |
        +------------------+------------------+
        |                  |                  |
    环同态            首一多项式         多项式环
   (Ring Map)       (Monic Poly)      (Poly Ring)
        |                  |                  |
        +------------------+------------------+
                           |
                    整扩张 (Integral Extension)
                           |
            +--------------+--------------+
            |              |              |
        有限扩张        诺特正规化      整闭包
      (Finite Ext)   (Noether Norm)  (Integral Closure)
```

**前置知识：**
- 环与环同态的基本理论
- 多项式环的构造
- 理想的运算

**依赖此概念：**
- 整扩张（Integral Extensions）
- 整闭包（Integral Closure）
- 诺特正规化定理（Noether Normalization）
- 维数理论（Dimension Theory）

## 4. 证明概要或详细内容

### 4.1 关键引理

**Lemma 10.36.2** (00GH所在章节的关键引理)

设 $\varphi : R \to S$ 是环同态，$y \in S$。如果存在有限 $R$-子模 $M \subset S$ 使得 $1 \in M$ 且 $yM \subset M$，则 $y$ 在 $R$ 上整。

**证明思路：**
1. 考虑映射 $\varphi : M \to M$, $x \mapsto y \cdot x$
2. 由 Cayley-Hamilton 引理（Lemma 10.16.2），存在首一多项式 $P \in R[T]$ 使得 $P(\varphi) = 0$
3. 在环 $S$ 中，$P(y) = P(y) \cdot 1 = P(\varphi)(1) = 0$

### 4.2 判别准则

**有限性判别（Lemma 10.36.4）**

设 $s_1, \ldots, s_n \in S$ 是有限个元素。则 $s_i$ 在 $R$ 上整对所有 $i = 1, \ldots, n$ 当且仅当存在 $R$-子代数 $S' \subset S$ 使得 $R \to S'$ 有限且包含所有 $s_i$。

**等价条件（Lemma 10.36.5）**

对于环同态 $R \to S$，以下条件等价：
1. $R \to S$ 是有限扩张
2. $R \to S$ 是整的且有限型的
3. 存在 $x_1, \ldots, x_n \in S$ 生成 $S$ 作为 $R$-代数，且每个 $x_i$ 在 $R$ 上整

## 5. 与FormalMath的对应关系

| FormalMath概念 | Stacks Project对应 | 说明 |
|----------------|-------------------|------|
| `Ring` | 环 $R$ | 基础交换环 |
| `RingHom` | $\varphi : R \to S$ | 环同态 |
| `IsIntegral` | integral element | 整元素判定 |
| `IntegralClosure` | $S'$ (Lemma 10.36.7) | 整闭包构造 |

**相关Lean4形式化库：**
- `Mathlib/RingTheory/IntegralClosure.lean`
- `Mathlib/RingTheory/Algebraic.lean`

## 6. 应用与重要性

### 6.1 核心应用

1. **代数几何中的有限态射**
   - 有限态射的纤维是零维的
   - 有限态射是proper的

2. **数论中的整数环**
   - $\mathbb{Z}$ 是 $\mathbb{Q}$ 的整闭包
   - 代数整数环的研究基础

3. **维数理论**
   - Cohen-Seidenberg定理（上升定理）
   - 下降定理（Going Down）

### 6.2 重要性说明

整依赖是交换代数最核心的概念之一，它是连接：
- **代数**与**几何**的桥梁（通过Spec函子）
- **局部**与**整体**的纽带（通过局部化）
- **离散**与**连续**的过渡（通过整闭包）

## 7. 与其他资源的关联

| 资源 | 相关内容 | 链接 |
|------|---------|------|
| Hartshorne | Chapter II, Exercise 3.4-3.7 | 有限态射与整扩张 |
| Atiyah-Macdonald | Chapter 5 | 整依赖与赋值 |
| Matsumura | Chapter 9 | 诺特正规化 |
| Wikipedia | Integral element | 基础概念回顾 |

**交叉引用：**
- Tag 00GI: 整依赖的传递性
- Tag 00H2: 相对于理想的整依赖
- Tag 00J5: Artinian环

## 8. Lean4形式化展望

### 8.1 当前形式化状态

在Lean4的mathlib4中，整依赖已有较为完整的形式化：

```lean
-- 整元素的定义
structure IsIntegral (x : S) : Prop where
  monic : ∃ p : R[X], p.Monic ∧ aeval x p = 0

-- 整扩张的定义
class Algebra.IsIntegral (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] : Prop where
  integral : ∀ x : A, IsIntegral R x
```

### 8.2 形式化挑战

1. **计算复杂性**
   - 寻找整依赖方程的计算
   - 整闭包的构造性算法

2. **高阶性质**
   - 整闭包的泛性质
   - 与平坦性的关系

3. **几何对应**
   - 与有限态射的对应
   - 纤维维数的形式化

### 8.3 建议形式化路线

```
阶段1: 基础定义
  └── IsIntegral元素判定
  └── IntegralClosure构造

阶段2: 基本性质
  └── 传递性 (00GI)
  └── 局部化兼容性

阶段3: 应用定理
  └── 上升/下降定理
  └── 诺特正规化
```

---

**文档版本：** Round 36  
**创建日期：** 2026-04-09  
**最后更新：** 2026-04-09
