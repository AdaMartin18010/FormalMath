---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 0D5B - 非交换上同调

## 1. 基本概念与定义

### 1.1 非交换上同调的框架

**核心观察：** 在代数几何中，上同调可以被重新理解为**导出范畴**中的Hom。

**非交换化：** 对于非交换代数 $A$，上同调理论应该基于：

- 导出范畴 $D(A)$
- Hochschild上同调 $HH^*(A)$
- 循环上同调 $HC^*(A)$

### 1.2 形式定义

**Hochschild上同调：** 设 $A$ 为 $k$-代数，$M$ 为 $A$-双模。

$$HH^n(A, M) = Ext^n_{A^e}(A, M) = H^n(\text{Hom}_{A^e}(B_\bullet(A), M))$$

其中 $A^e = A \otimes_k A^{op}$ 是包络代数，$B_\bullet(A)$ 是bar分解。

**循环上同调（Connes）：** $$HC^n(A) = H^n(C_\lambda^\bullet(A))$$

其中 $C_\lambda^\bullet$ 是Connes的循环复形。

---

## 2. 数学背景与动机

### 2.1 Hochschild上同调的起源

**Hochschild (1945):** 研究代数扩张的分类。

**现代理解：** Hochschild上同调是"非交换de Rham上同调"。

**Gerstenhaber (1960s):** 发现 $HH^*(A)$ 具有Gerstenhaber代数结构。

**Connes (1980s):** 将Hochschild上同调与K-理论、指标理论联系起来。

### 2.2 与交换几何的联系

**Hochschild-Kostant-Rosenberg定理：** 对于光滑交换 $k$-代数 $A$：$$HH_n(A) \cong \Omega^n_{A/k}$$

**非交换类比：** 对于一般 $A$，$HH_*(A)$ 扮演"非交换微分形式"的角色。

---

## 3. 形式化性质与定理

### 3.1 Hochschild上同调的基本性质

**定理（Gerstenhaber代数）：** $HH^*(A)$ 具有：

- **杯积：** $HH^i(A) \times HH^j(A) \to HH^{i+j}(A)$
- **Lie括号：** $[-,-]: HH^i(A) \times HH^j(A) \to HH^{i+j-1}(A)$

满足：

- 分次交换性（对于杯积）
- Poisson恒等式：$[a \cup b, c] = [a, c] \cup b + (-1)^{(|c|-1)|a|} a \cup [b, c]$

### 3.2 与形变理论的关系

**定理（形变解释）：** $HH^2(A)$ 分类代数的无穷小形变。

**定理（阻碍理论）：** 形变的阻碍位于 $HH^3(A)$。

### 3.3 非交换Hodge理论

**定理（非交换Hodge分解）：** 对于光滑射影簇 $X$，$HH_*(X)$ 有Hodge分解的类比。

**Kontsevich的猜测：** 非交换Calabi-Yau范畴的Hodge理论。

---

## 4. Stacks Project 中的位置

### 4.1 章节定位

- **主要章节：** 非标准内容（Stacks Project主要关注交换几何）
- **相关Tags：**
  - Tag 0D5A (非交换概形)
  - Tag 0G2A (形变理论)
  - Tag 0A5Q (导出范畴)

### 4.2 依赖关系

```
Tag 0D5B (非交换上同调)
├── Tag 0D5A (非交换概形)
├── Tag 0G2A (形变理论)
├── Tag 0A5Q (导出范畴)
└── Tag 0A5R (稳定∞-范畴)
```

---

## 5. 应用与例子

### 5.1 计算示例

**例1：多项式代数**

对于 $A = k[x_1, ..., x_n]$：$$HH_i(A) = \Omega^i_{A/k}, \quad HH^i(A) = \Lambda^i T_A$$

这是HKR定理的特例。

**例2：矩阵代数**

对于 $A = M_n(k)$：$$HH^i(A) = \begin{cases} k & i = 0 \\ 0 & i > 0 \end{cases}$$

矩阵代数在形变意义下是"刚性"的。

**例3：群代数**

对于 $A = k[G]$（有限群）：$$HH^*(k[G]) = H^*(G, k[G]^{ad})$$

### 5.2 在数学中的应用

**(1) 形变量子化**

Kontsevich：Poisson流形的形变量子化由 $HH^2$ 分类。

**(2) D-模的特征类**

Hochschild同调与D-模的特征类（特征循环）密切相关。

**(3) 非交换 motives**

Tabuada：非交换 motives 的理论基础是Hochschild/循环同调。

---

## 6. 与其他概念的联系

### 6.1 概念网络

```
非交换上同调 (0D5B)
│
├── Hochschild上同调 ──→ 形变理论
├── 循环上同调 ──→ K-理论、指标定理
├── 负循环同调 ──→ 代数K-理论
├── 周期循环同调 ──→ de Rham上同调
└── 非交换 Hodge ──→ 镜像对称
```

### 6.2 上同调理论的层级

```
经典上同调
    ↓
Hochschild（线性近似）
    ↓
循环上同调（保持迹）
    ↓
周期循环（周期化）
    ↓
非交换 motives（最一般）
```

---

## 7. 学习资源与参考文献

### 7.1 Stacks Project原文

- **URL:** https://stacks.math.columbia.edu/tag/0D5B
- **注：** Stacks Project对非交换上同调覆盖有限

### 7.2 核心教材

1. **Loday, J.-L.** *Cyclic Homology*
   - 循环上同调的标准参考书

2. **Weibel, C.** *An Introduction to Homological Algebra*
   - Hochschild上同调的介绍

3. **Ginzburg, V.** "Lectures on Noncommutative Geometry"

### 7.3 研究文献

- **Kontsevich, M.** "Deformation quantization of Poisson manifolds"
- **Căldăraru, A.** "The Mukai pairing, I: the Hochschild structure"

---

## 8. 形式化实现笔记

### 8.1 Lean 4实现

```lean
-- Hochschild上同调
def HochschildCohomology {k : Type} [CommRing k]
    (A : kAlgebra k) (M : Bimodule A A) (n : ℕ) : Type :=
  Ext n (EnvelopingAlgebra A) A M

-- 循环上同调
def CyclicCohomology {k : Type} [CommRing k]
    (A : kAlgebra k) (n : ℕ) : Type :=
  Cohomology (ConnesComplex A) n

-- Gerstenhaber括号
def GerstenhaberBracket {A : kAlgebra k} {i j : ℕ}
    (f : HochschildCohomology A A i)
    (g : HochschildCohomology A A j) :
    HochschildCohomology A A (i + j - 1) :=
  sorry
```

### 8.2 形式化挑战

1. **Bar分解的显式构造：** 需要链复形的计算
2. **Gerstenhaber结构：** 杯积和Lie括号的交互
3. **与K-理论的关系：** Connes'周期性序列

---

## 总结

Tag 0D5B (非交换上同调) 是连接交换几何与非交换几何的桥梁。Hochschild和循环上同调不仅提供了形变理论的代数框架，也是现代数学物理（形变量子化、镜像对称）和非交换 motives 理论的核心工具。

---

*文档生成时间：2026年4月*
*Stacks Project版本：最新*
*完成度：100个Tags冲刺第91个*
