---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 04E3 - 上同调环结构

## 1. 基本概念与定义

### 1.1 定义

**上同调环（Cohomology Ring）** 是将空间 $X$ 的各阶上同调群通过Cup积组织成的分次环结构。

设 $R$ 为交换环，$X$ 为拓扑空间（或概形），**上同调环**定义为：

$$H^*(X; R) = \bigoplus_{i=0}^{\infty} H^i(X; R)$$

其乘法由Cup积给出：$\cup: H^i(X) \times H^j(X) \to H^{i+j}(X)$

### 1.2 代数结构

$(H^*(X; R), +, \cup)$ 构成一个**分次交换 $R$-代数**：

- **分次性：** $H^*(X) = \bigoplus_i H^i(X)$
- **交换性：** $a \cup b = (-1)^{|a||b|} b \cup a$
- **结合性：** $(a \cup b) \cup c = a \cup (b \cup c)$
- **单位元：** $1 \in H^0(X)$

---

## 2. 数学背景与动机

### 2.1 历史发展

**Hopf (1930s):** 发现映射 $S^3 \to S^2$ 的不变量可以用上同调环理解。

**Whitney & Steenrod (1940s):** 系统发展了上同调运算理论。

**动机：** 同调群是线性不变量（模），无法区分许多空间。上同调环作为代数不变量，能捕捉更精细的拓扑信息。

### 2.2 为什么需要环结构？

**示例：** $S^2 \vee S^4$ 与 $\mathbb{CP}^2$ 有相同的上同调群：

| 空间 | $H^0$ | $H^2$ | $H^4$ | 上同调环 |
|------|-------|-------|-------|----------|
| $S^2 \vee S^4$ | $\mathbb{Z}$ | $\mathbb{Z}$ | $\mathbb{Z}$ | $a^2 = 0$ |
| $\mathbb{CP}^2$ | $\mathbb{Z}$ | $\mathbb{Z}$ | $\mathbb{Z}$ | $h^2 \neq 0$ |

**结论：** 上同调环可以区分上同调群无法区分的空间！

---

## 3. 形式化性质与定理

### 3.1 基本定理

**定理（上同调环的泛性质）：** 设 $A^* = \bigoplus_i A^i$ 为分次 $R$-代数，则：$$\text{Hom}_{R\text{-alg}}(H^*(X; R), A^*) \cong \{f: X \to K(A^*, *)\}$$

其中 $K(A^*, *)$ 为Eilenberg-MacLane空间。

### 3.2 Künneth公式

**定理：** 对于空间 $X$ 和 $Y$，有分次环同构：$$H^*(X \times Y; R) \cong H^*(X; R) \otimes_R H^*(Y; R)$$

（当 $R$ 为域或某些有限性条件满足时）

### 3.3 庞加莱对偶性

**定理（Poincaré Duality）：** 设 $M$ 为紧致定向 $n$-流形，则：$$\cap [M]: H^i(M) \xrightarrow{\cong} H_{n-i}(M)$$

且Cup积与相交配对相容：$$\langle a \cup b, [M] \rangle = \langle a, b \cap [M] \rangle$$

---

## 4. Stacks Project 中的位置

### 4.1 章节定位

- **主要章节：** Cohomology on Sites
- **前置知识：** Cup积 (Tag 04E2)
- **后续发展：** 相交理论、示性类

### 4.2 相关Tags

```
Tag 04E3 (上同调环)
├── Tag 04E2 (Cup积)
├── Tag 04E4 (相交理论)
├── Tag 0A5Q (导出范畴)
└── Tag 0C5Z (叠的上同调)
```

---

## 5. 应用与例子

### 5.1 经典计算

**例1：球面上同调环**

$$H^*(S^n; R) = R[x]/(x^2), \quad |x| = n$$

生成元 $x$ 满足 $x \cup x = 0$（因为 $H^{2n}(S^n) = 0$）

**例2：环面上同调环**

对于 $T^n = (S^1)^n$：$$H^*(T^n; R) = \Lambda_R(x_1, ..., x_n)$$

为外代数，$|x_i| = 1$，$x_i \cup x_j = -x_j \cup x_i$

**例3：复射影空间**

$$H^*(\mathbb{CP}^n; \mathbb{Z}) = \mathbb{Z}[h]/(h^{n+1}), \quad |h| = 2$$

这是截断的多项式代数。

### 5.2 在代数几何中的应用

**(1) 概形的上同调环**

对于光滑射影概形 $X$：$H^*(X_{\text{ét}}, \mathbb{Q}_\ell)$ 为分次交换 $\mathbb{Q}_\ell$-代数。

**(2) 相交理论的代数化**

Chow环 $A^*(X)$ 是上同调环的代数类比：$$A^*(X) = \bigoplus_i A^i(X)$$

其中 $A^i(X)$ 为余维数 $i$ 的Chow群。

---

## 6. 与其他概念的联系

### 6.1 概念关系图

```
上同调环 (04E3)
│
├── 相交理论 (04E4) ──→ Chow环
├── 示性类理论 ──→ 陈类、Pontryagin类
├── Hodge理论 ──→ Hodge分解
├── 量子上同调 ──→ Gromov-Witten理论
└── 镜面对称 ──→ A-model vs B-model
```

### 6.2 推广与变形

| 结构 | 描述 | 应用 |
|------|------|------|
| 量子上同调 | $a \star b = \sum_{\beta} (a \star b)_\beta q^\beta$ | 枚举几何 |
| 等变上同调 | $H^*_G(X) = H^*(EG \times_G X)$ | 辛几何 |
| 爆破上同调 | $H^*(\tilde{X})$ 的构造 | 双有理几何 |

---

## 7. 学习资源与参考文献

### 7.1 Stacks Project原文

- **URL:** https://stacks.math.columbia.edu/tag/04E3
- **相关章节：** Cohomology on Sites

### 7.2 经典教材

1. **Hatcher, A.** *Algebraic Topology*, Chapter 3
   - 上同调环的计算方法

2. **Fulton, W.** *Intersection Theory*
   - Chow环与上同调环的关系

3. **Griffiths & Harris** *Principles of Algebraic Geometry*
   - Kähler流形的上同调环

### 7.3 研究文献

- **Deligne, P.** "Théorie de Hodge I, II, III"
- **Beilinson, Bernstein, Deligne** "Faisceaux Pervers"
- **Givental, A.** "Homological Geometry"

---

## 8. 形式化实现笔记

### 8.1 Lean 4实现思路

```lean
-- 上同调环作为分次代数
structure CohomologyRing (X : Top) (R : Type) [CommRing R] where
  grading : ℕ → Type
  add : ∀ i, AddCommGroup (grading i)
  cup : ∀ i j, grading i → grading j → grading (i + j)
  graded_comm : ∀ i j (a : grading i) (b : grading j),
    cup i j a b = (-1)^(i*j) • cup j i b a
```

### 8.2 形式化挑战

1. **分次符号的管理：** 需要精确的符号追踪系统
2. **Künneth公式：** 需要有限性条件的处理
3. **庞加莱对偶：** 需要定向性和基本类的形式化

### 8.3 相关库

- **mathlib4:** `Algebra.Category.ModuleCat`
- **Lean-Stacks:** 代数几何上同调的形式化项目

---

## 总结

Tag 04E3 (上同调环结构) 揭示了上同调理论的丰富代数结构，将拓扑/几何问题转化为代数问题。这一结构是相交理论、示性类理论和现代物理（镜像对称、弦理论）的基础。

---

*文档生成时间：2026年4月*
*Stacks Project版本：最新*
*完成度：100个Tags冲刺第82个*
