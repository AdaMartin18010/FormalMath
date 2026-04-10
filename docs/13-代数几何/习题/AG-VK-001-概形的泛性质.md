---
title: 概形的泛性质
msc_primary: 14-01
msc_secondary:
- 14A15
- 18A40
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 4-5
topic: 概形的泛性质与构造
exercise_type: EXP (探索型)
difficulty: ⭐⭐⭐
importance: ★★
---

# AG-VK-001: 概形的泛性质

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 4-5: 概形理论 |
| **对应FOAG习题** | 4.3.B, 5.1.F |
| **类型** | EXP (探索型) |
| **难度** | ⭐⭐⭐ |
| **重要性** | ★★ |

---

## 问题陈述

### 主问题

设 $k$ 是一个域，考虑仿射直线 $\mathbb{A}^1_k = \operatorname{Spec} k[x]$。

**(a)** 证明：对于任意 $k$-概形 $X$，给出一个 $k$-态射 $f: X \to \mathbb{A}^1_k$ 等价于给出一个整体截面 $s \in \Gamma(X, \mathcal{O}_X)$。

**(b)** 更一般地，设 $A$ 是任意环，$S = \operatorname{Spec} A$。证明：对于任意 $S$-概形 $X$，给出一个 $S$-态射 $X \to \mathbb{A}^1_S$ 等价于给出一个 $\mathcal{O}_X$-模同态 $\mathcal{O}_X \to \mathcal{O}_X$。

**(c)** 解释这个结果如何体现了"泛性质"的思想。

---

## 解题思路

### 思路概述

本题探索的是**仿射直线的泛性质**——它是代数几何中最基本的代表函子之一。核心思想是：

> **$\mathbb{A}^1$ 代表整体截面函子**

### 关键步骤

```
证明路线图

Step 1: 局部情形
├─ 设 X = Spec B 是仿射概形
├─ k-态射 Spec B → Spec k[x] 对应环同态 k[x] → B
├─ 而 k[x] → B 由 x 的像唯一确定
└─ x 的像就是 B 的一个元素，即 Γ(X, 𝒪_X) 的元素

Step 2: 整体情形
├─ 一般概形可用仿射覆盖
├─ 态射可以黏合当且仅当局部数据相容
└─ 截面也可以黏合，两者对应关系保持

Step 3: 相对情形 (b部分)
├─ 将 k 替换为任意环 A
├─ A[x] → B 对应 B 作为 A-代数的结构
└─ 即给出一个 A-线性映射 A → B，也就是截面
```

---

## 详细解答

### (a) 仿射直线代表整体截面函子

**证明**：

**Step 1**: 先考虑 $X = \operatorname{Spec} B$ 是仿射概形的情形。

由仿射概形的范畴等价，$k$-态射 $f: \operatorname{Spec} B \to \operatorname{Spec} k[x]$ 一一对应于 $k$-代数同态：
$$f^*: k[x] \to B$$

而 $k[x]$ 是自由 $k$-代数（一个生成元的多项式代数），所以：
$$\operatorname{Hom}_{k\text{-alg}}(k[x], B) \cong B$$

对应关系为：$\phi \mapsto \phi(x)$。

注意 $B = \Gamma(\operatorname{Spec} B, \mathcal{O}_{\operatorname{Spec} B})$，这正是我们需要的整体截面。

**Step 2**: 设 $X$ 是任意 $k$-概形，取仿射开覆盖 $\{U_i = \operatorname{Spec} A_i\}$。

一个 $k$-态射 $f: X \to \mathbb{A}^1_k$ 由限制 $\{f|_{U_i}: U_i \to \mathbb{A}^1_k\}$ 决定，且满足相容性条件：
$$f|_{U_i}|_{U_i \cap U_j} = f|_{U_j}|_{U_i \cap U_j}$$

由Step 1，每个 $f|_{U_i}$ 对应 $s_i \in \Gamma(U_i, \mathcal{O}_X)$。相容性条件转化为：
$$s_i|_{U_i \cap U_j} = s_j|_{U_i \cap U_j}$$

由层的公理，这等价于整体截面 $s \in \Gamma(X, \mathcal{O}_X)$。

∎

### (b) 相对情形的推广

**证明**：

设 $S = \operatorname{Spec} A$，$X$ 是 $S$-概形。

类似地，$S$-态射 $X \to \mathbb{A}^1_S = \operatorname{Spec} A[x]$ 对应 $A$-代数同态 $A[x] \to \Gamma(X, \mathcal{O}_X)$。

而：
$$\operatorname{Hom}_{A\text{-alg}}(A[x], B) \cong B$$

作为集合，这同构于 $\operatorname{Hom}_A(A, B)$（将 $1 \in A$ 映到 $b \in B$）。

用层语言，这正是 $\mathcal{O}_X$-模同态 $\mathcal{O}_X \to \mathcal{O}_X$（由 $1 \mapsto s$ 给出）。

∎

### (c) 泛性质的解释

**解释**：

本题展示的是**可表函子**的基本例子。定义函子：
$$\mathbf{\Gamma}: (\text{Sch}/k)^{\text{op}} \to \text{Set}, \quad X \mapsto \Gamma(X, \mathcal{O}_X)$$

则我们证明了：
$$\mathbf{\Gamma} \cong \operatorname{Hom}_{\text{Sch}/k}(-, \mathbb{A}^1_k)$$

即 **$\mathbb{A}^1_k$ 代表函子 $\mathbf{\Gamma}$**。

这正是泛性质的体现：$\mathbb{A}^1_k$ 是使得"给出一个态射"与"给出一个截面"等价的最"经济"的对象。

---

## 关键概念

### 可表函子 (Representable Functor)

设 $\mathcal{C}$ 是范畴，$F: \mathcal{C}^{\text{op}} \to \text{Set}$ 是函子。

**定义**：若存在对象 $X \in \mathcal{C}$ 使得 $F \cong \operatorname{Hom}_{\mathcal{C}}(-, X)$，则称 $F$ 是**可表的**，$X$ 称为 $F$ 的**代表**。

### 泛性质的意义

| 几何对象 | 代表的函子 | 泛性质 |
|----------|-----------|--------|
| $\mathbb{A}^1_k$ | $X \mapsto \Gamma(X, \mathcal{O}_X)$ | 截面函子 |
| $\mathbb{A}^n_k$ | $X \mapsto \Gamma(X, \mathcal{O}_X)^n$ | $n$ 元组截面 |
| $\mathbb{P}^n_k$ | $X \mapsto \{\text{线丛满射 } \mathcal{O}_X^{n+1} \twoheadrightarrow \mathcal{L}\}$ | 线丛商 |
| $\operatorname{GL}_n$ | $X \mapsto \operatorname{GL}_n(\Gamma(X, \mathcal{O}_X))$ | 可逆矩阵 |

---

## 相关结果

### 更一般的泛性质

**定理**（仿射空间的泛性质）：
$$\operatorname{Hom}_S(X, \mathbb{A}^n_S) \cong \Gamma(X, \mathcal{O}_X)^n$$

**定理**（射影空间的泛性质）：
对于 $S$-概形 $X$，给出一个 $S$-态射 $X \to \mathbb{P}^n_S$ 等价于给出一个可逆层 $\mathcal{L}$ 和满射 $\mathcal{O}_X^{n+1} \twoheadrightarrow \mathcal{L}$（模去标量等价）。

---

## 变式练习

### 变式 1: 乘法群概形

证明：$\mathbb{G}_m = \operatorname{Spec} k[x, x^{-1}]$ 代表函子 $X \mapsto \Gamma(X, \mathcal{O}_X)^\times$（可逆元群）。

### 变式 2: 一般线性群

证明：$\operatorname{GL}_n = \operatorname{Spec} k[x_{ij}, \det^{-1}]$ 代表函子 $X \mapsto \operatorname{GL}_n(\Gamma(X, \mathcal{O}_X))$。

### 变式 3: 纤维积的泛性质

设 $X \to Z$ 和 $Y \to Z$ 是概形态射。证明：给出一个概形 $W$ 到 $X \times_Z Y$ 的态射等价于给出相容的态射对 $W \to X$ 和 $W \to Y$。

---

## 常见错误

| 错误 | 纠正 |
|------|------|
| 认为 $\mathbb{A}^1$ 只是"坐标轴" | $\mathbb{A}^1$ 是函子意义下的对象，不只是集合 |
| 忽略层条件 | 从局部到整体需要检查相容性 |
| 混淆绝对与相对情形 | 明确是在 $\text{Sch}/k$ 还是 $\text{Sch}/S$ 中工作 |

---

## 学习建议

1. **理解泛性质的本质**：将几何对象理解为它所"代表"的函子
2. **熟练掌握层论**：从局部到整体的黏合是代数几何的核心技术
3. **对比其他例子**：射影空间、Grassmannian 等都有类似的泛性质

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-001-概形的泛性质.md`  
**创建日期**: 2026-04-10  
**最后更新**: 2026-04-10
