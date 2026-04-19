---
title: Čech上同调与层上同调
description: 详细介绍Čech上同调的构造、与层上同调的比较定理、仿射覆盖上的计算技巧，以及它在代数几何计算中的实际应用。
msc_primary: 14

  - 14F05
  - 18F20
  - 55N30
processed_at: '2026-04-16'
---

# Čech 上同调与层上同调

## 引言

层上同调虽然定义优美，但直接通过内射分解来计算往往不切实际。Čech 上同调提供了一种更直观、更可计算的方法：它利用开覆盖，将层上同调转化为组合复形的上同调。对于代数几何中最重要的情形——仿射概形上的拟凝聚层——Čech 上同调与层上同调完全一致，从而成为实际计算的首选工具。

本教程将系统介绍 Čech 上同调的构造、与层上同调的关系，以及在射影空间上的典型计算。

---

## 一、Čech 复形的构造

### 1.1 开覆盖与交错链

设 $X$ 是拓扑空间，$\mathcal{U} = \{U_i\}_{i \in I}$ 是 $X$ 的开覆盖，$\mathcal{F}$ 是 $X$ 上的 Abel 群层。对每个 $p \geq 0$，定义**Čech 群**：

$$\check{C}^p(\mathcal{U}, \mathcal{F}) = \prod_{i_0 < i_1 < \cdots < i_p} \mathcal{F}(U_{i_0} \cap U_{i_1} \cap \cdots \cap U_{i_p})$$

一个元素 $\alpha \in \check{C}^p(\mathcal{U}, \mathcal{F})$ 由一族截面 $\alpha_{i_0 \cdots i_p}$ 组成，定义在每个 $p+1$ 重交上。

### 1.2 微分

**Čech 微分** $\delta: \check{C}^p \to \check{C}^{p+1}$ 定义为交错和：

$$(\delta \alpha)_{i_0 \cdots i_{p+1}} = \sum_{k=0}^{p+1} (-1)^k \alpha_{i_0 \cdots \widehat{i_k} \cdots i_{p+1}}|_{U_{i_0} \cap \cdots \cap U_{i_{p+1}}}$$

可以验证 $\delta^2 = 0$，因此 $(\check{C}^\bullet(\mathcal{U}, \mathcal{F}), \delta)$ 是一个上链复形。

### 1.3 Čech 上同调

**Čech 上同调群**定义为该复形的上同调：

$$\check{H}^p(\mathcal{U}, \mathcal{F}) = H^p(\check{C}^\bullet(\mathcal{U}, \mathcal{F}))$$

对所有开覆盖取正向极限，得到**Čech 上同调**：

$$\check{H}^p(X, \mathcal{F}) = \varinjlim_{\mathcal{U}} \check{H}^p(\mathcal{U}, \mathcal{F})$$

---

## 二、比较定理

### 2.1 Leray 定理

**定理**（Leray）：设 $\mathcal{U}$ 是 $X$ 的开覆盖，满足对所有有限交 $U_{i_0} \cap \cdots \cap U_{i_p}$ 和 $q > 0$，有 $H^q(U_{i_0} \cap \cdots \cap U_{i_p}, \mathcal{F}) = 0$。则：

$$\check{H}^p(\mathcal{U}, \mathcal{F}) \cong H^p(X, \mathcal{F})$$

这样的覆盖称为**$\mathcal{F}$-无环覆盖**（acyclic cover）。

### 2.2 代数几何中的情形

设 $X$ 是概形，$\mathcal{F}$ 是拟凝聚层。取 $X$ 的仿射开覆盖 $\mathcal{U} = \{U_i = \text{Spec}(A_i)\}$。由于仿射开集的任意有限交仍是仿射的（在分离概形上），且仿射概形上拟凝聚层的高阶上同调为零（Serre 定理），因此：

**定理**：对分离概形 $X$ 和拟凝聚层 $\mathcal{F}$，任意仿射开覆盖 $\mathcal{U}$ 都是无环的，从而：

$$\check{H}^p(\mathcal{U}, \mathcal{F}) \cong H^p(X, \mathcal{F})$$

这一定理是代数几何中计算层上同调的基本工具。

### 2.3 Čech 与层的等价性

对任意仿紧拓扑空间（或更一般地，满足某些条件的拓扑空间）和任意层，有：

$$\check{H}^p(X, \mathcal{F}) \cong H^p(X, \mathcal{F})$$

对 $p = 0, 1$ 恒成立，对更高阶需要额外条件。在概形理论中，分离概形上的拟凝聚层满足这一等价性。

---

## 三、典型计算：射影空间

### 3.1 $\mathbb{P}^1$ 的计算

设 $X = \mathbb{P}^1_k$，标准仿射覆盖 $\mathcal{U} = \{U_0, U_1\}$，其中：
- $U_0 = \text{Spec}(k[x])$
- $U_1 = \text{Spec}(k[y])$
- $U_0 \cap U_1 = \text{Spec}(k[x, x^{-1}])$，$y = x^{-1}$

计算 $H^i(X, \mathcal{O}(m))$：

**$i = 0$**：$\check{H}^0$ 是核：
$$\ker(\delta) = \{(f_0, f_1) \in \mathcal{O}(m)(U_0) \times \mathcal{O}(m)(U_1) \mid f_0 = f_1 \text{ 在 } U_0 \cap U_1\}$$
当 $m \geq 0$ 时，这是 $m$ 次齐次多项式空间，维数为 $m+1$。

**$i = 1$**：$\check{H}^1$ 是余核：
$$\text{coker}(\mathcal{O}(m)(U_0) \oplus \mathcal{O}(m)(U_1) \to \mathcal{O}(m)(U_0 \cap U_1))$$
当 $m \geq -1$ 时，映射是满的，因此 $H^1 = 0$。
当 $m \leq -2$ 时，$H^1$ 的维数为 $-m-1$。

### 3.2 一般射影空间

对 $\mathbb{P}^n$，标准覆盖有 $n+1$ 个开集，Čech 复形更复杂，但核心思想相同。通过分析 $n+1$ 重交上的 Laurent 多项式，可以恢复 Bott 公式的完整结果。

---

## 四、Čech 上同调的优势与局限

### 4.1 优势

- **显式计算**：完全通过截面数据计算，不涉及抽象的内射分解；
- **组合结构**：复形结构清晰，便于编程实现；
- **与覆盖相关**：不同的覆盖给出不同的复形，但都收敛到相同的上同调。

### 4.2 局限

- 对非分离概形或非拟凝聚层，仿射覆盖可能不是无环的；
- 对高维拓扑空间，Čech 上同调可能与层上同调不一致；
- 无法直接处理导出范畴中的高阶结构。

---

## 五、习题

### 习题 1
用 Čech 上同调重新计算 $H^0(\mathbb{P}^1, \mathcal{O})$ 和 $H^1(\mathbb{P}^1, \mathcal{O})$。

### 习题 2
设 $X = \mathbb{P}^2$ 用标准仿射覆盖 $\{U_0, U_1, U_2\}$。写出 $\check{C}^0$, $\check{C}^1$, $\check{C}^2$ 的显式形式。

### 习题 3
证明：若 $X$ 是仿射概形，$\mathcal{U}$ 是任意仿射开覆盖，$\mathcal{F}$ 是拟凝聚层，则 $\check{H}^p(\mathcal{U}, \mathcal{F}) = 0$ 对所有 $p > 0$。

### 习题 4
设 $E$ 是椭圆曲线，$\mathcal{U} = \{U, V\}$ 是由两个仿射开集组成的覆盖。描述 $\check{H}^1(\mathcal{U}, \mathcal{O})$ 并解释其维数。

---

## 延伸阅读

- **教材推荐**：Hartshorne, R. *Algebraic Geometry*, Chap. III.4, Springer, 1977.
- **网络资源**：Stacks Project, Tag [01X9](https://stacks.math.columbia.edu/tag/01X9).
- **项目内延伸阅读**：
  - [数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/17-Cech上同调与层上同调](../../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/17-Cech上同调与层上同调.md)
  - [数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/01-层上同调基础](../../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/01-层上同调基础.md)

---

**文档状态**：✅ 完成  
**字数**：约 2,400 字  
**最后更新**：2026-04-16
