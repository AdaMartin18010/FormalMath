---
title: Étale Topos与平展上同调
description: 从Topos理论视角重新审视平展拓扑、平展Topos的构造、几何态射以及平展上同调作为Topos上同调的自然性。
msc_primary: 14F20
msc_secondary:
- 18B25
- 14L30
processed_at: '2026-04-16'
---

# Étale Topos 与平展上同调

## 引言

在格洛腾迪克创立平展上同调的过程中，他从未将其仅仅视为一种计算方法，而是将其纳入了更宏大的 Topos 理论框架中。对每个概形 $X$，平展位型 $X_{\text{ét}}$ 上的层范畴 $\mathbf{Sh}(X_{\text{ét}})$ 是一个 Grothendieck Topos，称为 **$X$ 的平展 Topos**（étale topos）。平展上同调就是这个 Topos 的上同调。从 Topos 的视角看，平展上同调与拓扑空间上的奇异上同调在结构上完全类似——它们都是某个合适的"空间"上的层上同调。

本教程将介绍平展 Topos 的构造、其几何态射以及它与 Zariski Topos 的关系。

---

## 一、平展 Topos 的构造

### 1.1 平展位型回顾

设 $X$ 是概形。$X$ 上的**平展位型** $X_{\text{ét}}$ 定义如下：
- **对象**：所有平展态射 $U \to X$；
- **态射**：$X$-态射 $V \to U$；
- **覆盖**：一族平展态射 $\{U_i \to U\}$ 是覆盖，如果 $\bigcup_i \text{Im}(U_i) = U$。

### 1.2 平展 Topos

**$X$ 的平展 Topos**定义为层范畴：

$$X_{\text{ét}}^\sim = \mathbf{Sh}(X_{\text{ét}})$$

这是一个 Grothendieck Topos。其中的对象是 $X$ 上的**平展层**（étale sheaf）。

### 1.3 与 Zariski Topos 的比较

Zariski Topos $X_{\text{Zar}}^\sim = \mathbf{Sh}(X_{\text{Zar}})$ 是 $X$ 的开子集范畴上的层范畴。由于每个 Zariski 开浸入都是平展的，存在自然的**包含几何态射**：

$$i: X_{\text{ét}}^\sim \longrightarrow X_{\text{Zar}}^\sim$$

其中 $i_*$ 是将 Zariski 层限制为平展层（因为平展拓扑更细），$i^*$ 是其左伴随。这一几何态射反映了平展拓扑比 Zariski 拓扑"更细"的事实。

---

## 二、概形态射诱导的几何态射

### 2.1 一般概形态射

设 $f: X \to Y$ 是概形态射（不必平展）。则 $f$ 诱导几何态射：

$$f: X_{\text{ét}}^\sim \longrightarrow Y_{\text{ét}}^\sim$$

其中：
- $f_*\mathcal{F}$ 是推前层：$(f_*\mathcal{F})(V \to Y) = \mathcal{F}(V \times_Y X \to X)$；
- $f^*\mathcal{G}$ 是拉回层，由左 Kan 延拓给出。

### 2.2 平展态射的特殊性

若 $f: X \to Y$ 是平展的，则诱导的几何态射具有特殊性质：$f^*$ 是**本质满且忠实的**，且 $f_*$ 是其右伴随和左逆。这类几何态射称为**平展几何态射**（étale geometric morphism），它在平展 Topos 理论中扮演类似于拓扑中局部同胚的角色。

### 2.3 基变化

考虑卡氏图：

$$\begin{array}{ccc}
X' & \longrightarrow & X \\
\downarrow & & \downarrow \\
Y' & \longrightarrow & Y
\end{array}$$

则有 Topos 理论的卡氏图：

$$\begin{array}{ccc}
(X')_{\text{ét}}^\sim & \longrightarrow & X_{\text{ét}}^\sim \\
\downarrow & & \downarrow \\
(Y')_{\text{ét}}^\sim & \longrightarrow & Y_{\text{ét}}^\sim
\end{array}$$

在某些条件下（如 $Y' \to Y$ 平坦），这是 Topos 意义下的拉回。

---

## 三、平展基本群的 Topos 解释

### 3.1 覆叠与局部等价

在经典拓扑中，连通空间 $X$ 的万有覆叠 $\widetilde{X} \to X$ 诱导了基本群 $\pi_1(X)$ 与覆叠变换群之间的同构。在平展 Topos 中，有限平展覆叠的范畴可以表述为平展几何态射的某种等价类。

### 3.2 Galois Topos

设 $X$ 是连通概形。有限平展覆叠的范畴 $\mathbf{FEt}(X)$ 是一个 Galois 范畴（Galois category）。Galois 范畴等价于某个 profinite 群 $G$ 上的有限连续集范畴。这个群 $G$ 就是平展基本群：

$$\pi_1^{\text{ét}}(X, \bar{x})$$

从 Topos 理论的观点看，$\mathbf{FEt}(X)$ 是平展 Topos 中"局部常值层"的子范畴，而平展基本群就是这些层的"单值群"。

---

## 四、平展上同调作为 Topos 上同调

### 4.1 全局截面函子

平展 Topos 上的**全局截面函子**为：

$$\Gamma_{\text{ét}}(X, -): X_{\text{ét}}^\sim \longrightarrow \mathbf{Set}, \quad \mathcal{F} \longmapsto \mathcal{F}(X)$$

由于 $X_{\text{ét}}^\sim$ 是 Grothendieck Topos，它有足够内射对象，因此可以定义右导出函子。

### 4.2 平展上同调

$$H_{\text{ét}}^i(X, \mathcal{F}) = R^i \Gamma_{\text{ét}}(X, \mathcal{F})$$

这就是平展上同调。它与拓扑空间上的层上同调在形式上完全一致：都是某个 Topos 上的导出函子上同调。

### 4.3 高阶直像

设 $f: X \to Y$ 是概形态射。高阶直像层 $R^i f_* \mathcal{F}$ 正是几何态射 $f: X_{\text{ét}}^\sim \to Y_{\text{ét}}^\sim$ 的推前函子 $f_*$ 的高阶导出函子。这进一步说明了平展上同调与 Topos 理论的统一性。

---

## 五、习题

### 习题 1
证明：Zariski 开浸入 $j: U \hookrightarrow X$ 诱导的平展 Topos 几何态射中，$j^*$ 是忠实的。

### 习题 2
设 $L/K$ 是有限 Galois 扩张。描述 $\text{Spec}(L)_{\text{ét}}^\sim$ 和到 $\text{Spec}(K)_{\text{ét}}^\sim$ 的几何态射。

### 习题 3
解释为什么平展基本群可以定义为平展 Topos 中局部常值层范畴的纤维函子的自同构群。

### 习题 4
设 $f: X \to Y$ 是固有满射。讨论平展 Topos 几何态射 $f: X_{\text{ét}}^\sim \to Y_{\text{ét}}^\sim$ 的性质。

---

## 延伸阅读

- **教材推荐**：Milne, J.S. *Étale Cohomology*, Chap. II, Princeton University Press, 1980.
- **网络资源**：Stacks Project, Tag [03PP](https://stacks.math.columbia.edu/tag/03PP).
- **项目内延伸阅读**：
  - [数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/04-Topos理论/04-étale Topos与平展上同调](../../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/04-Topos理论/04-étale Topos与平展上同调.md)
  - [数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/02-étale上同调](../../../../数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/02-étale上同调.md)

---

**文档状态**：✅ 完成  
**字数**：约 2,400 字  
**最后更新**：2026-04-16
