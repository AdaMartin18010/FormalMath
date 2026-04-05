---
title: "triangulated范畴 - 深度版"
msc_primary: "18G80"
msc_secondary: ["18E30", "55U35", "14F05"]
processed_at: '2026-04-05'
---

# triangulated范畴 - 深度版

> **"triangulated范畴是导出范畴的公理化基础，它为上同调理论提供了统一的代数框架。"** —— 现代同调代数的基础

---

## 📚 概述

triangulated范畴（三角范畴）是Verdier在1967年引入的代数结构，它是导出范畴和稳定同伦范畴的公理化基础。三角范畴公理化了"distinguished triangles"（可区分的三角形）的概念，为上同调长正合序列提供了范畴论基础。

---

## 🕰️ 历史发展与数学家理念

### Verdier的公理化

**Verdier数学理念**的核心贡献：

1. **公理化方法**：从具体例子（导出范畴）抽象出一般结构
2. **局部化理论**：在三角范畴中反转一类态射
3. **t-结构理论**：从三角范畴提取阿贝尔范畴

### 格洛腾迪克的六函子形式

**格洛腾迪克数学理念**关于**上同调的形式化**：

- **六函子**：$f^*, f_*, f^!, f_!, \otimes, \text{Hom}$
- **对偶性**：Verdier对偶在三角范畴框架中的表达
- **稳定无穷范畴**：三角范畴的现代推广

### 稳定同伦论的联系

**代数拓扑**的发展与三角范畴：

- **稳定同伦范畴**：拓扑空间的谱范畴
- **Brown可表性**：从广义上同调构造谱
- **motivic稳定同伦范畴**：Voevodsky的 motivic理论

---

## 🏗️ 核心概念与完整证明

### 1. 基本定义

**定义 20.1**（三角范畴）
**三角范畴**是加法范畴$D$配备：

1. **平移自同构**$[1]: D \to D$（记$X[n] = [1]^n X$）
2. **distinguished triangles**（可区分三角形）的类

满足以下公理：

**TR1**（基本公理）：

- $X \overset{id}{\to} X \to 0 \to X[1]$是distinguished
- 与distinguished triangle同构的三角形是distinguished
- 任意态射$u: X \to Y$可嵌入distinguished triangle：
$$X \overset{u}{\longrightarrow} Y \overset{v}{\longrightarrow} Z \overset{w}{\longrightarrow} X[1]$$

**TR2**（旋转公理）：
$$X \overset{u}{\longrightarrow} Y \overset{v}{\longrightarrow} Z \overset{w}{\longrightarrow} X[1]$$
是distinguished当且仅当：
$$Y \overset{v}{\longrightarrow} Z \overset{w}{\longrightarrow} X[1] \overset{-u[1]}{\longrightarrow} Y[1]$$
是distinguished。

**TR3**（映射公理）：
给定两个distinguished triangles之间的交换方块：

```
X  → Y  → Z  → X[1]
↓f   ↓g
X' → Y' → Z' → X'[1]
```

存在$h: Z \to Z'$使上图交换。

**TR4**（八面体公理）：
给定两个可复合的态射$X \overset{u}{\to} Y \overset{v}{\to} Z$，存在八面体结构使得相关三角形都是distinguished。

### 2. 从同伦范畴到三角范畴

**定理 20.1**：同伦范畴$K(\mathcal{A})$是三角范畴。

**证明概要**：

**步骤1**：定义平移。

$A^\bullet[1]$：$(A^\bullet[1])^n = A^{n+1}$，微分$d_{A[1]} = -d_A$。

**步骤2**：定义mapping cone。

对链映射$f: A^\bullet \to B^\bullet$，**mapping cone**$C(f)^\bullet$：
$$C(f)^n = A^{n+1} \oplus B^n$$
微分：
$$d = \begin{pmatrix} -d_A & 0 \\ f & d_B \end{pmatrix}$$

**步骤3**：验证distinguished triangles。

序列：
$$A^\bullet \overset{f}{\longrightarrow} B^\bullet \overset{i}{\longrightarrow} C(f)^\bullet \overset{p}{\longrightarrow} A^\bullet[1]$$
其中$i(b) = (0, b)$，$p(a, b) = a$。

验证这是distinguished triangle。

**步骤4**：验证公理TR1-TR4。

- **TR1**：由mapping cone构造
- **TR2**：旋转对应于不同的mapping cone
- **TR3**：同伦范畴的映射性质
- **TR4**：复杂的同伦代数验证

### 3. 导出范畴的三角结构

**定理 20.2**：导出范畴$D(\mathcal{A})$是三角范畴。

**证明要点**：

**步骤1**：$D(\mathcal{A})$是$K(\mathcal{A})$的Verdier局部化。

**步骤2**：拟同构的乘法系与三角结构相容。

**步骤3**：局部化后三角结构自然延拓。

**关键性质**：

- distinguished triangles对应于长正合上同调序列
- 旋转公理对应于上同调的长正合序列的连接同态

### 4. t-结构与 heart

**定义 20.2**（t-结构）
三角范畴$D$上的**t-结构**是一对满子范畴$(D^{\leq 0}, D^{\geq 0})$满足：

1. $D^{\leq 0}[1] \subseteq D^{\leq 0}$，$D^{\geq 0}[-1] \subseteq D^{\geq 0}$
2. $\text{Hom}(X, Y) = 0$对$X \in D^{\leq 0}$，$Y \in D^{\geq 1}$
3. 任意$Z \in D$存在 distinguished triangle：
$$\tau^{\leq 0} Z \to Z \to \tau^{\geq 1} Z \to$$

**定理 20.3**（Verdier）：t-结构的**heart**$D^\heartsuit = D^{\leq 0} \cap D^{\geq 0}$是阿贝尔范畴。

**证明概要**：

**步骤1**：定义核与余核。

对$f: A \to B$在$D^\heartsuit$中，构造：
$$A \overset{f}{\longrightarrow} B \overset{g}{\longrightarrow} C \overset{h}{\longrightarrow} A[1]$$

则$\ker f = \tau^{\leq 0} C[-1]$，$\text{coker} f = \tau^{\geq 0} C$。

**步骤2**：验证阿贝尔范畴公理。

利用三角范畴公理和t-结构性质验证。

### 5. Verdier对偶

**定义 20.3**（对偶izing复形）
在适当的三角范畴（如有界导出范畴$D^b_c(X)$）中，**对偶izing复形**$\omega_X$使得：
$$\mathbb{D}(-) = R\text{Hom}(-, \omega_X)$$
是对偶函子。

**定理 20.4**（Verdier对偶）：$\mathbb{D}^2 \cong \text{id}$（在适当子范畴上）。

---

## 🧮 应用与联系

### 代数几何

- **导出范畴$D^b(X)$**：凝聚层的有界导出范畴
- **Fourier-Mukai变换**：$\Phi_{\mathcal{E}}(F) = Rq_*(Lp^*F \otimes \mathcal{E})$
- **桥接几何与代数**：Homological Mirror Symmetry

### 表示论

- **导出范畴的块分解**：Broué猜想
- **Koszul对偶性**：代数表示论的三角范畴方法

### 代数拓扑

- **稳定同伦范畴**：谱的三角范畴
- **广义上同调**：Brown可表性定理

---

## 📚 参考文献

1. **Verdier, J.-L.** (1996). *Des Catégories Dérivées des Catégories Abéliennes*. Astérisque.
2. **Neeman, A.** (2001). *Triangulated Categories*. Princeton University Press.
3. **Gelfand, S. I., & Manin, Y. I.** (2003). *Methods of Homological Algebra* (2nd ed.). Springer.
4. **Huybrechts, D.** (2006). *Fourier-Mukai Transforms in Algebraic Geometry*. Oxford.

---

*文档版本: 1.0*
*创建日期: 2026年4月*
*最后更新: 2026年4月*
