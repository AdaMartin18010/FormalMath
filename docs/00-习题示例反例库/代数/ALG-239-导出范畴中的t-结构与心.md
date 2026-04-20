---
msc_primary: 18

  - 18E30
exercise_id: ALG-239
title: 导出范畴中的t-结构与心
difficulty: 3
type: PRF
topic: 代数
subtopic: 导出范畴
source:
  course: 研究级课程
  chapter: "1.0"
  original: true
processed_at: '2026-04-10'
---

# ALG-239: 导出范畴中的 t-结构与心

**题号**: ALG-239
**难度**: ⭐⭐⭐ (Level 3)
**类型**: 证明型 (PRF)
**来源**: 研究级课程
**主题**: 导出范畴

---

## 题目

**(a)** 定义三角范畴中的 t-结构，给出 heart 的构造。

**(b)** 证明 heart 是 Abel 范畴。

**(c)** 讨论标准 t-结构、perverse t-结构及其应用。

---

## 解答

### (a) t-结构与 Heart 的定义

**定义（t-结构，Beilinson-Bernstein-Deligne, 1982）**：设 $\mathcal{D}$ 是三角范畴。$\mathcal{D}$ 上的 **t-结构**是一对全子范畴 $(\mathcal{D}^{\leq 0}, \mathcal{D}^{\geq 0})$，满足：

1. **平移**：$\mathcal{D}^{\leq 0}[1] \subset \mathcal{D}^{\leq 0}$，$\mathcal{D}^{\geq 0}[-1] \subset \mathcal{D}^{\geq 0}$。等价地，$\mathcal{D}^{\leq n} := \mathcal{D}^{\leq 0}[-n]$，$\mathcal{D}^{\geq n} := \mathcal{D}^{\geq 0}[-n]$。

2. **Hom 消失**：对 $X \in \mathcal{D}^{\leq 0}$，$Y \in \mathcal{D}^{\geq 1}$，有：
   $$\text{Hom}_{\mathcal{D}}(X, Y) = 0$$

3. **分解**：对任意 $Z \in \mathcal{D}$，存在 distinguished triangle：
   $$X \to Z \to Y \to X[1]$$
   其中 $X \in \mathcal{D}^{\leq 0}$，$Y \in \mathcal{D}^{\geq 1}$。

**Heart（心）**：t-结构的 **heart** 定义为：
$$\mathcal{A} = \mathcal{D}^{\leq 0} \cap \mathcal{D}^{\geq 0}$$

它是 $\mathcal{D}$ 中的全子范畴。

**关键例子**：

- **标准 t-结构**：$\mathcal{D} = D^b(\mathcal{A})$（Abel 范畴的有界导出范畴）。$\mathcal{D}^{\leq 0} = \{C^\bullet : H^i(C^\bullet) = 0 \text{ for } i > 0\}$，$\mathcal{D}^{\geq 0} = \{C^\bullet : H^i(C^\bullet) = 0 \text{ for } i < 0\}$。Heart 是 $\mathcal{A}$ 本身（复形集中在度 0）。

- **Perverse t-结构**：见 (c)。

### (b) Heart 是 Abel 范畴

**定理（BBD）**：t-结构的 heart $\mathcal{A}$ 是 Abel 范畴。

**证明**：

**步骤 1：核与余核的构造**

设 $f: A \to B$ 是 $\mathcal{A}$ 中的态射。在 $\mathcal{D}$ 中，考虑 distinguished triangle：
$$A \xrightarrow{f} B \to C \to A[1]$$

由 t-结构的分解性质，$C$ 有分解：
$$C^{\leq 0} \to C \to C^{\geq 1} \to C^{\leq 0}[1]$$

定义：
$$\ker f = C^{\geq 1}[-1], \quad \text{coker } f = C^{\leq 0}$$

需验证它们在 heart 中，且满足泛性质。

**步骤 2：验证 $
ker f \in \mathcal{A}$**

$C^{\geq 1}[-1] \in \mathcal{D}^{\geq 0}$（因 $C^{\geq 1} \in \mathcal{D}^{\geq 1}$，平移 $[-1]$）。需证 $C^{\geq 1}[-1] \in \mathcal{D}^{\leq 0}$。

由 distinguished triangle $C^{\leq 0} \to C \to C^{\geq 1} \to$ 及 $C^{\leq 0} \in \mathcal{D}^{\leq 0}$，$C^{\geq 1} \in \mathcal{D}^{\geq 1}$，以及 Hom 消失性，可得 $C^{\geq 1}[-1] \in \mathcal{D}^{\leq 0}$。

类似地，$\text{coker } f = C^{\leq 0} \in \mathcal{D}^{\leq 0}$，且由 triangle 的正合性，$C^{\leq 0} \in \mathcal{D}^{\geq 0}$。

**步骤 3：验证泛性质**

对 $K \in \mathcal{A}$ 满足 $K \to A \xrightarrow{f} B$ 为零，$K \to A \to B \to C \to A[1]$ 给出 $K \to C$。因 $K \in \mathcal{D}^{\leq 0}$，$C^{\geq 1} \in \mathcal{D}^{\geq 1}$，$\text{Hom}(K, C^{\geq 1}) = 0$。故 $K \to C$ 穿过 $C^{\leq 0}[-1]$？实际上由分解 $C \to C^{\geq 1}$ 的映射为零，$K \to C$ 穿过 $C^{\leq 0}$。然后利用 $C^{\leq 0} \to C^{\geq 1}[1]$ 的 distinguished triangle，得唯一映射 $K \to C^{\geq 1}[-1] = \ker f$。

**步骤 4：单态射与满态射**

$f$ 是单态射当且仅当 $\ker f = 0$（在 $\mathcal{A}$ 中），当且仅当 $C^{\geq 1}[-1] = 0$，当且仅当 $C \in \mathcal{D}^{\leq 0}$。

类似地，$f$ 是满态射当且仅当 $\text{coker } f = 0$，当且仅当 $C^{\leq 0} = 0$，当且仅当 $C \in \mathcal{D}^{\geq 1}$。

若 $f$ 既单又满，则 $C \in \mathcal{D}^{\leq 0} \cap \mathcal{D}^{\geq 1} = \{0\}$（因 $\mathcal{D}^{\leq 0} \cap \mathcal{D}^{\geq 1} \subset \mathcal{D}^{\leq 0} \cap \mathcal{D}^{\geq 0}[-1] = \mathcal{A}[-1]$，但 $X \in \mathcal{D}^{\leq 0}$，$Y \in \mathcal{D}^{\geq 0}$ 时 $\text{Hom}(X, Y[-1]) = 0$，推出交为 0）。故 $C = 0$，$f$ 是同构。

### (c) 标准与 Perverse t-结构

**标准 t-结构**：$\mathcal{D} = D^b(X)$，$X$ 是簇。
$$\mathcal{D}^{\leq 0} = \{K : H^i(K) = 0, i > 0\}$$
$$\mathcal{D}^{\geq 0} = \{K : H^i(K) = 0, i < 0\}$$
Heart = $Coh(X)$（凝聚层）。

**Perverse t-结构（BBD）**：设 $X$ 是代数簇，允许奇点。定义 perverse t-结构（对中间 perversity）：
$$\begin{aligned}
{}^p\mathcal{D}^{\leq 0} &= \{K : \dim \text{supp } H^i(K) \leq -i, \forall i\} \\
{}^p\mathcal{D}^{\geq 0} &= \{K : \dim \text{supp } H^i(\mathbb{D}K) \leq -i, \forall i\}
\end{aligned}$$

其中 $\mathbb{D}$ 是 Verdier 对偶。等价地，对光滑 stratification，要求 stalk 和上 stalk 的维数条件。

**Perverse sheaves**：$Perv(X) = {}^p\mathcal{D}^{\leq 0} \cap {}^p\mathcal{D}^{\geq 0}$ 是 heart，称为 **perverse sheaves**。它是 Abel 范畴，Artinian 和 Noetherian。

**应用**：

1. **分解定理**：若 $f: X \to Y$ 是 proper 代数态射，$IC_X$ 是中间扩张，则：
   $$Rf_* IC_X \cong \bigoplus_i {}^p\mathcal{H}^i(Rf_* IC_X)[-i]$$
   且每项是半单 perverse sheaf。

2. **Kazhdan-Lusztig 猜想**：通过 perverse sheaves on flag variety 和分解定理，证明李代数表示的 Kazhdan-Lusztig 多项式给出 Verma 模的合成因子重数。

**常见错误**：
- 将 t-结构等同于 filtration：t-结构是三角范畴的结构，不是简单的 filtration。
- 忽视 heart 中的短正合列与 distinguished triangle 的区别：heart 中 $0 \to A \to B \to C \to 0$ 对应 distinguished triangle $A \to B \to C \to A[1]$，但反之不成立（后者不一定在 heart 中）。
- 混淆 perverse sheaf 与通常 sheaf：perverse sheaf 是复形，不是单个 sheaf；它可能在通常意义下有多个非零上同调层。

**参考文献**：
- A. Beilinson, J. Bernstein, P. Deligne, *Faisceaux pervers*, Astérisque 100, 1982
- S. Gelfand, Y. Manin, *Methods of Homological Algebra*, Springer, 2003
- M. Kashiwara, P. Schapira, *Sheaves on Manifolds*, Springer, 1990
- R. Bezrukavnikov, I. Loseu, "Etingof's conjecture for rectangular rational Cherednik algebras", 2015
