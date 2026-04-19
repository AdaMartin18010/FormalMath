---
title: Forcing基础理论
msc_primary: 01
msc_secondary:
  - 01A60
  - 01A65
  - 01A70
processed_at: '2026-04-05'
---

# Forcing基础理论

## 目录

- [Forcing基础理论](#forcing基础理论)
  - [目录](#目录)
  - [历史背景与动机](#历史背景与动机)
  - [偏序集与力迫条件](#偏序集与力迫条件)
    - [定义 1.1（偏序集）](#定义-11偏序集)
    - [定义 1.2（相容性）](#定义-12相容性)
    - [定义 1.3（稠密性）](#定义-13稠密性)
  - [稠密开集与泛型滤子](#稠密开集与泛型滤子)
    - [定义 2.1（开集）](#定义-21开集)
    - [定义 2.2（稠密开集）](#定义-22稠密开集)
    - [定义 2.3（滤子）](#定义-23滤子)
    - [定义 2.4（泛型滤子）](#定义-24泛型滤子)
  - [力迫语言与力迫关系](#力迫语言与力迫关系)
    - [定义 3.1（力迫语言）](#定义-31力迫语言)
    - [定义 3.2（求值映射）](#定义-32求值映射)
    - [定义 3.3（力迫关系）](#定义-33力迫关系)
  - [力迫定理](#力迫定理)
    - [定理 4.1（力迫定理）](#定理-41力迫定理)
  - [具体例子：添加Cohen实数](#具体例子添加cohen实数)
    - [例 5.1（Cohen偏序集）](#例-51cohen偏序集)
    - [定理 5.2](#定理-52)
    - [推论 5.3](#推论-53)
  - [参考文献](#参考文献)
  - [MSC编码](#msc编码)

---

## 历史背景与动机

1963年，Paul Cohen在普林斯顿大学完成了数学史上最惊人的突破之一：他证明了连续统假设（CH）独立于ZFC公理系统。这一成果使他获得1966年菲尔兹奖，与哥德尔1938年证明CH与ZFC相容性的工作一起，完整回答了希尔伯特第一问题。

Cohen的原始论文《The independence of the Continuum Hypothesis》发表于1963年和1964年的*Proceedings of the National Academy of Sciences*。他在1966年的专著《Set Theory and the Continuum Hypothesis》中详细阐述了这一理论。Cohen的方法被称为**Forcing（力迫）**，它提供了一种系统性地构造集合论模型的技术。

> **核心洞见**：力迫方法允许我们从一个基础模型 $M$ 出发，通过添加"泛型"对象 $G$ 来构造扩展模型 $M[G]$，从而控制扩展模型中特定命题的真值。

---

## 偏序集与力迫条件

### 定义 1.1（偏序集）

一个**偏序集（partially ordered set，poset）**是一个二元组 $\mathbb{P} = (P, \leq)$，其中 $P$ 是非空集合，$\leq$ 是 $P$ 上的二元关系，满足：

1. **自反性**：$\forall p \in P, \, p \leq p$
2. **传递性**：$\forall p, q, r \in P, \, (p \leq q \land q \leq r) \Rightarrow p \leq r$
3. **反对称性**：$\forall p, q \in P, \, (p \leq q \land q \leq p) \Rightarrow p = q$

在力迫的语境中，$P$ 的元素称为**条件（conditions）**，$p \leq q$ 读作"$p$ 强于 $q$"或"$p$ 扩展 $q$"。

### 定义 1.2（相容性）

设 $\mathbb{P}$ 是偏序集，$p, q \in P$：

- $p$ 和 $q$ 是**相容的（compatible）**，记作 $p \parallel q$，如果存在 $r \in P$ 使得 $r \leq p$ 且 $r \leq q$
- $p$ 和 $q$ 是**不相容的（incompatible）**，记作 $p \perp q$，如果不存在这样的 $r$

### 定义 1.3（稠密性）

子集 $D \subseteq P$ 在 $\mathbb{P}$ 中是**稠密的（dense）**，如果：

$$\forall p \in P, \, \exists q \in D, \, q \leq p$$

子集 $D \subseteq P$ 在 $p$ 之下稠密，如果上述条件对所有 $q \leq p$ 成立。

---

## 稠密开集与泛型滤子

### 定义 2.1（开集）

子集 $U \subseteq P$ 是**开的（open）**或**向上封闭的（upward closed）**，如果：

$$\forall p \in U, \, \forall q \geq p, \, q \in U$$

### 定义 2.2（稠密开集）

子集 $D \subseteq P$ 是**稠密开集（dense open set）**，如果它既是稠密的又是开的。

**直观解释**：稠密开集可以理解为"必然会被遇到"的条件集合。从任何条件出发，通过不断细化（取更强的条件），我们终将落入某个稠密开集中。

### 定义 2.3（滤子）

非空子集 $F \subseteq P$ 是一个**滤子（filter）**，如果：

1. **向上封闭**：$\forall p \in F, \, \forall q \geq p, \, q \in F$
2. **对有限交封闭**：$\forall p, q \in F, \, \exists r \in F, \, r \leq p \land r \leq q$

### 定义 2.4（泛型滤子）

设 $M$ 是ZFC的可数传递模型，$\mathbb{P} \in M$ 是偏序集。滤子 $G \subseteq P$ 是**$M$-泛型的（$M$-generic）**，如果：

$$\forall D \in M, \, (D \subseteq P \text{ 在 } \mathbb{P} \text{ 中稠密}) \Rightarrow G \cap D \neq \emptyset$$

**存在性定理**：如果 $M$ 是可数模型，则对任何偏序集 $\mathbb{P} \in M$，存在 $M$-泛型滤子 $G \subseteq P$。

*证明概要*：由于 $M$ 可数，$P$ 的稠密子集在 $M$ 中只有可数个，记为 $\{D_n : n \in \omega\}$。递归构造序列 $p_0 \geq p_1 \geq p_2 \geq \cdots$ 使得 $p_{n+1} \in D_n$。令 $G = \{q \in P : \exists n, \, q \geq p_n\}$，则 $G$ 是 $M$-泛型滤子。 $\square$

---

## 力迫语言与力迫关系

### 定义 3.1（力迫语言）

设 $\mathbb{P}$ 是偏序集。**力迫语言** $\mathcal{L}_\mathbb{P}$ 是由以下符号构造的集合论语言：

1. **原子符号**：每个 $p \in P$ 是一个常量符号（表示"条件 $p$ 在泛型滤子中"）
2. **名称（names）**：递归定义的类 $\text{Name}^\mathbb{P}$
   - 每个标准集合论对象有规范名称
   - 若 $\tau$ 是一个函数，$\text{dom}(\tau) \subseteq \text{Name}^\mathbb{P}$ 且 $\forall \sigma \in \text{dom}(\tau), \, \tau(\sigma) \subseteq P$，则 $\tau$ 是一个 $\mathbb{P}$-名称

### 定义 3.2（求值映射）

给定泛型滤子 $G \subseteq P$，**求值映射** $\text{val}_G : \text{Name}^\mathbb{P} \to V$ 定义为：

$$\text{val}_G(\tau) = \{\text{val}_G(\sigma) : \exists p \in G, \, (\sigma, p) \in \tau\}$$

### 定义 3.3（力迫关系）

**力迫关系** $\Vdash$ 是一个三元关系，$p \Vdash \varphi(\tau_1, \ldots, \tau_n)$ 表示"条件 $p$ 力迫公式 $\varphi$ 在名称 $\tau_1, \ldots, \tau_n$ 处为真"。

力迫关系通过递归定义：

| 公式类型 | 力迫条件 |
|---------|---------|
| $\tau_1 = \tau_2$ | $p \Vdash \sigma \in \tau_1 \Leftrightarrow p \Vdash \sigma \in \tau_2$ 对所有 $\sigma$ 成立 |
| $\sigma \in \tau$ | $\forall q \leq p, \, \exists r \leq q, \, \exists (\pi, s) \in \tau$ 使得 $r \leq s$ 且 $r \Vdash \pi = \sigma$ |
| $\neg \varphi$ | $\forall q \leq p, \, q \not\Vdash \varphi$ |
| $\varphi \land \psi$ | $p \Vdash \varphi$ 且 $p \Vdash \psi$ |
| $\exists x \, \varphi(x)$ | 集合 $\{q \leq p : \exists \tau, \, q \Vdash \varphi(\tau)\}$ 在 $p$ 下稠密 |

---

## 力迫定理

### 定理 4.1（力迫定理）

设 $M$ 是ZFC的可数传递模型，$\mathbb{P} \in M$，$G$ 是 $M$-泛型滤子。则：

**(a) 真值引理（Truth Lemma）**：
$$M[G] \models \varphi(\text{val}_G(\tau_1), \ldots, \text{val}_G(\tau_n)) \Leftrightarrow \exists p \in G, \, p \Vdash \varphi(\tau_1, \ldots, \tau_n)$$

**(b) 可定义性引理（Definability Lemma）**：
集合 $\{(p, \vec{\tau}) : p \Vdash \varphi(\vec{\tau})\}$ 在 $M$ 中可定义。

**(c) 稠密性引理（Density Lemma）**：
如果 $p \Vdash \exists x \, \varphi(x)$，则存在 $q \leq p$ 和 $\tau$ 使得 $q \Vdash \varphi(\tau)$。

*证明思路*：

- (a) 通过对公式复杂度归纳证明，关键是利用 $G$ 的泛型性
- (b) 利用力迫关系的递归定义可在 $M$ 内部进行
- (c) 由力迫关系对存在量词的定义直接得到 $\square$

---

## 具体例子：添加Cohen实数

### 例 5.1（Cohen偏序集）

Cohen偏序集 $\text{Add}(\omega, 1)$（添加一个Cohen实数）定义为：

$$\mathbb{C} = \{p : p \text{ 是从有限子集 } \text{dom}(p) \subseteq \omega \text{ 到 } 2 \text{ 的函数}\}$$

序关系：$p \leq q$ 当且仅当 $p \supseteq q$（作为函数的扩展）。

**直观理解**：每个条件 $p$ 是对一个"Cohen实数"（$\omega$ 到 $2$ 的函数）的有限部分信息。$p \leq q$ 意味着 $p$ 提供了更多的信息。

### 定理 5.2

设 $G \subseteq \mathbb{C}$ 是 $M$-泛型滤子。则 $g = \bigcup G$ 是从 $\omega$ 到 $2$ 的函数，且 $g \notin M$。

*证明*：

1. **$g$ 是函数**：若 $(n, i), (n, j) \in g$，则存在 $p, q \in G$ 使得 $p(n) = i$，$q(n) = j$。由于 $G$ 是滤子，存在 $r \in G$ 使得 $r \leq p$ 且 $r \leq q$，故 $r(n) = i = j$。

2. **$g$ 定义在所有自然数上**：对每个 $n \in \omega$，集合 $D_n = \{p \in \mathbb{C} : n \in \text{dom}(p)\}$ 是稠密的。由泛型性，$G \cap D_n \neq \emptyset$。

3. **$g \notin M$**：对任何 $f \in M$，$f : \omega \to 2$，集合 $D_f = \{p \in \mathbb{C} : \exists n \in \text{dom}(p), \, p(n) \neq f(n)\}$ 是稠密的。因此 $g \neq f$。 $\square$

### 推论 5.3

$M[g]$ 是ZFC的可数传递模型，且 $M \subsetneq M[g]$。

---

## 参考文献

1. **Cohen, P.J. (1963)**. "The independence of the Continuum Hypothesis I". *Proceedings of the National Academy of Sciences*, 50(6), 1143-1148.

2. **Cohen, P.J. (1964)**. "The independence of the Continuum Hypothesis II". *Proceedings of the National Academy of Sciences*, 51(1), 105-110.

3. **Cohen, P.J. (1966)**. *Set Theory and the Continuum Hypothesis*. W.A. Benjamin, New York.

4. **Kunen, K. (2011)**. *Set Theory*. Studies in Logic and the Foundations of Mathematics, Vol. 102. College Publications.

5. **Jech, T. (2003)**. *Set Theory* (3rd Millennium ed.). Springer Monographs in Mathematics.

6. **Shoenfield, J.R. (1971)**. "Unramified forcing". *Axiomatic Set Theory*, Proc. Sympos. Pure Math., Vol. XIII, Part I, 357-381.

---

## MSC编码

- **03E35**: 力迫与其他集合论构造的一致性结果和独立性结果
- **03E40**: 力迫的其他方面（公理、偏序集等）


## 相关链接


- [科恩主页面](../../README.md)
- [FormalMath 总索引](../../../../INDEX.md)
- [核心概念库](../../../../concept/)
