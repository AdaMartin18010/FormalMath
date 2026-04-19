---
title: 序列演算LJ与LK
msc_primary: 01
msc_secondary:
  - 01A60
  - 01A70
processed_at: '2026-04-05'
---

# 序列演算LJ与LK

**创建日期**: 2025年12月15日（深度升级：2026年4月）
**研究领域**: 根岑数学理念 - 数学内容深度分析 - 序列演算
**主题编号**: G.02.02.01 (Gentzen.数学内容深度分析.序列演算.序列演算LJ和LK)
**深度等级**: 教学级 ⭐⭐⭐⭐⭐

---

## 📋 目录

- [序列演算LJ与LK](#序列演算lj与lk)
  - [📋 目录](../../README.md)
  - [一、历史背景与设计动机](#一历史背景与设计动机)
    - [1.1 从自然演绎到序列演算](#11-从自然演绎到序列演算)
    - [1.2 根岑的双重贡献](#12-根岑的双重贡献)
  - [二、序列的基本概念](#二序列的基本概念)
    - [2.1 序列的定义](#21-序列的定义)
    - [2.2 语义解释](#22-语义解释)
    - [2.3 公理与基本结构](#23-公理与基本结构)
  - [三、LK系统：经典序列演算](#三lk系统经典序列演算)
    - [3.1 结构规则](#31-结构规则)
    - [3.2 逻辑规则（命题逻辑）](#32-逻辑规则命题逻辑)
      - [合取（$\\land$）](#合取land)
      - [析取（$\\lor$）](#析取lor)
      - [蕴含（$\\to$）](#蕴含to)
      - [否定（$\\neg$）](#否定neg)
    - [3.3 量词规则](#33-量词规则)
    - [3.4 LK规则总表](#34-lk规则总表)
  - [四、LJ系统：直觉主义序列演算](#四lj系统直觉主义序列演算)
    - [4.1 LJ的限制](#41-lj的限制)
    - [4.2 LJ规则调整](#42-lj规则调整)
  - [五、切割消除定理（Hauptsatz）](#五切割消除定理hauptsatz)
    - [5.1 切割规则](#51-切割规则)
    - [5.2 Hauptsatz陈述](#52-hauptsatz陈述)
    - [5.3 直观证明思路](#53-直观证明思路)
  - [六、推导示例](#六推导示例)
    - [6.1 蕴含分配律](#61-蕴含分配律)
    - [6.2 排中律在LK中的推导](#62-排中律在lk中的推导)
  - [七、子公式性质与应用](#七子公式性质与应用)
    - [7.1 子公式性质](#71-子公式性质)
    - [7.2 一致性证明](#72-一致性证明)
  - [八、总结](#八总结)
  - [参考资源](#参考资源)
    - [原始文献](#原始文献)
    - [经典教材](#经典教材)
    - [在线资源](#在线资源)

---

## 一、历史背景与设计动机

### 1.1 从自然演绎到序列演算

根岑在1934-1935年的博士论文中不仅提出了自然演绎（NJ/NK），还提出了**序列演算**（Sequent Calculus）。为什么要设计两种系统？

**自然演绎的问题**：

| 问题 | 说明 |
|------|------|
| 非局部性 | 假设的引入和取消使得证明结构复杂 |
| 难以分析 | 证明的元理论性质难以研究 |
| 不对称性 | 前提和结论的处理不对称 |

**序列演算的优势**：

- **对称性**：前提（antecedent）和结论（succedent）对称处理
- **局部性**：每条规则只涉及待证公式
- **可分析性**：证明结构清晰，便于元理论研究
- **机械性**：更适合自动证明搜索

### 1.2 根岑的双重贡献

根岑提出序列演算的直接动机是证明**切割消除定理**（Hauptsatz）。在自然演绎中，证明归一化（消除"迂回"）相当复杂；而在序列演算中，切割消除具有清晰的结构。

| 特征 | 自然演绎 | 序列演算 |
|------|----------|----------|
| 核心概念 | 假设与推导 | 序列（sequent） |
| 证明形式 | 树形，节点为公式 | 树形，节点为序列 |
| 主要定理 | 证明归一化 | 切割消除 |
| 适用场景 | 教学、类型论 | 证明论分析、自动推理 |

---

## 二、序列的基本概念

### 2.1 序列的定义

**定义**（序列，Sequent）：

一个**序列**是形如

$$\Gamma \vdash \Delta$$

的表达式，其中：

- $\Gamma = A_1, A_2, \ldots, A_n$ 是**前件**（antecedent，左侧）
- $\Delta = B_1, B_2, \ldots, B_m$ 是**后件**（succedent，右侧）
- 两者都是公式的有限多重集（multiset，顺序不重要，重复计数）

### 2.2 语义解释

**经典解释**：

$$\Gamma \vdash \Delta \quad \text{表示} \quad \bigwedge \Gamma \to \bigvee \Delta$$

即：如果 $\Gamma$ 中所有公式为真，则 $\Delta$ 中至少一个公式为真。

**直觉主义解释**（LJ系统）：

$$\Gamma \vdash B \quad \text{表示} \quad \bigwedge \Gamma \to B$$

后件只能有一个公式（或为空表示矛盾）。

### 2.3 公理与基本结构

**公理**（Identity Axiom）：

$$A \vdash A$$

**空序列**：

- $\vdash A$ 表示 "$A$ 是定理"（无需假设）
- $\Gamma \vdash$（空后件）表示 "$\Gamma$ 是矛盾的"

---

## 三、LK系统：经典序列演算

LK（*Logistische Klassische*）是根岑为经典逻辑设计的序列演算系统。

### 3.1 结构规则

结构规则不引入逻辑连接词，只操作序列的结构。

**弱化规则**（Weakening，W）：

$$\frac{\Gamma \vdash \Delta}{\Gamma, A \vdash \Delta}(\text{WL}) \quad \frac{\Gamma \vdash \Delta}{\Gamma \vdash A, \Delta}(\text{WR})$$

**收缩规则**（Contraction，C）：

$$\frac{\Gamma, A, A \vdash \Delta}{\Gamma, A \vdash \Delta}(\text{CL}) \quad \frac{\Gamma \vdash A, A, \Delta}{\Gamma \vdash A, \Delta}(\text{CR})$$

**交换规则**（Exchange，E）：

$$\frac{\Gamma_1, A, B, \Gamma_2 \vdash \Delta}{\Gamma_1, B, A, \Gamma_2 \vdash \Delta}(\text{EL}) \quad \frac{\Gamma \vdash \Delta_1, A, B, \Delta_2}{\Gamma \vdash \Delta_1, B, A, \Delta_2}(\text{ER})$$

*注*：在多重集表示中，交换规则是隐含的（自动满足）。

**切割规则**（Cut，见后文）：

$$\frac{\Gamma \vdash A, \Delta \quad \Gamma', A \vdash \Delta'}{\Gamma, \Gamma' \vdash \Delta, \Delta'}$$

### 3.2 逻辑规则（命题逻辑）

逻辑规则分为**左规则**（在前提中引入连接词）和**右规则**（在结论中引入连接词）。

#### 合取（$\land$）

$$\frac{\Gamma, A, B \vdash \Delta}{\Gamma, A \land B \vdash \Delta}(\land\text{L}) \quad \frac{\Gamma \vdash A, \Delta \quad \Gamma \vdash B, \Delta}{\Gamma \vdash A \land B, \Delta}(\land\text{R})$$

#### 析取（$\lor$）

$$\frac{\Gamma, A \vdash \Delta \quad \Gamma, B \vdash \Delta}{\Gamma, A \lor B \vdash \Delta}(\lor\text{L}) \quad \frac{\Gamma \vdash A, B, \Delta}{\Gamma \vdash A \lor B, \Delta}(\lor\text{R})$$

#### 蕴含（$\to$）

$$\frac{\Gamma \vdash A, \Delta \quad \Gamma, B \vdash \Delta}{\Gamma, A \to B \vdash \Delta}(\to\text{L}) \quad \frac{\Gamma, A \vdash B, \Delta}{\Gamma \vdash A \to B, \Delta}(\to\text{R})$$

#### 否定（$\neg$）

$$\frac{\Gamma \vdash A, \Delta}{\Gamma, \neg A \vdash \Delta}(\neg\text{L}) \quad \frac{\Gamma, A \vdash \Delta}{\Gamma \vdash \neg A, \Delta}(\neg\text{R})$$

### 3.3 量词规则

**全称量词**（$\forall$）：

$$\frac{\Gamma, A(t) \vdash \Delta}{\Gamma, \forall x A(x) \vdash \Delta}(\forall\text{L}) \quad \frac{\Gamma \vdash A(y), \Delta}{\Gamma \vdash \forall x A(x), \Delta}(\forall\text{R})$$

条件（$\forall$R）：$y$ 不在 $\Gamma, \Delta$ 中自由出现（Eigenvariable条件）。

**存在量词**（$\exists$）：

$$\frac{\Gamma, A(y) \vdash \Delta}{\Gamma, \exists x A(x) \vdash \Delta}(\exists\text{L}) \quad \frac{\Gamma \vdash A(t), \Delta}{\Gamma \vdash \exists x A(x), \Delta}(\exists\text{R})$$

条件（$\exists$L）：$y$ 不在 $\Gamma, \Delta$ 中自由出现。

### 3.4 LK规则总表

| 连接词 | 左规则 | 右规则 |
|--------|--------|--------|
| $\land$ | $\frac{\Gamma, A, B \vdash \Delta}{\Gamma, A \land B \vdash \Delta}$ | $\frac{\Gamma \vdash A, \Delta \quad \Gamma \vdash B, \Delta}{\Gamma \vdash A \land B, \Delta}$ |
| $\lor$ | $\frac{\Gamma, A \vdash \Delta \quad \Gamma, B \vdash \Delta}{\Gamma, A \lor B \vdash \Delta}$ | $\frac{\Gamma \vdash A, B, \Delta}{\Gamma \vdash A \lor B, \Delta}$ |
| $\to$ | $\frac{\Gamma \vdash A, \Delta \quad \Gamma, B \vdash \Delta}{\Gamma, A \to B \vdash \Delta}$ | $\frac{\Gamma, A \vdash B, \Delta}{\Gamma \vdash A \to B, \Delta}$ |
| $\neg$ | $\frac{\Gamma \vdash A, \Delta}{\Gamma, \neg A \vdash \Delta}$ | $\frac{\Gamma, A \vdash \Delta}{\Gamma \vdash \neg A, \Delta}$ |
| $\forall$ | $\frac{\Gamma, A(t) \vdash \Delta}{\Gamma, \forall x A(x) \vdash \Delta}$ | $\frac{\Gamma \vdash A(y), \Delta}{\Gamma \vdash \forall x A(x), \Delta}^*$ |
| $\exists$ | $\frac{\Gamma, A(y) \vdash \Delta}{\Gamma, \exists x A(x) \vdash \Delta}^*$ | $\frac{\Gamma \vdash A(t), \Delta}{\Gamma \vdash \exists x A(x), \Delta}$ |

*注：* 表示Eigenvariable条件。

---

## 四、LJ系统：直觉主义序列演算

### 4.1 LJ的限制

LJ（*Logistische Intuitionistische*）是直觉主义逻辑的序列演算。其核心限制是：

**LJ序列形式**：$\Gamma \vdash C$ 或 $\Gamma \vdash$

即：**后件最多只能有一个公式**（或为空）。

### 4.2 LJ规则调整

由于后件只能有一个公式，以下LK规则需要修改：

| 规则 | LK形式 | LJ形式 |
|------|--------|--------|
| $\land$R | $\frac{\Gamma \vdash A, \Delta \quad \Gamma \vdash B, \Delta}{\Gamma \vdash A \land B, \Delta}$ | $\frac{\Gamma \vdash A \quad \Gamma \vdash B}{\Gamma \vdash A \land B}$ |
| $\lor$R | $\frac{\Gamma \vdash A, B, \Delta}{\Gamma \vdash A \lor B, \Delta}$ | $\frac{\Gamma \vdash A}{\Gamma \vdash A \lor B}$ 或 $\frac{\Gamma \vdash B}{\Gamma \vdash A \lor B}$ |
| $\to$R | $\frac{\Gamma, A \vdash B, \Delta}{\Gamma \vdash A \to B, \Delta}$ | $\frac{\Gamma, A \vdash B}{\Gamma \vdash A \to B}$ |
| $\neg$R | $\frac{\Gamma, A \vdash \Delta}{\Gamma \vdash \neg A, \Delta}$ | $\frac{\Gamma, A \vdash}{\Gamma \vdash \neg A}$ |

**重要差异**：

- LK中，$A \lor B$ 的右规则允许同时保留 $A$ 和 $B$ 作为可能结论
- LJ中，必须在应用规则前决定是推出 $A$ 还是推出 $B$
- 这反映了直觉主义逻辑的**构造性**：证明必须明确构造出哪个析取支成立

---

## 五、切割消除定理（Hauptsatz）

### 5.1 切割规则

**切割规则**（Cut Rule）：

$$\frac{\Gamma \vdash A, \Delta \quad \Gamma', A \vdash \Delta'}{\Gamma, \Gamma' \vdash \Delta, \Delta'}(\text{Cut})$$

**直观意义**：如果我们能从 $\Gamma$ 推出 $A$（或 $\Delta$），且从 $\Gamma'$ 和 $A$ 推出 $\Delta'$，则从 $\Gamma$ 和 $\Gamma'$ 可以推出 $\Delta$ 或 $\Delta'$。

切割规则类似于**三段论**：使用中间结论 $A$ 连接两个推导。

### 5.2 Hauptsatz陈述

**定理**（切割消除定理，Hauptsatz，根岑1935）：

> 在LK（或LJ）中，任何使用切割规则的证明都可以转化为**不使用切割规则**的证明。

形式化表述：

$$\text{如果 } \Gamma \vdash_{LK+Cut} \Delta, \text{ 则 } \Gamma \vdash_{LK} \Delta$$

**注意**：

- 无切证明可能**指数级更长**
- 但具有更好的结构性质（子公式性质）

### 5.3 直观证明思路

切割消除的证明使用**双重归纳**：

**定义复杂度**：

- **秩**（rank）：切公式 $A$ 的复杂度（连接词数量）
- **度**（degree）：切割规则在证明树中的高度

**证明策略**：

1. **基本情况**：切公式是原子公式——直接消除

2. **归纳步骤**：将切割"向上推"，降低复杂度

   关键情况示例（主公式情况）：

   假设最后一步分别是 $\land$R 和 $\land$L：

   $$\frac{\vdots \\ \Gamma \vdash A \quad \Gamma \vdash B}{\Gamma \vdash A \land B}(\land\text{R}) \quad \frac{\vdots \\ \Gamma', A, B \vdash \Delta'}{\Gamma', A \land B \vdash \Delta'}(\land\text{L})$$

   转换为对 $A$ 和 $B$ 的两次切割（复杂度更低）。

3. **重复直到**所有切割都被消除

---

## 六、推导示例

### 6.1 蕴含分配律

**定理**：$(A \to (B \to C)) \to ((A \to B) \to (A \to C))$

**LK证明**（目标：$\vdash (A \to (B \to C)) \to ((A \to B) \to (A \to C))$）：

$$\frac{\frac{\frac{\frac{A \vdash A}{A \to (B \to C), A \vdash B \to C}(\to\text{L}) \quad \frac{B \vdash B}{B \to C, B \vdash C}(\to\text{L})}{A \to (B \to C), A, B \vdash C}(\text{Cut})}{A \to (B \to C), A \vdash B \to C}(\to\text{R}) \quad \frac{\frac{A \vdash A}{A \to B, A \vdash B}(\to\text{L})}{A \to B, A \vdash B}(\to\text{R})}{\frac{A \to (B \to C), A \to B, A \vdash C}{A \to (B \to C), A \to B \vdash A \to C}(\to\text{R})}(\to\text{L})}{\frac{A \to (B \to C) \vdash (A \to B) \to (A \to C)}{\vdash (A \to (B \to C)) \to ((A \to B) \to (A \to C))}(\to\text{R})}(\to\text{R})$$

### 6.2 排中律在LK中的推导

**定理**：$\vdash A \lor \neg A$

**LK证明**（无切）：

$$\frac{\frac{A \vdash A}{\vdash A, \neg A}(\neg\text{R})}{\vdash A \lor \neg A}(\lor\text{R})$$

**LJ中不可证**：

在LJ中，$\lor$R规则要求：

$$\frac{\Gamma \vdash A}{\Gamma \vdash A \lor B} \quad \text{或} \quad \frac{\Gamma \vdash B}{\Gamma \vdash A \lor B}$$

要证 $A \lor \neg A$，必须先证 $A$ 或先证 $\neg A$，这无法从空前提做到。

---

## 七、子公式性质与应用

### 7.1 子公式性质

**定理**（子公式性质）：

在无切证明中，出现的所有公式都是**最终结论的子公式**。

**定义**：公式 $A$ 是 $B$ 的**子公式**如果：

- $A = B$，或
- $A$ 是 $B$ 的真子公式（通过拆连接词得到）

**意义**：

- 证明是"局部的"
- 不需要引入"外部"公式
- 证明搜索空间有限

### 7.2 一致性证明

**定理**：PA（皮亚诺算术）的一致性可以通过序列演算+切割消除证明。

**证明思路**（根岑1936）：

1. 假设PA不一致，则存在证明 $0 = 1$
2. 转化为序列演算证明
3. 切割消除，得到无切证明
4. 但 $0 = 1$ 是原子公式，无子公式
5. 无切证明只能使用公理，而 $0 = 1$ 不是公理
6. 矛盾！

---

## 八、总结

根岑的序列演算系统（LJ/LK）是证明论的里程碑：

1. **对称设计**：前提与结论对称处理，结构清晰
2. **切割消除**：Hauptsatz提供了强大的元理论工具
3. **子公式性质**：使证明搜索和一致性证明成为可能
4. **经典与直觉主义统一**：LK和LJ展示了两种逻辑的本质差异

序列演算至今仍是：

- 自动定理证明的基础
- 逻辑编程（Prolog）的理论基础
- 现代类型论和线性逻辑的起点

---

## 参考资源

### 原始文献

- Gentzen, G. (1934/1935). "Untersuchungen über das logische Schließen". *Mathematische Zeitschrift*, 39:176-210, 405-431.
- Gentzen, G. (1936). "Die Widerspruchsfreiheit der reinen Zahlentheorie". *Mathematische Annalen*, 112:493-565.

### 经典教材

- Troelstra, A.S. & Schwichtenberg, H. (2000). *Basic Proof Theory* (2nd ed.). Cambridge University Press.
- Takeuti, G. (1987). *Proof Theory* (2nd ed.). North-Holland.

### 在线资源

- Stanford Encyclopedia of Philosophy: "Proof Theory" (https://plato.stanford.edu/)
- Stanford Encyclopedia of Philosophy: "Gentzen's Proof of the Consistency of Arithmetic"

---

**文档状态**: ✅ 教学级深度完成
**字数**: 约4,500字
**数学公式数**: 40+
**证明示例数**: 3个
**最后更新**: 2026年4月3日
