---
title: Chomsky 层次的定义
msc_primary: 01
msc_secondary:
  - 01A60
  - 01A65
  - 01A70
processed_at: '2026-04-05'
---

# Chomsky 层次的定义

**数学分类**: 68Q15 (复杂性层次), 68Q42 (语法与文法), 68Q45 (形式语言)
**历史背景**: 1956-1963年乔姆斯基的语言学革命
**参考来源**: Chomsky (1956, 1959), Chomsky & Schützenberger (1963)

---

## 1. 引言

1956年至1963年间，诺姆·乔姆斯基（Noam Chomsky）和合作者马塞尔·保罗·舒岑贝格（Marcel-Paul Schützenberger）建立了形式语言理论的完整体系。其中最重要的贡献是**Chomsky 层次**（Chomsky Hierarchy）——一个根据生成能力对形式语言进行分类的四层结构。

Chomsky 层次不仅深刻影响了语言学，更成为计算机科学的核心理论基础：

- **编译器设计**：不同语法分析技术对应层次中的不同类别
- **计算理论**：语言类别与计算模型（自动机）存在精确对应
- **复杂性理论**：层次关系揭示了计算问题的本质难度

---

## 2. 文法的形式化定义

### 2.1 短语结构文法

**定义 2.1**（短语结构文法，Phrase-Structure Grammar）
> 一个**文法** $G$ 是四元组 $G = (V, \Sigma, R, S)$，其中：
>
> - $V$：非终结符（变量）的有限集合
> - $\Sigma$：终结符的有限集合，$V \cap \Sigma = \emptyset$
> - $R \subseteq (V \cup \Sigma)^* \times (V \cup \Sigma)^*$：产生式规则的有限集合
> - $S \in V$：开始符号（公理）

**记号约定**：

- 产生式 $(\alpha, \beta) \in R$ 记作 $\alpha \to \beta$
- $V \cup \Sigma$ 上的元素称为**符号**
- $(V \cup \Sigma)^*$ 上的元素称为**句型**（sentential form）

### 2.2 推导关系

**定义 2.2**（直接推导）
> 设 $G = (V, \Sigma, R, S)$ 为文法。若存在产生式 $\alpha \to \beta \in R$ 和字符串 $\gamma, \delta \in (V \cup \Sigma)^*$ 使得：
> $$u = \gamma\alpha\delta, \quad v = \gamma\beta\delta$$
> 则称 $u$ **直接推导出** $v$，记作 $u \Rightarrow_G v$ 或简写为 $u \Rightarrow v$。

**定义 2.3**（推导）
> **推导** $\Rightarrow^*$ 是 $\Rightarrow$ 的自反传递闭包：$u \Rightarrow^* v$ 当且仅当存在 $k \geq 0$ 和序列 $u = u_0 \Rightarrow u_1 \Rightarrow \cdots \Rightarrow u_k = v$。

**定义 2.4**（生成的语言）
> 文法 $G$ **生成**的语言定义为：
> $$L(G) = \{w \in \Sigma^* \mid S \Rightarrow^* w\}$$

---

## 3. Chomsky 层次的四类文法

### 3.1 Type 0：无限制文法

**定义 3.1**（无限制文法，Unrestricted Grammar / Type 0）
> **无限制文法**对产生式 $R$ 没有任何限制：任意 $\alpha \to \beta$ 其中 $\alpha \neq \varepsilon$。

**对应自动机**：图灵机（Turing Machine）

**定理 3.1**（Chomsky, 1959）
> 语言 $L$ 被某个无限制文法生成 **当且仅当** $L$ 是**递归可枚举的**（Recursively Enumerable, RE）。

*证明思路*：

- $(\Rightarrow)$：给定文法 $G$，构造非确定型图灵机模拟所有可能的推导
- $(\Leftarrow)$：给定图灵机 $M$，构造文法模拟 $M$ 的计算历史

---

### 3.2 Type 1：上下文有关文法

**定义 3.2**（上下文有关文法，Context-Sensitive Grammar / Type 1 / CSG）
> 产生式形如 $\alpha A \beta \to \alpha \gamma \beta$，其中：
>
> - $A \in V$（单个非终结符）
> - $\alpha, \beta \in (V \cup \Sigma)^*$（上下文）
> - $\gamma \in (V \cup \Sigma)^+$, $\gamma \neq \varepsilon$（非空替换）
>
> 或允许 $S \to \varepsilon$，但此时 $S$ 不能出现在任何产生式右侧。

**关键特性**：产生式右侧长度 $
geq$ 左侧长度（单调性）

**对应自动机**：线性有界自动机（Linear Bounded Automaton, LBA）

**例子 3.1**:
> 语言 $L = \{a^n b^n c^n \mid n \geq 1\}$ 是上下文有关的但非上下文无关的。
>
> 文法：
>
> ```
> S  → aSBC | aBC
> CB → BC
> aB → ab
> bB → bb
> bC → bc
> cC → cc
> ```

---

### 3.3 Type 2：上下文无关文法

**定义 3.3**（上下文无关文法，Context-Free Grammar / Type 2 / CFG）
> 每个产生式形如 $A \to \alpha$，其中：
>
> - $A \in V$（单个非终结符）
> - $\alpha \in (V \cup \Sigma)^*$（任意句型）

**关键特性**：非终结符的替换**不依赖上下文**

**对应自动机**：下推自动机（Pushdown Automaton, PDA）

**定理 3.2**（Chomsky, 1959）
> 语言 $L$ 被某个上下文无关文法生成 **当且仅当** 它被某个下推自动机接受。

**例子 3.2**:
> 平衡括号语言：
>
> ```
> S → (S) | SS | ε
> ```

**Chomsky 范式（CNF）**:
> 任何 CFG 可转化为等价文法，其产生式只有两种形式：
>
> - $A \to BC$（$B, C$ 为非终结符）
> - $A \to a$（$a$ 为终结符）

---

### 3.4 Type 3：正则文法

**定义 3.4**（正则文法，Regular Grammar / Type 3）
> **右线性文法**：产生式形如 $A \to aB$ 或 $A \to a$ 或 $A \to \varepsilon$
>
> **左线性文法**：产生式形如 $A \to Ba$ 或 $A \to a$ 或 $A \to \varepsilon$

**关键特性**：产生式右侧至多一个非终结符，且若存在则在最右（或最左）

**对应自动机**：有限自动机（Finite Automaton, FA）

**定理 3.3**（Kleene, 1956; Rabin & Scott, 1959）
> 以下等价：
>
> 1. $L$ 被某个正则文法生成
> 2. $L$ 被某个 DFA 接受
> 3. $L$ 被某个 NFA 接受
> 4. $L$ 被某个正则表达式表示

**例子 3.3**:
> 以 01 结尾的二进制串：
>
> ```
> S → 0S | 1S | 0A
> A → 1B
> B → ε | 0S | 1S
> ```

---

## 4. 层次包含关系

### 4.1 层次结构

**定理 4.1**（Chomsky 层次包含关系）
> $$\mathcal{L}_3 \subsetneq \mathcal{L}_2 \subsetneq \mathcal{L}_1 \subsetneq \mathcal{L}_0$$
>
> 其中 $\mathcal{L}_i$ 表示 Type $i$ 语言类。

*证明思路*：

**$\mathcal{L}_3 \subseteq \mathcal{L}_2$**：
> 每个正则产生式 $A \to aB$ 也是上下文无关的（满足 $A \to \alpha$ 形式）。

**$\mathcal{L}_2 \subseteq \mathcal{L}_1$**：
> 上下文无关产生式 $A \to \alpha$ 可视为 $\varepsilon A \varepsilon \to \varepsilon \alpha \varepsilon$，满足上下文有关形式（在空上下文下）。

**$\mathcal{L}_1 \subseteq \mathcal{L}_0$**：
> 由定义直接可得。

**严格性证明**：

**$\mathcal{L}_3 \neq \mathcal{L}_2$**：
> 语言 $\{a^n b^n \mid n \geq 0\}$ 是上下文无关的但非正则的（用泵引理）。

**$\mathcal{L}_2 \neq \mathcal{L}_1$**：
> 语言 $\{a^n b^n c^n \mid n \geq 0\}$ 是上下文有关的但非上下文无关的。

**$\mathcal{L}_1 \neq \mathcal{L}_0$**：
> 存在递归可枚举但非上下文有关的语言（利用可判定性差异）。

---

## 5. 泵引理（Pumping Lemmas）

泵引理提供了证明语言**不属于**某类的方法。

### 5.1 正则语言的泵引理

**定理 5.1**（正则语言泵引理）
> 若 $L$ 是正则语言，则存在泵长度 $p > 0$ 使得：对任意 $w \in L$ 且 $|w| \geq p$，存在分解 $w = xyz$ 满足：
>
> 1. $|xy| \leq p$
> 2. $|y| > 0$
> 3. 对所有 $i \geq 0$，$xy^i z \in L$

*证明思路*：基于 DFA 的鸽巢原理。DFA 有有限状态，长字符串必然重复经过某状态，形成循环。

**应用**：证明 $L = \{a^n b^n \mid n \geq 0\}$ 非正则。

### 5.2 上下文无关语言的泵引理

**定理 5.2**（CFG 泵引理）
> 若 $L$ 是 CFL，则存在泵长度 $p > 0$ 使得：对任意 $w \in L$ 且 $|w| \geq p$，存在分解 $w = uvxyz$ 满足：
>
> 1. $|vxy| \leq p$
> 2. $|vy| > 0$
> 3. 对所有 $i \geq 0$，$uv^i xy^i z \in L$

*证明思路*：基于语法分析树的鸽巢原理。长句子的分析树必含重复的非终结符节点，形成可泵结构。

**应用**：证明 $L = \{a^n b^n c^n \mid n \geq 0\}$ 非上下文无关。

---

## 6. 总结与对应关系

| 层次 | 名称 | 文法形式 | 自动机 | 典型问题 | 计算能力 |
|-----|------|---------|--------|---------|---------|
| Type 3 | 正则 | $A \to aB \| a$ | 有限自动机 | 词法分析 | 最低 |
| Type 2 | 上下文无关 | $A \to \alpha$ | 下推自动机 | 语法分析 | 中等 |
| Type 1 | 上下文有关 | $\alpha A \beta \to \alpha \gamma \beta$ | 线性有界自动机 | 复杂模式 | 高 |
| Type 0 | 无限制 | $\alpha \to \beta$ | 图灵机 | 通用计算 | 最高 |

**层次关系的深刻含义**：

1. **表达能力**与**计算复杂度**呈反比
2. **识别难度**随层次上升而增加
3. **实际应用**中通常使用受限的子类（如确定性 CFL）

Chomsky 层次不仅是一个分类体系，更揭示了**语言、计算和复杂性之间的深刻联系**。

---

## 参考文献

1. Chomsky, N. (1956). "Three models for the description of language." *IRE Trans. on Information Theory*, 2(3), 113-124.
2. Chomsky, N. (1959). "On certain formal properties of grammars." *Information and Control*, 2(2), 137-167.
3. Chomsky, N., & Schützenberger, M. P. (1963). "The algebraic theory of context-free languages." In *Computer Programming and Formal Systems* (pp. 118-161). North-Holland.
4. Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). *Introduction to Automata Theory, Languages, and Computation* (3rd ed.). Pearson.
5. Sipser, M. (2012). *Introduction to the Theory of Computation* (3rd ed.). Cengage Learning.


## 相关链接

- [08-计算数学](../../../../docs/08-计算数学/)

### 相关概念

- [层](../../../../concept/核心概念/22-层.md)

- [乔姆斯基主页面](../../README.md)
- [FormalMath 总索引](../../../../INDEX.md)
- [核心概念库](../../../../concept/)
