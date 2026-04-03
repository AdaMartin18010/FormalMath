---
msc_primary: "01A99"
---

# Forcing与独立性证明

## 目录

- [Forcing与独立性证明](#forcing与独立性证明)
  - [目录](#目录)
  - [可构造宇宙回顾](#可构造宇宙回顾)
    - [1.1 哥德尔的构造性公理](#11-哥德尔的构造性公理)
  - [力迫扩展模型的构造](#力迫扩展模型的构造)
    - [2.1 从基础模型出发](#21-从基础模型出发)
    - [2.2 构造 $M\[G\]$](#22-构造-mg)
  - [独立性证明的核心框架](#独立性证明的核心框架)
    - [3.1 独立性证明的标准策略](#31-独立性证明的标准策略)
    - [3.2 Cohen的突破性洞见](#32-cohen的突破性洞见)
  - [ZFC + ¬CH的模型构造](#zfc--ch的模型构造)
    - [4.1 Cohen力迫](#41-cohen力迫)
    - [4.2 独立性证明](#42-独立性证明)
    - [4.3 完整独立性结果](#43-完整独立性结果)
  - [可数链条件与基数保持](#可数链条件与基数保持)
    - [5.1 ccc的正式定义](#51-ccc的正式定义)
    - [5.2 ccc的基数保持性质](#52-ccc的基数保持性质)
    - [5.3 ccc在Cohen力迫中的应用](#53-ccc在cohen力迫中的应用)
  - [力迫方法的威力](#力迫方法的威力)
    - [6.1 力迫的普适性](#61-力迫的普适性)
    - [6.2 力迫与绝对性](#62-力迫与绝对性)
    - [6.3 现代视角](#63-现代视角)
  - [参考文献](#参考文献)
  - [MSC编码](#msc编码)

---

## 可构造宇宙回顾

### 1.1 哥德尔的构造性公理

1938年，Kurt Gödel证明了连续统假设与ZFC的相容性。他的方法是通过构造一个ZFC的最小内模型——**可构造宇宙 $L$**。

**定义（可构造层级）**：递归定义 $L_\alpha$：

- $L_0 = \emptyset$
- $L_{\alpha+1} = \text{Def}(L_\alpha)$（$L_\alpha$ 的可定义子集）
- $L_\lambda = \bigcup_{\alpha < \lambda} L_\alpha$（极限序数）

可构造宇宙 $L = \bigcup_{\alpha \in \text{Ord}} L_\alpha$。

**定理（Gödel）**：$L \models \text{ZFC} + \text{V} = \text{L} + \text{GCH}$。

这意味着GCH（因此CH）在ZFC中不能被反驳。要证明CH独立于ZFC，我们需要构造一个ZFC + ¬CH的模型。

---

## 力迫扩展模型的构造

### 2.1 从基础模型出发

**设定**：设 $M$ 是ZFC的可数传递模型（由反射定理和Löwenheim-Skolem定理保证存在）。设 $\mathbb{P} \in M$ 是偏序集。

### 2.2 构造 $M[G]$

给定 $M$-泛型滤子 $G \subseteq P$，定义：

$$M[G] = \{\text{val}_G(\tau) : \tau \in M^\mathbb{P}\}$$

其中 $M^\mathbb{P} = M \cap \text{Name}^\mathbb{P}$ 是 $M$ 中的 $\mathbb{P}$-名称。

**定理 2.1**：$M[G]$ 是ZFC的可数传递模型，且 $M \subseteq M[G]$，$G \in M[G]$。

*证明要点*：

- **传递性**：若 $x \in \text{val}_G(\tau)$，则存在 $(\sigma, p) \in \tau$，$p \in G$ 使得 $x = \text{val}_G(\sigma)$。由归纳假设 $x \in M[G]$。
- **ZFC公理**：每个ZFC公理在 $M[G]$ 中的验证都对应 $M$ 中力迫关系的验证。例如：
  - **配对公理**：对 $\text{val}_G(\sigma), \text{val}_G(\tau)$，构造名称 $\{ (\sigma, 1_\mathbb{P}), (\tau, 1_\mathbb{P}) \}$
  - **幂集公理**：关键是证明 $M[G]$ 中 $x$ 的子集都可以由 $M$ 中的名称表示
  - **替换公理**：利用力迫关系的可定义性

---

## 独立性证明的核心框架

### 3.1 独立性证明的标准策略

要证明命题 $\varphi$ 独立于ZFC，需要：

1. **一致性证明**：构造 $M_1 \models \text{ZFC} + \varphi$
2. **独立性证明**：构造 $M_2 \models \text{ZFC} + \neg\varphi$

由哥德尔完备性定理，这证明了 $\text{ZFC} \not\vdash \varphi$ 且 $\text{ZFC} \not\vdash \neg\varphi$。

### 3.2 Cohen的突破性洞见

Cohen的关键贡献是认识到：**通过精心选择偏序集 $\mathbb{P}$，我们可以控制 $M[G]$ 中特定命题的真值**。

**核心原则**：

- 如果 $\mathbb{P}$ 添加足够多的新实数，则 $M[G] \models \neg\text{CH}$
- 如果 $\mathbb{P}$ 保持所有基数，则 $M[G] \models \text{CH}$ 的真值与 $M$ 中相同

---

## ZFC + ¬CH的模型构造

### 4.1 Cohen力迫

Cohen证明CH独立性的原始构造：

**定义（Cohen力迫）**：
$$\text{Add}(\omega, \omega_2^M) = \{p : p \text{ 是函数，} |p| < \omega, \, \text{dom}(p) \subseteq \omega_2^M \times \omega, \, \text{ran}(p) \subseteq 2\}$$

序关系：$p \leq q$ 当且仅当 $p \supseteq q$。

**直观理解**：我们同时添加 $\omega_2^M$ 个Cohen实数（从 $M$ 的角度看，$\omega_2^M$ 是第二个不可数基数）。

### 4.2 独立性证明

**定理 4.1（Cohen, 1963）**：设 $M \models \text{ZFC} + \text{CH}$，$G$ 是 $M$-泛型滤子。则 $M[G] \models \text{ZFC} + \neg\text{CH}$。

*证明*：

**步骤1：定义泛型实数**

对每个 $\alpha < \omega_2^M$，定义：
$$c_\alpha = \{(n, i) : \exists p \in G, \, p(\alpha, n) = i\}$$

由 $G$ 的泛型性，每个 $c_\alpha : \omega \to 2$ 是良定义的函数。

**步骤2：证明 $c_\alpha$ 互不相同**

对 $\alpha \neq \beta$，集合：
$$D_{\alpha,\beta} = \{p \in \mathbb{P} : \exists n, \, p(\alpha, n) \neq p(\beta, n)\}$$

是稠密的（因为任何条件都可以扩展到区分 $c_\alpha$ 和 $c_\beta$ 的定义域）。因此 $c_\alpha \neq c_\beta$。

**步骤3：基数保持**

**引理**：$\mathbb{P}$ 满足**可数链条件（ccc）**：任何反链（两两不相容的元素集合）都是可数的。

*证明引理*：由 $\Delta$-系统引理，任何不可数子族都有大小为 $\omega_1$ 的 $\Delta$-子系统。在Cohen力迫中，有限函数的任何不可数族都有相容的元素。$\square$

**步骤4：应用ccc引理**

**定理（ccc保持基数）**：如果 $\mathbb{P}$ 满足ccc，则 $\mathbb{P}$ 保持所有基数，即对任何基数 $\kappa \in M$，$\kappa$ 在 $M[G]$ 中仍是基数。

因此：

- $\omega_2^M = \omega_2^{M[G]}$
- $M[G]$ 中有至少 $\omega_2^{M[G]}$ 个不同的实数
- 所以 $M[G] \models 2^{\aleph_0} \geq \aleph_2 > \aleph_1$，即 $M[G] \models \neg\text{CH}$

### 4.3 完整独立性结果

**定理 4.2**：CH独立于ZFC。

*证明*：

- 由哥德尔：$\text{Con}(\text{ZFC}) \Rightarrow \text{Con}(\text{ZFC} + \text{CH})$（通过 $L$）
- 由Cohen：$\text{Con}(\text{ZFC}) \Rightarrow \text{Con}(\text{ZFC} + \neg\text{CH})$（通过力迫）

因此CH不能被ZFC证明或反驳。$\square$

---

## 可数链条件与基数保持

### 5.1 ccc的正式定义

**定义**：偏序集 $\mathbb{P}$ 满足**可数链条件（ccc）**，如果每个反链 $A \subseteq P$ 都是可数的。

反链是指子集 $A \subseteq P$ 满足：$\forall p, q \in A, \, p \neq q \Rightarrow p \perp q$。

### 5.2 ccc的基数保持性质

**定理 5.1**：设 $\mathbb{P}$ 满足ccc，$M$ 是ZFC的可数传递模型，$G$ 是 $M$-泛型滤子。则：

1. **保持基数**：若 $\kappa$ 在 $M$ 中是基数，则 $\kappa$ 在 $M[G]$ 中仍是基数
2. **保持共尾性**：$\text{cf}^M(\kappa) = \text{cf}^{M[G]}(\kappa)$
3. **保持不可数性**：若 $\kappa > \omega$ 在 $M$ 中不可数，则在 $M[G]$ 中也不可数

*证明概要*：关键在于证明ccc力迫不会添加新的可数序列。假设在 $M[G]$ 中 $f : \omega \to \kappa$ 是共尾函数，则存在名称 $\tau$ 使得 $\text{val}_G(\tau) = f$。由力迫定理，存在 $p \in G$ 使得 $p \Vdash "\tau \text{ 是从 } \omega \text{ 到 } \check{\kappa} \text{ 的函数}"$。

利用ccc，可以证明在 $M$ 中已存在从 $\omega$ 到 $\kappa$ 的共尾映射，矛盾。$\square$

### 5.3 ccc在Cohen力迫中的应用

**引理 5.2（$\Delta$-系统引理）**：设 $\kappa$ 是不可数正则基数，$\mathcal{A}$ 是 $\kappa$ 个有限集的族。则存在 $\mathcal{B} \subseteq \mathcal{A}$，$|\mathcal{B}| = \kappa$，使得 $\mathcal{B}$ 形成 $\Delta$-系统（即存在根 $r$ 使得对所有 $A, B \in \mathcal{B}$，$A \cap B = r$）。

**推论**：Cohen偏序集满足ccc。

---

## 力迫方法的威力

### 6.1 力迫的普适性

Cohen力迫的惊人之处在于其**普适性**：

**定理 6.1**：任何ZF（或ZFC）的传递模型 $M$ 都可以通过力迫扩展为模型 $M[G]$，使得：

1. $M[G]$ 也是ZF（或ZFC）的模型
2. $M \subseteq M[G]$ 且 $M \cap \text{Ord} = M[G] \cap \text{Ord}$
3. 可以精确控制 $M[G]$ 中各种命题的真值

### 6.2 力迫与绝对性

**定义**：集合论命题 $\varphi$ 是**绝对的**，如果在任意两个具有相同序数的传递模型之间真值相同。

**力迫与绝对性**：力迫关系揭示了哪些命题是绝对的（如算术命题），哪些不是（如CH）。

### 6.3 现代视角

现代集合论中，力迫已成为研究以下问题的核心工具：

- **大基数**：可测基数、超紧基数等的力迫性质
- **描述集合论**：决定性公理与实数正则性
- **迭代力迫**：多次扩展模型以得到更强的独立性结果
- **Woodin计划**：寻找"终极"集合论公理系统

---

## 参考文献

1. **Cohen, P.J. (1963)**. "The independence of the Continuum Hypothesis I". *PNAS*, 50(6), 1143-1148.

2. **Cohen, P.J. (1964)**. "The independence of the Continuum Hypothesis II". *PNAS*, 51(1), 105-110.

3. **Cohen, P.J. (1966)**. *Set Theory and the Continuum Hypothesis*. Benjamin.

4. **Jech, T. (2003)**. *Set Theory* (3rd Millennium ed.). Springer.

5. **Kunen, K. (2011)**. *Set Theory*. College Publications.

6. **Shoenfield, J.R. (1971)**. "Unramified forcing". *Axiomatic Set Theory*, Proc. Sympos. Pure Math., Vol. XIII, Part I, 357-381.

7. **Gödel, K. (1940)**. *The Consistency of the Continuum Hypothesis*. Annals of Mathematics Studies, No. 3. Princeton University Press.

---

## MSC编码

- **03E35**: 力迫与一致性结果和独立性结果
