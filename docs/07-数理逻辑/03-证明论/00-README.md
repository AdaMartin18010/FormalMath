---
title: "证明论 (Proof Theory)"
msc_primary: "03F03"
msc_secondary: ['03F05', '03F30', '03F35', '03F50']
processed_at: '2026-04-05'
references:
  textbooks:
    - id: enderton_logic
      type: textbook
      title: A Mathematical Introduction to Logic
      authors:
      - Herbert B. Enderton
      publisher: Academic Press
      edition: 2nd
      year: 2001
      isbn: 978-0122384523
      msc: 03-01
      chapters: []
      url: ~
    - id: mendelson_logic
      type: textbook
      title: Introduction to Mathematical Logic
      authors:
      - Elliott Mendelson
      publisher: Chapman and Hall/CRC
      edition: 6th
      year: 2015
      isbn: 978-1482237725
      msc: 03-01
      chapters: []
      url: ~
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
      consulted_at: 2026-04-17
    - id: stacks_project
      type: database
      name: Stacks Project
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
      consulted_at: 2026-04-17
    - id: zbmath
      type: database
      name: zbMATH Open
      entry_url: "https://zbmath.org/?q=an:{zb_id}"
      consulted_at: 2026-04-17
---

# 证明论 (Proof Theory)

**最后更新**: 2026年4月5日  
**MSC分类**: 03F-XX (证明论与构造数学)

---

## 1. 引言

证明论由David Hilbert在20世纪初创立，作为其元数学计划的核心组成部分。通过分析数学证明的结构，证明论不仅揭示了逻辑系统的内在性质，还提供了构造性数学的基础。从Gentzen的切消定理到Gödel的Dialectica解释，从序数分析到证明复杂性，证明论已成为连接逻辑、计算机科学和数学基础的桥梁。

---

## 2. 证明系统

### 2.1 Hilbert系统

**定义 2.1** (Hilbert式公理系统): Hilbert系统包含：
- **公理模式**:
  - (A1) $\varphi \rightarrow (\psi \rightarrow \varphi)$
  - (A2) $(\varphi \rightarrow (\psi \rightarrow \chi)) \rightarrow ((\varphi \rightarrow \psi) \rightarrow (\varphi \rightarrow \chi))$
  - (A3) $(\neg\varphi \rightarrow \neg\psi) \rightarrow (\psi \rightarrow \varphi)$
- **推理规则**: 
  - **假言推理 (MP)**: 从 $\varphi$ 和 $\varphi \rightarrow \psi$ 推出 $\psi$

**定理 2.1** (演绎定理): $T \cup \{\varphi\} \vdash \psi$ 当且仅当 $T \vdash \varphi \rightarrow \psi$。

---

### 2.2 自然演绎

**定义 2.2** (自然演绎系统): Gentzen的自然演绎由引入规则和消去规则组成：

| 联结词 | 引入规则 | 消去规则 |
|--------|----------|----------|
| $\land$ | $\frac{\varphi \quad \psi}{\varphi \land \psi}$ ($\land$I) | $\frac{\varphi \land \psi}{\varphi}$, $\frac{\varphi \land \psi}{\psi}$ ($\land$E) |
| $\lor$ | $\frac{\varphi}{\varphi \lor \psi}$, $\frac{\psi}{\varphi \lor \psi}$ ($\lor$I) | $\frac{\varphi \lor \psi \quad \varphi \rightarrow \chi \quad \psi \rightarrow \chi}{\chi}$ ($\lor$E) |
| $\rightarrow$ | $\frac{[\varphi] \cdots \psi}{\varphi \rightarrow \psi}$ ($\rightarrow$I) | $\frac{\varphi \quad \varphi \rightarrow \psi}{\psi}$ ($\rightarrow$E) |
| $\forall$ | $\frac{\varphi(x)}{\forall x \varphi(x)}$ ($\forall$I) | $\frac{\forall x \varphi(x)}{\varphi(t)}$ ($\forall$E) |
| $\exists$ | $\frac{\varphi(t)}{\exists x \varphi(x)}$ ($\exists$I) | $\frac{\exists x \varphi(x) \quad [\varphi(y)] \cdots \psi}{\psi}$ ($\exists$E) |

---

### 2.3 矢列演算

**定义 2.3** (矢列): 矢列 (sequent) 形如 $\Gamma \Rightarrow \Delta$，其中 $\Gamma, \Delta$ 是公式有限多重集。

**定义 2.4** (LK系统): Gentzen的LK系统规则：

**结构规则**:
- 弱化: $\frac{\Gamma \Rightarrow \Delta}{\varphi, \Gamma \Rightarrow \Delta}$ (左弱化)
- 收缩: $\frac{\varphi, \varphi, \Gamma \Rightarrow \Delta}{\varphi, \Gamma \Rightarrow \Delta}$ (左收缩)
- 交换: $\frac{\Gamma, \varphi, \psi, \Gamma' \Rightarrow \Delta}{\Gamma, \psi, \varphi, \Gamma' \Rightarrow \Delta}$ (左交换)
- 切 (Cut): $\frac{\Gamma \Rightarrow \Delta, \varphi \quad \varphi, \Gamma' \Rightarrow \Delta'}{\Gamma, \Gamma' \Rightarrow \Delta, \Delta'}$

**逻辑规则**:
- 合取左: $\frac{\varphi, \psi, \Gamma \Rightarrow \Delta}{\varphi \land \psi, \Gamma \Rightarrow \Delta}$
- 合取右: $\frac{\Gamma \Rightarrow \Delta, \varphi \quad \Gamma \Rightarrow \Delta, \psi}{\Gamma \Rightarrow \Delta, \varphi \land \psi}$
- 蕴含左: $\frac{\Gamma \Rightarrow \Delta, \varphi \quad \psi, \Gamma' \Rightarrow \Delta'}{\varphi \rightarrow \psi, \Gamma, \Gamma' \Rightarrow \Delta, \Delta'}$

---

## 3. 切消定理

### 3.1 Gentzen的Haupsatz

**定理 3.1** (切消定理 / Cut-Elimination Theorem): LK中任何可证的矢列都可用无切证明来证明。

**证明概要**: 通过多重归纳，将切公式复杂度逐步降低，最终消除所有切规则。$\square$

**推论 3.1** (子公式性质): 无切证明中的每个公式都是最终矢列中公式的子公式。

**推论 3.2** (一致性): 纯逻辑LK是一致的（不能证明空矢列 $\Rightarrow$）。

**推论 3.3** (插值定理): 若 $\vdash \varphi \rightarrow \psi$，则存在插值公式 $\theta$（只含 $\varphi$ 和 $\psi$ 的公共符号）使得 $\vdash \varphi \rightarrow \theta$ 和 $\vdash \theta \rightarrow \psi$。

---

### 3.2 序数分析

**定义 3.1** (证明论序数): 理论 $T$ 的证明论序数 $|T|$ 是衡量 $T$ 证明复杂度的序数。

**定理 3.2** (Gentzen, 1936): PA（皮亚诺算术）的一致性可在PRA（原始递归算术）加上超限归纳到 $\varepsilon_0$ 来证明。

$$|\text{PA}| = \varepsilon_0 = \sup\{\omega, \omega^\omega, \omega^{\omega^\omega}, \ldots\}$$

**定义 3.2** (序数记号系统): 
- $\varepsilon_0$ 是满足 $\omega^\alpha = \alpha$ 的最小序数
- $\Gamma_0$ (Feferman-Schütte序数) 是证明论中重要的更大序数

---

## 4. 构造性数学

### 4.1 直觉主义逻辑

**定义 4.1** (BHK解释): 直觉主义逻辑的真值条件解释 (Brouwer-Heyting-Kolmogorov)：
- $\varphi \land \psi$ 的证明是 $(p, q)$，其中 $p$ 是 $\varphi$ 的证明，$q$ 是 $\psi$ 的证明
- $\varphi \lor \psi$ 的证明是 $(0, p)$（$\varphi$ 的证明）或 $(1, q)$（$\psi$ 的证明）
- $\varphi \rightarrow \psi$ 的证明是将 $\varphi$ 的证明映射为 $\psi$ 的证明的函数
- $\exists x \varphi(x)$ 的证明是 $(a, p)$，其中 $p$ 是 $\varphi(a)$ 的证明
- $\forall x \varphi(x)$ 的证明是将每个 $a$ 映射为 $\varphi(a)$ 的证明的函数

**定理 4.1**: 直觉主义命题逻辑不能用有限值真值表刻画。

---

### 4.2 可实现性

**定义 4.2** (Kleene可实现性): 数 $e$ 可实现公式 $\varphi$，记 $e \Vdash \varphi$：
- $e \Vdash A$（原子）当且仅当 $A$ 为真
- $e \Vdash \varphi \land \psi$ 当且仅当 $(e)_0 \Vdash \varphi$ 且 $(e)_1 \Vdash \psi$
- $e \Vdash \varphi \rightarrow \psi$ 当且仅当 $\forall n (n \Vdash \varphi \Rightarrow \{e\}(n) \Vdash \psi)$
- $e \Vdash \exists x \varphi(x)$ 当且仅当 $(e)_1 \Vdash \varphi((e)_0)$

**定理 4.2** (可实现性 soundness): 若 HA（Heyting算术）$\vdash \varphi$，则存在 $e$ 使得 $e \Vdash \varphi$。

---

### 4.3 Gödel的Dialectica解释

**定义 4.3** (Dialectica解释): 将公式 $\varphi$ 解释为存在公式 $\exists \bar{x} \forall \bar{y} \varphi_D(\bar{x}, \bar{y})$。

**定理 4.3** (Gödel): 若 HA $\vdash \varphi$，则在T（有限型算术）中可证 $\varphi$ 的Dialectica翻译。

---

## 5. 证明复杂性

### 5.1 证明长度

**定义 5.1** (证明长度): 证明的长度是其中公式符号的总数。

**定理 5.1** (超指数增长): 存在命题公式序列 $\varphi_n$ 使得：
- $\varphi_n$ 有长度 $O(n)$
- 任何切消后的证明长度 $\geq 2^{2^{\cdot^{\cdot^{2}}}}$（$n$ 层高）

**定理 5.2** (Haken, 1985): 鸽巢原理的反驳需要指数长度的分辨率证明。

---

## 6. 目录结构

```
docs/07-数理逻辑/03-证明论/
├── 00-README.md                    # 本文件
├── 01-证明系统.md                   # Hilbert、自然演绎、矢列演算
├── 02-切消定理.md                   # Gentzen的Haupsatz
├── 03-序数分析.md                   # 证明论序数
├── 04-构造性数学.md                 # 直觉主义逻辑
├── 05-可实现性.md                   # Kleene可实现性
├── 06-证明复杂性.md                 # 证明长度下界
└── 07-实战问题.md                   # 证明分析练习
```

---

## 7. 学习路径

### 7.1 基础路径
**命题逻辑证明** → **一阶逻辑证明** → **切消定理** → **构造性数学**

### 7.2 高级路径
- **序数分析**: 证明论序数、系统强度比较
- **构造性分析**: Bishop的构造主义数学
- **自动定理证明**: 归结原理、SMT求解器

---

## 8. 核心定理索引

| 定理 | 领域 | 贡献者 | 重要性 |
|------|------|--------|--------|
| 切消定理 | 结构证明论 | Gentzen (1934) | ⭐⭐⭐⭐⭐ |
| 演绎定理 | Hilbert系统 | Herbrand | ⭐⭐⭐⭐ |
| 序数分析 | 元数学 | Gentzen, Schütte | ⭐⭐⭐⭐ |
| 可实现性 | 构造性数学 | Kleene (1945) | ⭐⭐⭐⭐ |
| Dialectica解释 | 函数式解释 | Gödel (1958) | ⭐⭐⭐⭐ |

---

**最后更新**: 2026年4月5日  
**维护者**: FormalMath项目组  
**质量等级**: ⭐⭐⭐⭐⭐ (研究级)
