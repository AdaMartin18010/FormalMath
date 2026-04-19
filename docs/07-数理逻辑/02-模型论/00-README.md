---
title: "模型论 (Model Theory)"
msc_primary: 03

  - 03C07
msc_secondary: ['03C10', '03C35', '03C45', '03C64']
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
      chapters: 
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
      chapters: 
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

# 模型论 (Model Theory)

**最后更新**: 2026年4月5日  
**MSC分类**: 03C-XX (模型论), 研究形式语言与结构之间的关系

---

## 1. 引言

模型论是数理逻辑的核心分支，研究形式语言（特别是一阶逻辑）与数学结构之间的关系。通过语义方法，模型论为代数、分析和数论提供了统一的视角。从紧致性定理到稳定性理论，从量词消去到o-极小结构，模型论已成为现代数学不可或缺的一部分。

---

## 2. 一阶语言与结构

### 2.1 一阶语言

**定义 2.1** (一阶语言): 一阶语言 $\mathcal{L}$ 包含：
- **逻辑符号**: $\neg, \land, \lor, \rightarrow, \leftrightarrow, \forall, \exists, =$
- **变元**: $v_0, v_1, v_2, \ldots$
- **非逻辑符号**: 
  - 函数符号集 $\mathcal{F} = \{f_i : i \in I\}$，各带元数 $n_i \geq 1$
  - 谓词符号集 $\mathcal{R} = \{R_j : j \in J\}$，各带元数 $m_j \geq 1$
  - 常数符号集 $\mathcal{C} = \{c_k : k \in K\}$

**定义 2.2** ($\mathcal{L}$-项): $\mathcal{L}$-项递归定义为：
1. 变元和常数符号是项
2. 若 $t_1, \ldots, t_n$ 是项，$f$ 是 $n$ 元函数符号，则 $f(t_1, \ldots, t_n)$ 是项

**定义 2.3** ($\mathcal{L}$-公式): 
- 原子公式: $t_1 = t_2$ 或 $R(t_1, \ldots, t_n)$
- 若 $\varphi, \psi$ 是公式，则 $\neg\varphi$, $\varphi \land \psi$, $\varphi \lor \psi$, $\varphi \rightarrow \psi$ 是公式
- 若 $\varphi$ 是公式，$x$ 是变元，则 $\forall x \varphi$, $\exists x \varphi$ 是公式

---

### 2.2 结构与解释

**定义 2.4** ($\mathcal{L}$-结构): $\mathcal{L}$-结构 $\mathcal{M}$ 包含：
- **论域**: 非空集合 $M$
- **解释函数**: 
  - 对每个 $n$-元函数符号 $f$，赋予函数 $f^{\mathcal{M}}: M^n \to M$
  - 对每个 $n$-元谓词符号 $R$，赋予关系 $R^{\mathcal{M}} \subseteq M^n$
  - 对每个常数符号 $c$，赋予元素 $c^{\mathcal{M}} \in M$

**定义 2.5** (满足关系): 设 $\mathcal{M}$ 是 $\mathcal{L}$-结构，$\sigma$ 是赋值，定义满足关系 $\mathcal{M} \models_\sigma \varphi$ 递归地：
- $\mathcal{M} \models_\sigma t_1 = t_2$  iff  $t_1^{\mathcal{M},\sigma} = t_2^{\mathcal{M},\sigma}$
- $\mathcal{M} \models_\sigma R(t_1, \ldots, t_n)$  iff  $(t_1^{\mathcal{M},\sigma}, \ldots, t_n^{\mathcal{M},\sigma}) \in R^{\mathcal{M}}$
- $\mathcal{M} \models_\sigma \exists x \varphi$  iff  存在 $a \in M$ 使得 $\mathcal{M} \models_{\sigma[x/a]} \varphi$

---

## 3. 核心定理

### 3.1 完备性定理

**定义 3.1** (逻辑后承): $T \models \varphi$ 表示任何满足 $T$ 的结构都满足 $\varphi$。

**定义 3.2** (形式可证): $T \vdash \varphi$ 表示存在从 $T$ 到 $\varphi$ 的形式证明。

**定理 3.1** (Gödel完备性定理, 1929): 
$$T \models \varphi \quad \text{当且仅当} \quad T \vdash \varphi$$
特别地，$T$ 是一致的当且仅当 $T$ 有模型。

**证明概要**: 
1. 构造一致的完备理论 $T^* \supseteq T$
2. 用Henkin方法添加 witnesses
3. 从 $T^*$ 的语法构造典范模型 $\mathcal{M}$
4. 证明 $\mathcal{M} \models T^*$ $\square$

---

### 3.2 紧致性定理

**定理 3.2** (紧致性定理): 理论 $T$ 有模型当且仅当 $T$ 的每个有限子集有模型。

**证明**: 由完备性定理，$T$ 有模型 $\Leftrightarrow$ $T$ 一致 $\Leftrightarrow$ 每个有限子集一致 $\Leftrightarrow$ 每个有限子集有模型。$\square$

**推论 3.1**: 若理论 $T$ 有任意大的有限模型，则 $T$ 有无穷模型。

**推论 3.2** (Löwenheim-Skolem向上定理): 若 $T$ 有无穷模型，则对任意基数 $\kappa \geq |\mathcal{L}|$，$T$ 有基数为 $\kappa$ 的模型。

**推论 3.3** (Löwenheim-Skolem向下定理): 若 $T$ 有模型，则 $T$ 有基数 $\leq |\mathcal{L}|$ 的模型。

---

## 4. 同态与同构

### 4.1 结构映射

**定义 4.1** (同态): 映射 $h: \mathcal{M} \to \mathcal{N}$ 是同态，若：
- $h(c^{\mathcal{M}}) = c^{\mathcal{N}}$（对所有常数 $c$）
- $h(f^{\mathcal{M}}(a_1, \ldots, a_n)) = f^{\mathcal{N}}(h(a_1), \ldots, h(a_n))$
- $(a_1, \ldots, a_n) \in R^{\mathcal{M}} \Rightarrow (h(a_1), \ldots, h(a_n)) \in R^{\mathcal{N}}$

**定义 4.2** (嵌入): 同态 $h$ 是嵌入，若 $h$ 是单射且保持谓词的双向：
$$(a_1, \ldots, a_n) \in R^{\mathcal{M}} \Leftrightarrow (h(a_1), \ldots, h(a_n)) \in R^{\mathcal{N}}$$

**定义 4.3** (同构): 满射的嵌入称为同构，记 $\mathcal{M} \cong \mathcal{N}$。

**定理 4.1**: 同构的结构满足完全相同的句子。

---

### 4.2 初等等价与初等子结构

**定义 4.4** (初等等价): $\mathcal{M} \equiv \mathcal{N}$ 表示对所有句子 $\varphi$，$\mathcal{M} \models \varphi \Leftrightarrow \mathcal{N} \models \varphi$。

**定义 4.5** (初等子结构): $\mathcal{M} \preceq \mathcal{N}$（$\mathcal{M}$ 是 $\mathcal{N}$ 的初等子结构）表示：
$$\mathcal{M} \subseteq \mathcal{N} \quad \text{且} \quad \forall \varphi(\bar{v}), \forall \bar{a} \in M^{|\bar{v}|}, \mathcal{M} \models \varphi(\bar{a}) \Leftrightarrow \mathcal{N} \models \varphi(\bar{a})$$

**定理 4.2** (Tarski-Vaught判别法): $\mathcal{M} \subseteq \mathcal{N}$ 是初等子结构当且仅当：
对任意公式 $\varphi(v, \bar{w})$ 和 $\bar{a} \in M^{|\bar{w}|}$，
$$\mathcal{N} \models \exists v \varphi(v, \bar{a}) \Rightarrow \exists b \in M, \mathcal{N} \models \varphi(b, \bar{a})$$

---

## 5. 量词消去与模型完备性

### 5.1 量词消去

**定义 5.1** (量词消去): 理论 $T$ 允许量词消去，若对每个公式 $\varphi(\bar{v})$，存在无量词公式 $\psi(\bar{v})$ 使得：
$$T \models \forall \bar{v} (\varphi(\bar{v}) \leftrightarrow \psi(\bar{v}))$$

**定理 5.1**: 稠密线性序无端点理论 (DLO) 允许量词消去。

**推论 5.1**: DLO是完备的、可判定的。

---

### 5.2 代数闭域

**定义 5.2** (代数闭域/ACF): 域 $F$ 是代数闭的，若每个非常数多项式 $f(x) \in F[x]$ 在 $F$ 中有根。

**定理 5.2** (Tarski): ACF允许量词消去。

**定理 5.3**: ACF$_p$（特征为 $p$ 的代数闭域）是完备的、可判定的。

---

## 6. 稳定性理论入门

### 6.1 稳定性概念

**定义 6.1** (型): 设 $A \subseteq \mathcal{M}$，$n$-型 $p(\bar{v})$ 是在 $A$ 上相容的公式集。

**定义 6.2** (稳定性): 理论 $T$ 是 $\kappa$-稳定的，若对任意 $|A| \leq \kappa$，有 $|S_n(A)| \leq \kappa$。

**定理 6.1** (Morley定理): 完全可数理论 $T$ 要么：
- 对某个 $\kappa$ 是 $\kappa$-不稳定的
- 对某个 $\kappa$ 是 $\kappa$-稳定的但不对所有 $\kappa$ 稳定（超稳定）
- 对某个 $\kappa$ 稳定且对所有 $\kappa$ 稳定（全超越）

---

## 7. 目录结构

```
docs/07-数理逻辑/02-模型论/
├── 00-README.md                    # 本文件
├── 01-一阶语言.md                   # 语法与语义基础
├── 02-完备性定理.md                 # Henkin构造
├── 03-紧致性定理.md                 # Löwenheim-Skolem定理
├── 04-同态与同构.md                 # 结构映射
├── 05-量词消去.md                   # 可判定性理论
├── 06-稳定性理论.md                 # Shelah稳定性
└── 07-o-极小结构.md                 # 实代数几何应用
```

---

## 8. 学习路径

### 8.1 基础路径
**一阶逻辑基础** → **完备性定理** → **紧致性定理** → **量词消去** → **稳定性理论**

### 8.2 应用路径
- **代数**: ACF、微分闭域
- **分析**: o-极小结构、实闭域
- **数论**: 丢番图几何、Manin-Mumford猜想

---

**最后更新**: 2026年4月5日  
**维护者**: FormalMath项目组  
**质量等级**: ⭐⭐⭐⭐⭐ (研究级)
