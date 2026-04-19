---
title: "可计算性理论 (Computability Theory)"
msc_primary: 03

  - 03D05
msc_secondary: ['03D10', '03D25', '03D30', '03D35']
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

# 可计算性理论 (Computability Theory)

**最后更新**: 2026年4月5日  
**MSC分类**: 03D-XX (递归论), 研究可计算性与不可判定性

---

## 1. 引言

可计算性理论（又称递归论）是数理逻辑的核心分支，研究算法可解与不可解的问题边界。从Church-Turing论题到Gödel不完备定理，从停机问题到多项式层级，可计算性理论不仅奠定了计算机科学的理论基础，也深刻影响了我们对数学真理本质的理解。

---

## 2. 可计算函数的形式化

### 2.1 Turing机

**定义 2.1** (Turing机): Turing机是一个七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, q_{accept}, q_{reject})$，其中：
- $Q$: 有限状态集
- $\Sigma$: 输入字母表（不含空白符 $\sqcup$）
- $\Gamma$: 带字母表，$\Sigma \subseteq \Gamma$，$\sqcup \in \Gamma$
- $\delta: Q \times \Gamma \to Q \times \Gamma \times \{L, R\}$: 转移函数（部分函数）
- $q_0 \in Q$: 初始状态
- $q_{accept}, q_{reject} \in Q$: 接受和拒绝状态

**定义 2.2** (Turing可计算): 函数 $f: \Sigma^* \to \Sigma^*$ 是Turing可计算的，若存在Turing机 $M$ 使得对所有输入 $w$：
- 若 $f(w)$ 有定义，则 $M$ 在带上留下 $f(w)$ 后停机
- 若 $f(w)$ 无定义，则 $M$ 永不停机

---

### 2.2 其他计算模型

**定义 2.3** ($\lambda$-演算): $\lambda$-项由以下文法生成：
$$e ::= x \mid \lambda x.e \mid (e_1 \ e_2)$$

**定义 2.4** ( $\beta$-归约): $(\lambda x.e_1)e_2 \to_\beta e_1[e_2/x]$

**定理 2.1** (Church-Turing论题): 所有直觉上可计算的函数都是Turing可计算的。

**注**: 这是一个论题（不可证明的断言），而非定理。

---

## 3. 可判定性与可识别性

### 3.1 语言分类

**定义 3.1** (语言): 语言 $L \subseteq \Sigma^*$ 是字符串集合。

**定义 3.2** (可判定): 语言 $L$ 是可判定的，若存在Turing机 $M$ 使得：
- $w \in L \Rightarrow M$ 接受 $w$
- $w \notin L \Rightarrow M$ 拒绝 $w$

**定义 3.3** (可识别/半可判定): 语言 $L$ 是可识别的，若存在Turing机 $M$ 使得：
$$L = \{w : M \text{ 在输入 } w \text{ 上接受}\}$$

**定理 3.1**: 语言 $L$ 可判定当且仅当 $L$ 和 $\overline{L}$ 都可识别。

---

### 3.2 停机问题

**定义 3.4** (停机问题): 
$$A_{TM} = \{\langle M, w \rangle : M \text{ 是Turing机且 } M \text{ 接受 } w\}$$

**定理 3.2** (停机问题不可判定): $A_{TM}$ 不可判定。

**证明** (对角线法): 假设 $H$ 判定 $A_{TM}$。构造机器 $D$：
- 输入 $\langle M \rangle$
- 运行 $H$ 在 $\langle M, \langle M \rangle \rangle$ 上
- 若 $H$ 接受，则拒绝；若 $H$ 拒绝，则接受

则 $D$ 接受 $\langle D \rangle$ 当且仅当 $D$ 不接受 $\langle D \rangle$，矛盾。$\square$

**推论 3.1**: 若 $L$ 不可判定且 $L \leq_m A$，则 $A$ 不可判定。

---

## 4. 可归约性

### 4.1 多一归约

**定义 4.1** (多一归约): $A \leq_m B$ 若存在可计算函数 $f$ 使得：
$$w \in A \Leftrightarrow f(w) \in B$$

**定理 4.1**: 若 $A \leq_m B$ 且 $B$ 可判定，则 $A$ 可判定。

**定义 4.2** (完全可计算枚举集): 集合 $K$ 是m-完全的，若 $K$ 可计算枚举且对所有可计算枚举集 $A$，$A \leq_m K$。

**定理 4.2**: 停机问题 $K = \{e : \varphi_e(e)\downarrow\}$ 是m-完全的。

---

### 4.2 Turing归约

**定义 4.3** (Turing归约/相对可计算): $A \leq_T B$ 若存在Oracle Turing机 $M^B$ 判定 $A$。

**定义 4.4** (图灵度): $A$ 和 $B$ 图灵等价（$A \equiv_T B$）若 $A \leq_T B$ 且 $B \leq_T A$。

**定理 4.3**: 图灵度形成上半格，最小元 $\mathbf{0}$（可判定集的度），最大元不存在。

---

## 5. 递归定理与不动点

### 5.1 Kleene递归定理

**定理 5.1** (Kleene递归定理): 对任意可计算函数 $f: \mathbb{N} \to \mathbb{N}$，存在 $e$ 使得：
$$\varphi_e = \varphi_{f(e)}$$

**证明**: 构造对角线函数，应用s-m-n定理。$\square$

**推论 5.1**: 存在程序输出自身代码（Quine）。

---

### 5.2 Rice定理

**定理 5.2** (Rice定理): 任何关于程序语义的非平凡性质都是不可判定的。

形式化：设 $\mathcal{C}$ 是可计算函数的非平凡类，则 $\{e : \varphi_e \in \mathcal{C}\}$ 不可判定。

**证明**: 假设可判定。利用对角线构造导出矛盾。$\square$

---

## 6. 复杂性理论入门

### 6.1 时间复杂性

**定义 6.1** (时间复杂性类):
- $\text{P} = \bigcup_{k \geq 1} \text{TIME}(n^k)$: 多项式时间可判定
- $\text{NP} = \bigcup_{k \geq 1} \text{NTIME}(n^k)$: 非确定性多项式时间可验证
- $\text{EXP} = \bigcup_{k \geq 1} \text{TIME}(2^{n^k})$

**定义 6.2** (NP完全): 语言 $L$ 是NP完全的，若：
1. $L \in \text{NP}$
2. 对所有 $A \in \text{NP}$，$A \leq_p L$（多项式时间归约）

**定理 6.1** (Cook-Levin定理): SAT（布尔可满足性）是NP完全的。

---

### 6.2 空间复杂性

**定义 6.3** (空间复杂性类):
- $\text{L} = \text{SPACE}(\log n)$: 对数空间
- $\text{PSPACE} = \bigcup_{k \geq 1} \text{SPACE}(n^k)$
- $\text{NPSPACE} = \bigcup_{k \geq 1} \text{NSPACE}(n^k)$

**定理 6.2** (Savitch定理): $\text{NPSPACE} \subseteq \text{SPACE}((\log n)^2)$，故 $\text{PSPACE} = \text{NPSPACE}$。

---

## 7. 目录结构

```
docs/07-数理逻辑/04-可计算性理论/
├── 00-README.md                    # 本文件
├── 01-计算模型.md                   # Turing机、λ演算
├── 02-可判定性.md                   # 可判定、可识别语言
├── 03-停机问题.md                   # 对角线法
├── 04-可归约性.md                   # m-归约、Turing归约
├── 05-递归定理.md                   # 不动点定理
├── 06-复杂性理论.md                 # P vs NP
└── 07-实战问题.md                   # 不可判定性证明练习
```

---

## 8. 学习路径

### 8.1 基础路径
**Turing机** → **可判定性** → **停机问题** → **可归约性** → **复杂性理论**

### 8.2 高级路径
- **度理论**: 图灵度结构、优先方法
- **可计算模型论**: 可表示结构
- **反推数学**: 证明的强度分析

---

## 9. 核心定理索引

| 定理 | 领域 | 贡献者 | 年份 | 重要性 |
|------|------|--------|------|--------|
| 停机问题不可判定 | 可计算性 | Turing | 1936 | ⭐⭐⭐⭐⭐ |
| Church-Turing论题 | 计算模型 | Church, Turing | 1936 | ⭐⭐⭐⭐⭐ |
| Rice定理 | 语义性质 | Rice | 1953 | ⭐⭐⭐⭐ |
| Kleene递归定理 | 自引用 | Kleene | 1938 | ⭐⭐⭐⭐ |
| Cook-Levin定理 | 复杂性 | Cook, Levin | 1971 | ⭐⭐⭐⭐⭐ |
| Savitch定理 | 空间复杂性 | Savitch | 1970 | ⭐⭐⭐⭐ |

---

**最后更新**: 2026年4月5日  
**维护者**: FormalMath项目组  
**质量等级**: ⭐⭐⭐⭐⭐ (研究级)
