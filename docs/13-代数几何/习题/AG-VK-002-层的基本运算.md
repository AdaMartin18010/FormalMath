---
title: 层的基本运算
msc_primary: 14
  - 14F05
  - 18F20
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 2-3
topic: 层论基础运算
exercise_type: TEC (技术型)
difficulty: ⭐⭐
importance: ★
references:
  textbooks:
    - id: hartshorne_ag
      type: textbook
      title: Algebraic Geometry
      authors:
      - Robin Hartshorne
      publisher: Springer
      edition: 1st
      year: 1977
      isbn: 978-0387902449
      msc: 14-01
      chapters: 
      url: ~
    - id: vakil_foag
      type: textbook
      title: Foundations of Algebraic Geometry
      authors:
      - Ravi Vakil
      publisher: self-published
      edition: draft
      year: 2024
      isbn: ~
      msc: 14-01
      chapters: 
      url: "https://math.stanford.edu/~vakil/216blog/"
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

# AG-VK-002: 层的基本运算

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 2-3: 层论基础 |
| **对应FOAG习题** | 2.3.C, 2.3.F, 3.1.A |
| **类型** | TEC (技术型) |
| **难度** | ⭐⭐ |
| **重要性** | ★ |

---

## 问题陈述

### 主问题

设 $X$ 是拓扑空间，$\mathcal{F}, \mathcal{G}$ 是 $X$ 上的阿贝尔群层。

**(a)** **层的 Hom**: 定义 $\mathcal{H}om(\mathcal{F}, \mathcal{G})$ 为预层：
$$U \mapsto \operatorname{Hom}_{\text{Sh}(U)}(\mathcal{F}|_U, \mathcal{G}|_U)$$

证明这是一个层（不是仅仅预层）。

**(b)** **张量积**: 设 $\mathcal{F}, \mathcal{G}$ 是 $\mathcal{O}_X$-模层，定义：
$$\mathcal{F} \otimes_{\mathcal{O}_X} \mathcal{G} := (\mathcal{F} \otimes_{\mathcal{O}_X}^{\text{pre}} \mathcal{G})^+$$
其中上标 $+$ 表示层化（sheafification）。

验证：对于任意开集 $U$，$(\mathcal{F} \otimes_{\mathcal{O}_X} \mathcal{G})(U)$ 中的元素可以局部表示为有限和 $\sum f_i \otimes g_i$。

**(c)** **茎的计算**: 证明对于任意 $p \in X$：
- $\mathcal{H}om(\mathcal{F}, \mathcal{G})_p \cong \operatorname{Hom}(\mathcal{F}_p, \mathcal{G}_p)$（注意：一般不对！）
- $(\mathcal{F} \otimes_{\mathcal{O}_X} \mathcal{G})_p \cong \mathcal{F}_p \otimes_{\mathcal{O}_{X,p}} \mathcal{G}_p$

---

## 解题思路

### 思路概述

本题涉及层的三大基本运算：
1. **Hom层** - 内部Hom，结果仍是层
2. **张量积** - 需要层化
3. **茎的交换性** - 层化与张量积交换

### 技术要点

```
层化 Sheafification

预层 P ──→ 层 P^+ (伴随于遗忘函子的左伴随)
    │
    └─ 满足层公理：局部定义唯一黏合

关键性质：
1. 有典范映射 P → P^+
2. (P^+)_p = P_p 对所有茎
3. Hom(P, F) ≅ Hom(P^+, F) 对任意层 F
```

---

## 详细解答

### (a) $\mathcal{H}om(\mathcal{F}, \mathcal{G})$ 是层

**证明**：

需要验证层公理：设 $\{U_i\}$ 是 $U$ 的开覆盖。

**唯一性**：设 $\phi, \psi \in \mathcal{H}om(\mathcal{F}, \mathcal{G})(U)$ 满足 $\phi|_{U_i} = \psi|_{U_i}$ 对所有 $i$。

对任意开集 $V \subset U$ 和任意 $s \in \mathcal{F}(V)$，需证 $\phi_V(s) = \psi_V(s)$。

$\{V \cap U_i\}$ 覆盖 $V$，且：
$$(\phi_V(s))|_{V \cap U_i} = \phi_{V \cap U_i}(s|_{V \cap U_i}) = \psi_{V \cap U_i}(s|_{V \cap U_i}) = (\psi_V(s))|_{V \cap U_i}$$

因 $\mathcal{G}$ 是层，$\phi_V(s) = \psi_V(s)$。∎

**存在性**：设给定相容的 $\phi_i \in \mathcal{H}om(\mathcal{F}, \mathcal{G})(U_i)$。

对 $V \subset U$，定义 $\phi_V: \mathcal{F}(V) \to \mathcal{G}(V)$：

对 $s \in \mathcal{F}(V)$，限制到 $V \cap U_i$ 得 $s_i = s|_{V \cap U_i}$。

$\phi_i$ 给出 $t_i = (\phi_i)_{V \cap U_i}(s_i) \in \mathcal{G}(V \cap U_i)$。

相容性条件保证 $\{t_i\}$ 黏合为唯一的 $t \in \mathcal{G}(V)$。定义 $\phi_V(s) = t$。

验证这是层同态（保持加法和限制）。∎

### (b) 张量积的局部描述

**解答**：

预层张量积定义为：
$$(\mathcal{F} \otimes^{\text{pre}} \mathcal{G})(U) = \mathcal{F}(U) \otimes_{\mathcal{O}_X(U)} \mathcal{G}(U)$$

层化后，$(\mathcal{F} \otimes \mathcal{G})(U)$ 由相容的局部数据组成。

**具体描述**：元素 $\xi \in (\mathcal{F} \otimes \mathcal{G})(U)$ 对应以下数据：
- 开覆盖 $\{U_i\}$ 的 $U$
- 对每个 $i$，元素 $\xi_i = \sum_k f_{ik} \otimes g_{ik} \in \mathcal{F}(U_i) \otimes \mathcal{G}(U_i)$
- 在 $U_i \cap U_j$ 上，$\xi_i$ 和 $\xi_j$ 表示同一张量

**注意**：一般情况下，全局元素**不能**写为有限和 $\sum f_k \otimes g_k$，其中 $f_k \in \mathcal{F}(U), g_k \in \mathcal{G}(U)$。

**例子**（需要层化的情况）：

设 $X = \mathbb{P}^1_k$，$\mathcal{F} = \mathcal{O}(1)$，$\mathcal{G} = \mathcal{O}(-1)$。

则 $\mathcal{F} \otimes \mathcal{G} \cong \mathcal{O}$。

全局截面 $\mathcal{O}(\mathbb{P}^1) = k$，对应单位元 $1$。

但 $\mathcal{O}(1)$ 没有非零全局截面，所以 $1$ 不能写为全局截面张量的和！

### (c) 茎的计算

**证明**：

**张量积与茎交换**：

由层化的性质，$(\mathcal{F} \otimes^{\text{pre}} \mathcal{G})^+_p = (\mathcal{F} \otimes^{\text{pre}} \mathcal{G})_p$。

而预层茎是正向极限：
$$(\mathcal{F} \otimes^{\text{pre}} \mathcal{G})_p = \varinjlim_{p \in U} \mathcal{F}(U) \otimes \mathcal{G}(U) = \varinjlim \mathcal{F}(U) \otimes \varinjlim \mathcal{G}(U) = \mathcal{F}_p \otimes \mathcal{G}_p$$

（张量积与正向极限交换）∎

**Hom与茎**：

**注意**：一般情况下：
$$\mathcal{H}om(\mathcal{F}, \mathcal{G})_p \not\cong \operatorname{Hom}(\mathcal{F}_p, \mathcal{G}_p)$$

左边到右边有典范映射，但一般不是同构。

**反例**：设 $X = \mathbb{A}^1_k$，$p = 0$。令 $\mathcal{F} = \bigoplus_{n \geq 0} \mathcal{O}$（无限直和），$\mathcal{G} = \mathcal{O}$。

则 $\mathcal{F}_p = \bigoplus_{n \geq 0} \mathcal{O}_p$（代数直和），但：
$$\operatorname{Hom}(\mathcal{F}, \mathcal{G})(U) = \prod_{n \geq 0} \mathcal{O}(U)$$

正向极限与无限积不交换。

**正面结果**：若 $\mathcal{F}$ 是有限展示的（finite presentation），则有同构。

---

## 关键概念

### 层化 (Sheafification)

预层 $\mathcal{P} \leadsto$ 层 $\mathcal{P}^+$ 的构造：

$\mathcal{P}^+(U) = \{(s_p)_{p \in U} \in \prod_{p \in U} \mathcal{P}_p : \forall p, \exists p \in V \subset U, \exists t \in \mathcal{P}(V), \forall q \in V: t_q = s_q\}$

### 层运算的左右正合性

| 运算 | 正合性 | 说明 |
|------|--------|------|
| $\mathcal{H}om(\mathcal{F}, -)$ | 左正合 | 对第二变元 |
| $\mathcal{H}om(-, \mathcal{G})$ | 左正合 | 反变函子 |
| $\mathcal{F} \otimes -$ | 右正合 | 需要导出函子 |

---

## 相关结果

### 伴随关系

$$\operatorname{Hom}(\mathcal{F} \otimes \mathcal{G}, \mathcal{H}) \cong \operatorname{Hom}(\mathcal{F}, \mathcal{H}om(\mathcal{G}, \mathcal{H}))$$

### 内部Hom的层版本

$$\mathcal{H}om(\mathcal{F} \otimes \mathcal{G}, \mathcal{H}) \cong \mathcal{H}om(\mathcal{F}, \mathcal{H}om(\mathcal{G}, \mathcal{H}))$$

---

## 变式练习

### 变式 1: 推出与拉回

设 $f: X \to Y$ 是连续映射，$\mathcal{F}$ 是 $X$ 上的层，$\mathcal{G}$ 是 $Y$ 上的层。

证明：$\operatorname{Hom}_X(f^{-1}\mathcal{G}, \mathcal{F}) \cong \operatorname{Hom}_Y(\mathcal{G}, f_*\mathcal{F})$。

### 变式 2: 层的扩张

设 $0 \to \mathcal{F}' \to \mathcal{F} \to \mathcal{F}'' \to 0$ 是短正合列，$\mathcal{G}$ 是另一层。

写出 $0 \to \mathcal{H}om(\mathcal{F}'', \mathcal{G}) \to \mathcal{H}om(\mathcal{F}, \mathcal{G}) \to \mathcal{H}om(\mathcal{F}', \mathcal{G})$ 的正合性证明。

### 变式 3: 局部自由层

设 $\mathcal{F}, \mathcal{G}$ 是秩为 $r, s$ 的局部自由层，证明：
- $\mathcal{H}om(\mathcal{F}, \mathcal{G})$ 是秩 $rs$ 的局部自由层
- $\mathcal{F} \otimes \mathcal{G}$ 是秩 $rs$ 的局部自由层
- $\bigwedge^n(\mathcal{F} \otimes \mathcal{G})$ 与 $\bigwedge^r \mathcal{F}$、$\bigwedge^s \mathcal{G}$ 的关系

---

## 计算示例

### 例: $\mathbb{P}^1$ 上的层运算

设 $X = \mathbb{P}^1_k$，计算：

| 运算 | 结果 |
|------|------|
| $\mathcal{O}(m) \otimes \mathcal{O}(n)$ | $\mathcal{O}(m+n)$ |
| $\mathcal{H}om(\mathcal{O}(m), \mathcal{O}(n))$ | $\mathcal{O}(n-m)$ |
| $\mathcal{O}(m)^{\vee} = \mathcal{H}om(\mathcal{O}(m), \mathcal{O})$ | $\mathcal{O}(-m)$ |

---

## 常见错误

| 错误 | 纠正 |
|------|------|
| 忽略张量积需要层化 | 预层张量积一般不是层 |
| 混淆代数Hom与层Hom | $\operatorname{Hom}_{\mathcal{O}_X}(\mathcal{F}, \mathcal{G}) \neq \mathcal{H}om(\mathcal{F}, \mathcal{G})$（左边是全局截面） |
| 认为Hom与茎交换 | 一般不对，需要有限生成条件 |

---

## 学习建议

1. **熟练层公理**：所有验证都基于唯一性和存在性
2. **掌握正向极限**：茎的计算依赖范畴论的极限
3. **对比交换代数**：层论是交换代数的"参数化"版本

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-002-层的基本运算.md`  
**创建日期**: 2026-04-10  
**最后更新**: 2026-04-10
