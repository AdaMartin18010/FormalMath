---
title: 导出函子计算
msc_primary: 14
  - 14F99
  - 18G10
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 16-17
topic: 同调代数技术
exercise_type: HOM (同调型)
difficulty: ⭐⭐⭐
importance: ★★
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

# AG-VK-007: 导出函子计算

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 16-17: 导出函子 |
| **对应FOAG习题** | 16.3.B, 17.2.C |
| **类型** | HOM (同调型) |
| **难度** | ⭐⭐⭐ |
| **重要性** | ★★ |

---

## 问题陈述

### 主问题

设 $\mathcal{A}$ 是Abel范畴，$F: \mathcal{A} \to \mathcal{B}$ 是左正合加性函子。

**(a)** **导出函子的构造**：

设 $\mathcal{A}$ 有足够内射对象。对 $A \in \mathcal{A}$，取内射分解：
$$0 \to A \to I^0 \to I^1 \to I^2 \to \cdots$$

定义 $R^iF(A) = H^i(F(I^\bullet))$。

证明：
1. $R^iF(A)$ 不依赖于内射分解的选取
2. $R^0F(A) = F(A)$
3. 对短正合列 $0 \to A \to B \to C \to 0$，有长正合列：
$$0 \to FA \to FB \to FC \to R^1FA \to R^1FB \to \cdots$$

**(b)** **Ext的计算**：

设 $R$ 是环，$M, N$ 是 $R$-模。证明：
$$\operatorname{Ext}^i_R(M, N) = H^i(\operatorname{Hom}_R(P_\bullet, N))$$

其中 $P_\bullet \to M$ 是投射分解。

**(c)** **具体计算**：

计算 $\operatorname{Ext}^i_{\mathbb{Z}}(\mathbb{Z}/n\mathbb{Z}, \mathbb{Z}/m\mathbb{Z})$ 对所有 $i$。

---

## 解题思路

### 思路概述

本题涉及**同调代数的核心技术**：
- **导出函子** - 从左正合到完全正合
- **Ext函子** - 扩张的分类
- **具体计算** - 从抽象到具体

### 概念图

```
左正合函子 F: A → B
    │
    ▼
0 → F(A) → F(B) → F(C)   ← 不保持满射
    │
    ▼  导出函子 R^iF
    
长正合列:
0 → FA → FB → FC → R^1FA → R^1FB → R^1FC → R^2FA → ...
    │
    ▼
通过内射分解计算
```

---

## 详细解答

### (a) 导出函子的基本性质

**1. 不依赖于分解的选取**

**引理**：任意两个内射分解 $I^\bullet$ 和 $J^\bullet$ 是同伦等价的。

即存在链映射 $f: I^\bullet \to J^\bullet$ 和 $g: J^\bullet \to I^\bullet$，使得 $g \circ f \sim \text{id}$，$f \circ g \sim \text{id}$。

同伦等价的复形有同调的同构，所以：
$$H^i(F(I^\bullet)) \cong H^i(F(J^\bullet))$$

**2. $R^0F(A) = F(A)$**

内射分解：$0 \to A \to I^0 \to I^1 \to \cdots$

应用 $F$：$0 \to FA \to FI^0 \to FI^1 \to \cdots$

由于 $F$ 左正合，$0 \to FA \to FI^0 \to FI^1$ 正合。

所以 $H^0(F(I^\bullet)) = \ker(FI^0 \to FI^1) / 0 = FA$。

**3. 长正合列**

给定 $0 \to A \to B \to C \to 0$，用马蹄引理（Horseshoe Lemma）构造内射分解的短正合列：

$$
\begin{array}{ccccccccc}
0 & \to & A & \to & B & \to & C & \to & 0 \\
  &     & \downarrow & & \downarrow & & \downarrow & & \\
0 & \to & I^\bullet & \to & J^\bullet & \to & K^\bullet & \to & 0
\end{array}$$

其中 $I^\bullet, J^\bullet, K^\bullet$ 分别是 $A, B, C$ 的内射分解。

$I^\bullet$ 内射 $\Rightarrow$ 列分裂，所以复形列正合。

应用 $F$：由于 $F$ 加性，保持分裂性，$0 \to FI^\bullet \to FJ^\bullet \to FK^\bullet \to 0$ 正合。

复形的短正合列给出长正合列（蛇引理迭代）。∎

### (b) Ext函子的计算

**定义**：$\operatorname{Ext}^i_R(M, -) = R^i\operatorname{Hom}_R(M, -)$

**定理**：若 $R$ 有足够投射对象，则：
$$\operatorname{Ext}^i_R(M, N) \cong H^i(\operatorname{Hom}_R(P_\bullet, N))$$

其中 $P_\bullet \to M$ 是投射分解。

**证明概要**：

**平衡性 (Balancing)**：$\operatorname{Ext}$ 可以用内射分解（第二变元）或投射分解（第一变元）计算。

对第二变元用内射分解：
$$\operatorname{Ext}^i(M, N) = H^i(\operatorname{Hom}(M, I^\bullet))$$

对第一变元用投射分解：取 $P_\bullet \to M$。

构造双复形：$C^{p,q} = \operatorname{Hom}(P_p, I^q)$

两个谱序列都收敛到总复形的同调：
- 水平方向先算：$H^p(\operatorname{Hom}(P_\bullet, N))$（用 $I^\bullet$ 的正合性）
- 垂直方向先算：$H^q(\operatorname{Hom}(M, I^\bullet))$（用 $P_\bullet$ 的投射性）

所以两者同构。∎

### (c) Ext的具体计算

**计算** $\operatorname{Ext}^i_{\mathbb{Z}}(\mathbb{Z}/n, \mathbb{Z}/m)$

**步骤1: 投射分解**

$\mathbb{Z}$ 是PID，$\mathbb{Z}/n$ 的投射分解：
$$\cdots \to 0 \to \mathbb{Z} \xrightarrow{\times n} \mathbb{Z} \to \mathbb{Z}/n \to 0$$

即：$P_0 = \mathbb{Z}$，$P_1 = \mathbb{Z}$，$d_1 = \times n$，$P_i = 0$（$i \geq 2$）。

**步骤2: 应用 Hom**

$$\operatorname{Hom}_{\mathbb{Z}}(\mathbb{Z}, \mathbb{Z}/m) = \mathbb{Z}/m$$

复形：
$$0 \to \mathbb{Z}/m \xrightarrow{\times n} \mathbb{Z}/m \to 0$$

**步骤3: 计算同调**

- $\ker(\times n) = \{a \in \mathbb{Z}/m : na \equiv 0 \pmod{m}\} = (m/\gcd(n,m))\mathbb{Z}/m \cong \mathbb{Z}/\gcd(n,m)$
- $\operatorname{im}(\times n) = n\mathbb{Z}/m \cong \mathbb{Z}/(m/\gcd(n,m))$

所以：
$$\operatorname{Ext}^0 = \ker = \mathbb{Z}/\gcd(n,m)$$
$$\operatorname{Ext}^1 = \ker / \operatorname{im} = \mathbb{Z}/\gcd(n,m) / n\mathbb{Z}/m \cong \mathbb{Z}/\gcd(n,m)$$
$$\operatorname{Ext}^i = 0, \quad i \geq 2$$

**总结**：
$$\operatorname{Ext}^i_{\mathbb{Z}}(\mathbb{Z}/n, \mathbb{Z}/m) = \begin{cases} \mathbb{Z}/\gcd(n,m) & i = 0, 1 \\ 0 & i \geq 2 \end{cases}$$

---

## 关键概念

### 导出函子的性质

| 性质 | 说明 |
|------|------|
| $R^0F \cong F$ | 0阶恢复原函子 |
| $R^iF(I) = 0$（$i > 0$, $I$ 内射） | 内射对象零调 |
| 长正合列 | 连接同态 $\delta$ |
| 万有性质 | 任何 $\delta$-函子因子通过导出函子 |

### Ext的解释

**$\operatorname{Ext}^1$ 的分类意义**：

$\operatorname{Ext}^1_R(M, N)$ 一一对应于扩张的等价类：
$$0 \to N \to E \to M \to 0$$

平凡扩张对应 $E = M \oplus N$。

---

## 变式练习

### 变式 1: Tor的计算

计算 $\operatorname{Tor}^i_{\mathbb{Z}}(\mathbb{Z}/n, \mathbb{Z}/m)$。

### 变式 2: 层上同调的导出函子

解释 $\Gamma(X, -)$ 的导出函子如何给出层上同调 $H^i(X, \mathcal{F})$。

### 变式 3: Grothendieck谱序列

设 $F: \mathcal{A} \to \mathcal{B}$，$G: \mathcal{B} \to \mathcal{C}$，陈述Grothendieck谱序列：
$$E_2^{p,q} = R^pG(R^qF(A)) \Rightarrow R^{p+q}(G \circ F)(A)$$

---

## 计算示例

### 群上同调

对群 $G$ 和 $G$-模 $M$，群上同调：
$$H^i(G, M) = \operatorname{Ext}^i_{\mathbb{Z}[G]}(\mathbb{Z}, M)$$

计算 $H^i(C_n, \mathbb{Z})$（循环群，平凡作用）：

$$H^0 = \mathbb{Z}, \quad H^{2k+1} = 0, \quad H^{2k} = \mathbb{Z}/n \text{（$k > 0$）}$$

---

## 常见错误

| 错误 | 纠正 |
|------|------|
| 混淆投射和内射 | 左导出用投射，右导出用内射 |
| 忘记验证分解存在 | 需要范畴有足够投射/内射 |
| 忽略加性条件 | 导出函子要求加性函子 |

---

## 学习建议

1. **掌握同调代数基础**：链复形、同伦、长正合列
2. **练习具体计算**：Ext和Tor的计算
3. **理解几何意义**：导出函子如何测量"正合性的失败"

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-007-导出函子计算.md`  
**创建日期**: 2026-04-10  
**最后更新**: 2026-04-10
