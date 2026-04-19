---
title: 射影概形的构造
msc_primary: 14
  - 14A15
  - 14C40
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 9-10
topic: 射影概形与丰沛线丛
exercise_type: GEO (几何型)
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

# AG-VK-004: 射影概形的构造

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 9-10: 射影概形 |
| **对应FOAG习题** | 9.3.E, 10.4.B, 10.5.G |
| **类型** | GEO (几何型) |
| **难度** | ⭐⭐⭐ |
| **重要性** | ★★ |

---

## 问题陈述

### 主问题

设 $S = \operatorname{Spec} A$ 是仿射概形，$A$ 是分次环 $A = \bigoplus_{d \geq 0} A_d$。

**(a)** **Proj构造的泛性质**：

定义 $\operatorname{Proj} A$ 为 $A_+$（正次数部分）中齐次素理想的集合，带有Zariski拓扑和结构层。

证明：对于任意概形 $X$，给出一个 $S$-态射 $X \to \operatorname{Proj} A$ 等价于给出：
1. 可逆层 $\mathcal{L}$ 在 $X$ 上
2. 分次环同态 $A \to \Gamma_*(X, \mathcal{L})$（截面分次代数）
3. 像生成 $\mathcal{L}$（即 $A_1$ 的像生成 $\mathcal{L}$）

**(b)** **射影丛的构造**：

设 $\mathcal{E}$ 是 $S$ 上秩为 $n+1$ 的局部自由层，定义射影丛：
$$\mathbb{P}(\mathcal{E}) = \operatorname{Proj}(\operatorname{Sym}^* \mathcal{E})$$

证明：存在自然的投射 $\pi: \mathbb{P}(\mathcal{E}) \to S$ 和线丛 $\mathcal{O}_{\mathbb{P}(\mathcal{E})}(1)$，满足泛性质。

**(c)** **丰沛性判定**：

设 $X$ 是 $S$-概形，$\mathcal{L}$ 是 $X$ 上的可逆层。证明以下等价：
1. $\mathcal{L}$ 是 $S$-丰沛的（amper relative to $S$）
2. 存在 $n > 0$ 使得 $\mathcal{L}^{\otimes n}$ 给出浸入 $X \hookrightarrow \mathbb{P}^N_S$

---

## 解题思路

### 思路概述

本题涉及射影几何的**核心构造**：
- **Proj** - 从分次环构造射影概形
- **射影丛** - 向量丛的射影化
- **丰沛性** - 射影嵌入的组合判据

### 几何直观

```
Proj 构造的直观

仿射概形: Spec A      射影概形: Proj A
    │                       │
    │  所有素理想            │  齐次素理想
    │  （几何点）             │  （射影等价类）
    ▼                       ▼
  仿射空间                射影空间
  A^n                     P^n
  
关键区别：Proj 忽略了“原点”(A_+)
```

```
射影丛的几何

向量丛 E → S          射影丛 P(E) → S
    │                      │
    │  每点纤维是 A^n      │  每点纤维是 P^n
    │                      │
    ▼                      ▼
   线性空间              射影空间
   （带原点）             （无原点）
```

---

## 详细解答

### (a) Proj 的泛性质

**定理**：$\operatorname{Hom}_S(X, \operatorname{Proj} A) \cong \{(\mathcal{L}, \phi)\}/\cong$

其中 $\mathcal{L}$ 是 $X$ 上可逆层，$\phi: A \to \Gamma_*(X, \mathcal{L})$ 是分次同态且 $A_1$ 生成 $\mathcal{L}$。

**证明概要**：

**构造**：给定 $(\mathcal{L}, \phi)$，构造 $f: X \to \operatorname{Proj} A$。

对 $a \in A_+$ 齐次，设 $U_a = X_{\phi(a)}$（非消失集）。

在 $U_a$ 上，$\phi(a) \in \mathcal{L}(U_a)$ 是处处非零截面，给出平凡化 $\mathcal{L}|_{U_a} \cong \mathcal{O}_{U_a}$。

这给出环同态 $A_{(a)} \to \mathcal{O}_X(U_a)$，即 $U_a \to \operatorname{Spec} A_{(a)} \subset \operatorname{Proj} A$。

这些映射相容，黏合为 $f: X \to \operatorname{Proj} A$。

**逆构造**：给定 $f: X \to \operatorname{Proj} A$，拉回 $\mathcal{L} = f^*\mathcal{O}(1)$，标准映射 $A \to \Gamma_*(\mathcal{L})$。

∎

### (b) 射影丛的构造

**定义**：设 $\mathcal{E}$ 是秩 $n+1$ 局部自由层，则：
$$\operatorname{Sym}^* \mathcal{E} = \mathcal{O}_S \oplus \mathcal{E} \oplus \operatorname{Sym}^2 \mathcal{E} \oplus \cdots$$

是拟凝聚 $\mathcal{O}_S$-代数。

**相对Proj**：定义
$$\mathbb{P}(\mathcal{E}) = \underline{\operatorname{Proj}}_S(\operatorname{Sym}^* \mathcal{E})$$

这是 $S$-概形，带有投射 $\pi: \mathbb{P}(\mathcal{E}) \to S$。

**纤维**：对 $s \in S$，
$$\mathbb{P}(\mathcal{E})_s = \mathbb{P}(\mathcal{E}_s \otimes k(s)) = \mathbb{P}^n_{k(s)}$$

**泛性质**：

$\mathbb{P}(\mathcal{E})$ 代表函子：
$$X \mapsto \{(\mathcal{L}, \phi: \pi^*\mathcal{E} \twoheadrightarrow \mathcal{L})\}/\cong$$

即 $X$ 到 $\mathbb{P}(\mathcal{E})$ 的态射等价于给出 $X$ 上可逆层和 $\mathcal{E}$ 的商。

**标准线丛**：$\mathcal{O}_{\mathbb{P}(\mathcal{E})}(1)$ 满足：
$$\pi_* \mathcal{O}(1) = \mathcal{E}^\vee$$

（当 $S$ 仿射时）。∎

### (c) 丰沛性判定

**定义**：$\mathcal{L}$ 是 $S$-丰沛的，如果对任意仿射开集 $U \subset S$，$\mathcal{L}|_{X_U}$ 是丰沛的（在绝对意义下）。

**绝对丰沛性**：$\mathcal{L}$ 丰沛 $\Leftrightarrow$ 对任意凝聚层 $\mathcal{F}$，当 $n \gg 0$ 时 $\mathcal{F} \otimes \mathcal{L}^n$ 整体生成。

**等价性证明**：

**$\mathcal{L}$ 丰沛 $\Rightarrow$ 给出浸入**：

由丰沛性，$\mathcal{L}^n$ 整体生成，给出：
$$f: X \to \mathbb{P}^N_S = \mathbb{P}(\pi_*\mathcal{L}^n)$$

需要证明这是浸入（浸入 = 开浸入 + 闭浸入，或局部闭浸入）。

利用丰沛性的另一判据：$X$ 可以被形如 $X_s$（$s \in \Gamma(X, \mathcal{L}^n)$）的仿射开集覆盖。

**浸入 $\Rightarrow$ 丰沛**：

若 $f: X \hookrightarrow \mathbb{P}^N_S$ 是浸入，则 $\mathcal{L} = f^*\mathcal{O}(1)$ 是丰沛的（因为 $\mathcal{O}(1)$ 丰沛，丰沛性在拉回下保持）。

∎

---

## 关键概念

### Proj 构造

**分次环**：$A = \bigoplus_{d \geq 0} A_d$，$A_d \cdot A_e \subset A_{d+e}$。

**齐次谱**：$\operatorname{Proj} A = \{\mathfrak{p} \in \operatorname{Spec} A : \mathfrak{p} \text{ 齐次}, A_+ \not\subset \mathfrak{p}\}$

**拓扑**：Zariski拓扑，闭集 $V_+(I) = \{\mathfrak{p} : I \subset \mathfrak{p}\}$（$I$ 齐次理想）。

**结构层**：$\mathcal{O}_{\operatorname{Proj} A}(D_+(f)) = A_{(f)}$（齐次局部化）。

### 丰沛性 vs 极强性

| 性质 | 定义 | 关系 |
|------|------|------|
| **极强 (very ample)** | 给出闭浸入到 $\mathbb{P}^n$ | 极强 $\Rightarrow$ 丰沛 |
| **丰沛 (ample)** | 张量幂整体生成 | 丰沛 $\Leftrightarrow$ 某个张量幂极强 |

**重要区别**：
- 极强性依赖于特定的射影嵌入
- 丰沛性是内在性质

---

## 计算示例

### 例: $\mathbb{P}^1$ 上的线丛

设 $X = \mathbb{P}^1_k$，$\mathcal{O}(1)$ 是超平面线丛。

| 线丛 | 丰沛性 | 极强性 | 整体截面 |
|------|--------|--------|----------|
| $\mathcal{O}(n), n > 0$ | ✅ 丰沛 | ✅ 极强 | $\dim = n+1$ |
| $\mathcal{O}(0) = \mathcal{O}$ | ❌ 不丰沛 | ❌ | $\dim = 1$ |
| $\mathcal{O}(n), n < 0$ | ❌ 不丰沛 | ❌ | $0$ |

### 例: 曲线的典范嵌入

设 $C$ 是亏格 $g \geq 2$ 的光滑射影曲线，$K_C$ 是典范除子。

- $\mathcal{O}(K_C)$ 是丰沛的（除非是超椭圆曲线）
- 给出浸入 $C \hookrightarrow \mathbb{P}^{g-1}$（典范嵌入）

---

## 相关结果

### 周引理 (Chow's Lemma)

**定理**：设 $X$ 是 $S$ 上有限型分离概形，则存在射影概形 $\bar{X}$ 和满射、固有、双有理态射 $\bar{X} \to X$。

**意义**：任何"合理"的概形都被某个射影概形支配。

### 丰沛性的数值判据

对曲面（或高维），丰沛性有数值判据（Nakai-Moishezon判据）。

---

## 变式练习

### 变式 1: Hirzebruch 曲面

设 $\mathcal{E} = \mathcal{O}_{\mathbb{P}^1} \oplus \mathcal{O}_{\mathbb{P}^1}(n)$，计算 $\mathbb{P}(\mathcal{E})$（Hirzebruch曲面 $\mathbb{F}_n$）。

### 变式 2: Segre嵌入

证明：乘积 $\mathbb{P}^m \times \mathbb{P}^n$ 可以嵌入到 $\mathbb{P}^{(m+1)(n+1)-1}$（Segre嵌入）。

**提示**：用分次环的张量积，$\operatorname{Proj}(A \otimes B)$。

### 变式 3: 丰沛性的上同调判据

证明：$\mathcal{L}$ 丰沛 $\Leftrightarrow$ 对任意凝聚层 $\mathcal{F}$，$H^i(X, \mathcal{F} \otimes \mathcal{L}^n) = 0$ 对所有 $i > 0$，$n \gg 0$（Serre判据）。

---

## 常见错误

| 错误 | 纠正 |
|------|------|
| 混淆 $\operatorname{Proj}$ 与 $\operatorname{Spec}$ | Proj 需要分次结构，且排除 $A_+$ |
| 认为射影丛是乘积 | $\mathbb{P}(\mathcal{E}) \neq \mathbb{P}^n \times S$ 一般 |
| 丰沛 = 整体生成 | 丰沛性更强，涉及所有凝聚层 |

---

## 学习建议

1. **理解 Proj 的泛性质**：这是射影几何的核心
2. **熟悉标准例子**：$\mathbb{P}^n$, Hirzebruch 曲面等
3. **掌握丰沛性的多种判据**：嵌入判据、上同调判据、数值判据

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-004-射影概形的构造.md`  
**创建日期**: 2026-04-10  
**最后更新**: 2026-04-10
