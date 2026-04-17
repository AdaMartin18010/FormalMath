---
title: 分离与真态射判别
msc_primary: 14-01
msc_secondary:
- 14A15
- 14D20
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 7, 8, 11
topic: 概形态射的性质
exercise_type: ANA (分析型)
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
      chapters: []
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
      chapters: []
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

# AG-VK-003: 分离与真态射判别

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 7, 8, 11: 概形理论 |
| **对应FOAG习题** | 7.3.F, 8.4.G, 11.1.H |
| **类型** | ANA (分析型) |
| **难度** | ⭐⭐⭐ |
| **重要性** | ★★ |

---

## 问题陈述

### 主问题

设 $f: X \to Y$ 是概形的态射。

**(a)** **分离性的赋值判别法 (Valuative Criterion)**：

证明：$f$ 是分离的当且仅当对任意离散赋值环 $R$ 及其分式域 $K$，以及任意交换图：
$$
\begin{array}{ccc}
\operatorname{Spec} K & \to & X \\
\downarrow & & \downarrow f \\
\operatorname{Spec} R & \to & Y
\end{array}
$$
存在**至多一个**提升 $\operatorname{Spec} R \to X$ 使得图交换。

**(b)** **固有性的赋值判别法**：

证明：$f$ 是固有的（proper）当且仅当
1. $f$ 是分离的
2. 对任意如上的交换图，存在**恰好一个**提升

**(c)** **应用**：证明：
- 仿射空间的态射 $\mathbb{A}^2 \to \mathbb{A}^1$ 是分离的但不是固有的
- 射影空间的态射 $\mathbb{P}^1 \to \operatorname{Spec} k$ 是固有的

---

## 解题思路

### 思路概述

本题涉及概形理论的**核心概念**：
- **分离性**：类比Hausdorff条件
- **固有性**：类比紧性
- **赋值判别法**：代数几何独特的判别工具

### 几何直观

```
分离性的几何意义

Hausdorff空间:        分离概形:
任意两点有            对角线 Δ: X → X ×_Y X
不相交的开邻域        是闭浸入
                      
直观: 极限唯一        直观: 赋值环的"极限点"
                      提升到 X 的方式唯一
```

```
固有性的几何意义

紧空间:               固有态射:
闭集映到闭集          泛闭的 (universally closed)
+局部紧              +分离的+有限型

直观: 序列有聚点      直观: 赋值环的提升
                      必然存在
```

---

## 详细解答

### (a) 分离性的赋值判别法

**定理**（Valuative Criterion for Separatedness）：

$f: X \to Y$ 是分离的 $\Leftrightarrow$ 赋值环提升至多一个。

**证明概要**：

**$(\Rightarrow)$** 设 $f$ 分离，给定交换图：

$$
\begin{array}{ccc}
\operatorname{Spec} K & \xrightarrow{g} & X \\
\downarrow & & \downarrow f \\
\operatorname{Spec} R & \xrightarrow{h} & Y
\end{array}
$$

两个提升 $g_1, g_2: \operatorname{Spec} R \to X$ 给出：

$$(g_1, g_2): \operatorname{Spec} R \to X \times_Y X$$

对角线 $\Delta: X \to X \times_Y X$ 是闭浸入（分离性定义）。

$g_1|_{\operatorname{Spec} K} = g_2|_{\operatorname{Spec} K} = g$，所以 $(g_1, g_2)$ 在一般点与 $\Delta$ 相交。

$\Delta(X)$ 是闭集，其原像在 $\operatorname{Spec} R$ 中是包含一般点的闭集，故是整个空间。

因此 $g_1 = g_2$。

**$(\Leftarrow)$** 需要证明对角线 $\Delta(X) \subset X \times_Y X$ 是闭集。

设 $z \in \overline{\Delta(X)} \setminus \Delta(X)$，用赋值环的存在定理构造矛盾。

（详细证明参见Hartshorne II.4或FOAG Ch 7）∎

### (b) 固有性的赋值判别法

**定理**（Valuative Criterion for Properness）：

$f$ 是固有的 $\Leftrightarrow$ 赋值环提升恰好一个。

**证明概要**：

**"恰好一个"的含义**：
- "至多一个" = 分离性
- "至少一个" = 泛闭性 + 有限型

**$(\Rightarrow)$** 固有 $\Rightarrow$ 分离（已知）+ 泛闭。

给定交换图，需要构造提升。

$(g, h): \operatorname{Spec} R \to X \times_Y Y = X$ 不太对...

实际上：构造 $Z = \overline{\{g(\xi)\}}$ 在 $X$ 中的闭包，$\xi$ 是 $\operatorname{Spec} K$ 的一般点。

由固有性，$f(Z)$ 是 $\operatorname{Spec} R$ 的闭子集，包含一般点，故等于整个空间。

在 $f^{-1}(s)$（$s$ 是 $\operatorname{Spec} R$ 的特殊点）中取一点即可得到提升。

**$(\Leftarrow)$** 需要证明泛闭性。这是赋值判别法的核心应用。

（详细证明较长，参见FOAG Ch 11）∎

### (c) 应用

**例1**: $\mathbb{A}^2 \to \mathbb{A}^1$, $(x, y) \mapsto x$

**分离性**：基底变换后仍分离（仿射态射自动分离）。

**非固有**：考虑赋值环 $R = k[t]_{(t)}$，$K = k(t)$。

图：
$$
\begin{array}{ccc}
\operatorname{Spec} k(t) & \to & \mathbb{A}^2 = \operatorname{Spec} k[x,y] \\
\downarrow & & \downarrow \\
\operatorname{Spec} R & \to & \mathbb{A}^1 = \operatorname{Spec} k[x]
\end{array}
$$

设底边的 $\operatorname{Spec} R \to \mathbb{A}^1$ 对应 $x \mapsto t$。

顶边 $\operatorname{Spec} k(t) \to \mathbb{A}^2$ 需要选择 $y$ 的像，即选择 $k(t)$ 中元素。

提升存在要求 $y$ 映到 $R$（在 $\mathbb{A}^2$ 中）。

但可以选择 $y \mapsto t^{-1} \notin R$，此时无法提升到 $\operatorname{Spec} R \to \mathbb{A}^2$。

**解释**：点 $(t, t^{-1})$ "跑向无穷远"，极限不存在。这是非固有的典型现象。

**例2**: $\mathbb{P}^1_k \to \operatorname{Spec} k$

**固有性验证**：

给定交换图：
$$
\begin{array}{ccc}
\operatorname{Spec} K & \to & \mathbb{P}^1 \\
\downarrow & & \downarrow \\
\operatorname{Spec} R & \to & \operatorname{Spec} k
\end{array}
$$

顶边给出一个 $K$-点 $[a : b] \in \mathbb{P}^1(K)$。

乘以适当单位，可设 $a, b \in R$ 且至少一个可逆。

则 $[a : b] \in \mathbb{P}^1(R)$，给出所求提升。

唯一性由分离性保证（射影态射分离）。

∎

---

## 关键概念

### 分离性 (Separatedness)

**定义**：$f: X \to Y$ 是分离的，如果对角线 $\Delta: X \to X \times_Y X$ 是闭浸入。

**类比**：拓扑空间 $X$ 是Hausdorff $\Leftrightarrow$ 对角线 $\Delta \subset X \times X$ 是闭集。

### 固有性 (Properness)

**定义**：$f: X \to Y$ 是固有的，如果：
1. 分离的
2. 有限型的
3. 泛闭的（universally closed）

**类比**：拓扑空间之间的连续映射是固有的（proper）如果紧集的原像紧。

### 赋值判别法的直观

| 条件 | 几何意义 |
|------|----------|
| 提升存在 | 极限点存在（紧性） |
| 提升唯一 | 极限唯一（Hausdorff） |

赋值环 $\operatorname{Spec} R$ 有：
- 一般点 $\xi$（开稠密）
- 特殊点 $s$（闭点）

想象：$\xi$ 是"序列"，$s$ 是"极限"。

---

## 相关结果

### 重要例子

| 态射 | 分离？ | 固有？ | 说明 |
|------|--------|--------|------|
| 仿射概形 $/Y$ | ✅ | ❌ | 一般不是固有的 |
| 射影概形 $/Y$ | ✅ | ✅ | 射影态射固有 |
| 拟仿射（非仿射） | 可能❌ | ❌ | 需具体验证 |
| 开浸入 | ❌ | ❌ | 除非也是闭浸入 |
| 闭浸入 | ✅ | ✅ | 闭浸入固有 |

### 判别法的变形

**离散赋值环版**：上述形式（最常用）。

**一般赋值环版**：对任意赋值环成立（更一般）。

**曲线版**：只需对正规曲线（$\dim = 1$）的验证。

---

## 变式练习

### 变式 1: 有限态射是固有的

证明：有限态射是固有的。

**提示**：有限 = 仿射 + 整体凝聚代数。利用赋值判别法或直接验证。

### 变式 2: 分离性的局部判别

设 $f: X \to Y$，$Y$ 有开覆盖 $\{V_i\}$。证明：$f$ 分离 $\Leftrightarrow$ 每个 $f^{-1}(V_i) \to V_i$ 分离。

### 变式 3: 非分离概形的构造

构造一个域 $k$ 上的非分离概形：取两条 $\mathbb{A}^1_k$，沿非空开子集（但不是整个空间）黏合。

---

## 常见错误

| 错误 | 纠正 |
|------|------|
| 认为仿射态射固有 | 仿射态射一般不是固有的（除非有限） |
| 混淆固有与射影 | 射影 $\Rightarrow$ 固有，但逆不对（周引理） |
| 赋值判别法的方向 | 提升是从 $\operatorname{Spec} R$ 到 $X$，不是反向 |

---

## 学习建议

1. **理解几何直观**：分离 = 极限唯一，固有 = 极限存在且唯一
2. **掌握标准例子**：$\mathbb{A}^n$ 分离非固有，$\mathbb{P}^n$ 固有
3. **练习赋值判别法**：这是代数几何独特的工具

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-003-分离与真态射判别.md`  
**创建日期**: 2026-04-10  
**最后更新**: 2026-04-10
