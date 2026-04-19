---
title: 曲线模空间
msc_primary: 14
  - 14H10
  - 14D20
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 26-27
topic: 代数曲线模理论
exercise_type: GEO (几何型)
difficulty: ⭐⭐⭐⭐
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

# AG-VK-011: 曲线模空间

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 26-27: 曲线理论 |
| **对应FOAG习题** | 26.2.F, 27.4.C |
| **类型** | GEO (几何型) |
| **难度** | ⭐⭐⭐⭐ |
| **重要性** | ★★ |

---

## 问题陈述

### 主问题

设 $k$ 是代数闭域，特征为0。

**(a)** **$M_g$ 的存在性**：

陈述并解释 Deligne-Mumford 定理：亏格 $g \geq 2$ 的光滑射影曲线的模空间 $M_g$ 作为Deligne-Mumford叠的存在性。

**(b)** **维度计算**：

计算 $M_g$ 的维度。证明：$\dim M_g = 3g - 3$（$g \geq 2$）。

**(c)** **具体计算**：

对椭圆曲线（$g = 1$），证明 $M_1 = \mathbb{A}^1$（由 $j$-不变量参数化）。

计算亏格2曲线的模空间描述。

---

## 解题思路

### 思路概述

本题涉及**代数几何最经典的模空间之一**：
- **$M_g$的存在性** - Deligne-Mumford的里程碑工作
- **维度公式** - $3g-3$ 模数
- **低亏格情形** - 椭圆曲线、超椭圆曲线

### 模空间图景

```
曲线模空间 M_g
    │
    ├─ g = 0: 点（唯一有理曲线 P^1）
    ├─ g = 1: A^1（由j-不变量）
    ├─ g = 2: M_2 = A^3（都是超椭圆的）
    └─ g ≥ 3: 3g-3维，一般曲线非超椭圆
    
紧致化:
M_g → M̄_g（稳定曲线）
```

---

## 详细解答

### (a) Deligne-Mumford定理

**定理**（Deligne-Mumford, 1969）：

设 $g \geq 2$。函子：
$$\mathcal{M}_g: (\text{Sch}/k)^{\text{op}} \to \text{Groupoids}$$
$$S \mapsto \{\text{光滑曲线 } C \to S \text{ 亏格 } g\}$$

是Deligne-Mumford叠。

作为粗模空间，$M_g$ 是拟射影概形（由Mumford）。

**解释**：

**为什么是叠？**

曲线可能有非平凡自同构（如超椭圆对合、Weierstrass点）。

这些自同构阻碍精细模空间的存在。

**Deligne-Mumford叠的性质**：

1. **对角线 $\Delta: \mathcal{M}_g \to \mathcal{M}_g \times \mathcal{M}_g$ 是固有的**

2. **存在étale atlas**：存在概形 $U$ 和光滑满射 $U \to \mathcal{M}_g$

   实际上，取Hilbert概形中的光滑曲线子集。

3. **几何点的同构类**：$\mathcal{M}_g(k)/\cong = \{\text{亏格}g\text{曲线}\}/\text{同构}$

**稳定曲线的紧致化**（Deligne-Mumford）：

$$\overline{\mathcal{M}}_g \supset \mathcal{M}_g$$

参数化**稳定曲线**：只有节点奇点，有限自同构群。

$\overline{\mathcal{M}}_g$ 是固有Deligne-Mumford叠。∎

### (b) 维度计算

**定理**：$\dim M_g = 3g - 3$（$g \geq 2$）。

**证明**：

**步骤1**: 形变理论。

曲线 $C$ 的一阶形变由 $H^1(C, T_C)$ 分类。

**步骤2**: 计算 $h^1(T_C)$。

由Serre对偶：
$$h^1(T_C) = h^0(T_C^\vee \otimes K_C) = h^0(K_C^{\otimes 2})$$

因为 $T_C^\vee = \Omega_C^1 = K_C$。

**步骤3**: 计算 $h^0(K_C^{\otimes 2})$。

由Riemann-Roch：
$$h^0(K_C^{\otimes 2}) - h^1(K_C^{\otimes 2}) = \deg(2K) + 1 - g = 4g - 4 + 1 - g = 3g - 3$$

由Serre对偶：$h^1(K_C^{\otimes 2}) = h^0(K_C^{\otimes (-1)}) = 0$（$g \geq 2$，负次数线丛无整体截面）。

所以：$h^0(K_C^{\otimes 2}) = 3g - 3$。

**步骤4**: 光滑性。

形变理论说 $H^2(C, T_C) = 0$（曲线维数1），所以形变无阻碍，模空间在 $[C]$ 处光滑。

所以 $M_g$ 是 $3g-3$ 维光滑叠。∎

### (c) 低亏格情形

**椭圆曲线（$g = 1$）**：

光滑射影曲线 $E$，亏格1，带单位点 $O \in E$ 构成阿贝尔群。

**Weierstrass方程**：
$$y^2 = x^3 + ax + b, \quad 4a^3 + 27b^2 \neq 0$$

**$j$-不变量**：
$$j(E) = 1728 \frac{4a^3}{4a^3 + 27b^2}$$

**定理**：
- $E \cong E'$ $\Leftrightarrow$ $j(E) = j(E')$
- $j: M_1 \xrightarrow{\sim} \mathbb{A}^1$

**注意**：$M_1$ 是粗模空间，不是叠（因为每个椭圆曲线有 $\mathbb{Z}/2$ 自同构 $P \mapsto -P$）。

实际上，$\mathcal{M}_{1,1}$（带标架）是叠，但 $M_1$ 只是概形。

**亏格2曲线**：

**定理**：每条亏格2曲线都是超椭圆的。

**证明**：由Riemann-Roch，$|K_C|$ 给出 $2:1$ 映射 $C \to \mathbb{P}^1$。

**Weierstrass形式**：
$$y^2 = f(x)$$

其中 $f$ 是6次多项式，无重根。

**模空间**：
$$M_2 \cong \{\text{二元6次型}\}/PGL_2$$

由不变量理论，这是3维拟仿射概形。

具体描述：$M_2$ 可以嵌入 $\mathbb{A}^3$，由Igusa不变量参数化。

---

## 关键概念

### 稳定曲线

**定义**：曲线 $C$ 是**稳定的**，如果：
1. 只有节点奇点（普通双重点）
2. 每条有理成分与足够多其他成分相交（自同构有限）

**稳定性条件**：对每条有理成分 $E \subset C$：
$$|E \cap \overline{C \setminus E}| + 2\cdot\text{(在}E\text{上的奇点数)} \geq 3$$

### 模数的直观

| 亏格 | 模数 | 说明 |
|------|------|------|
| 0 | 0 | 只有 $\mathbb{P}^1$ |
| 1 | 1 | $j$-不变量 |
| 2 | 3 | 都是超椭圆的 |
| $g \geq 3$ | $3g-3$ | 一般曲线非超椭圆 |

---

## 重要结果

### 一般曲线的性质

对 $M_g$ 中一般曲线 $C$（$g \geq 3$）：
- 无自同构（$\operatorname{Aut}(C) = \{1\}$）
- 非超椭圆的
- Brill-Noether数给出线丛存在性

### Brill-Noether理论

问题：在一般亏格 $g$ 曲线上，是否存在 $g_d^r$（度 $d$，维数 $r$ 的线性系）？

**期望维数**（Brill-Noether数）：
$$\rho(g, r, d) = g - (r+1)(g - d + r)$$

**定理**（Griffiths-Harris）：若 $\rho \geq 0$，则一般曲线有 $g_d^r$；若 $\rho < 0$，则没有。

---

## 变式练习

### 变式 1: $M_g$ 的Picard群

陈述Harer和Mumford关于 $\operatorname{Pic}(M_g) \otimes \mathbb{Q}$ 的结果。

### 变式 2: 超椭圆轨迹

证明超椭圆曲线构成 $M_g$ 的 $2g-1$ 维闭子簇（$g \geq 3$）。

### 变式 3: 稳定约化

陈述并解释半稳定约化定理：任何曲线族在基变换后可有稳定模型。

---

## 常见错误

| 错误 | 纠正 |
|------|------|
| 认为 $M_g$ 是精细模空间 | 只有粗模空间，叠才是精细的 |
| 忽略稳定性条件 | 紧致化需要稳定曲线条件 |
| 混淆维数公式 | $g=1$ 时公式给出0，但实际是1 |

---

## 学习建议

1. **理解叠的概念**：曲线模空间是理解叠的最佳例子
2. **研究具体计算**：低亏格情形的显式描述
3. **学习紧致化**：稳定曲线的几何

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-011-曲线模空间.md`  
**创建日期**: 2026-04-10  
**最后更新**: 2026-04-10
