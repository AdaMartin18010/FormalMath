---
title: 算术几何应用
msc_primary: 14
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 11
topic: 算术几何与数论联系
exercise_type: NTH (数论型)
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

# AG-VK-015: 算术几何应用

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 11: 算术概形 |
| **对应FOAG习题** | 11.3.J |
| **类型** | NTH (数论型) |
| **难度** | ⭐⭐⭐⭐ |
| **重要性** | ★★ |

---

## 问题陈述

### 主问题

设 $K$ 是数域，$\mathcal{O}_K$ 是其整数环。

**(a)** **算术概形的基本构造**：

设 $X \to \operatorname{Spec} \mathbb{Z}$ 是有限型概形。解释：
1. 一般纤维 $X_\mathbb{Q} = X \times_{\operatorname{Spec} \mathbb{Z}} \operatorname{Spec} \mathbb{Q}$ 的几何意义
2. 特殊纤维 $X_{\mathbb{F}_p} = X \times_{\operatorname{Spec} \mathbb{Z}} \operatorname{Spec} \mathbb{F}_p$ 的几何意义
3. 为什么 $X$ 可以看作"在 $\mathbb{Z}$ 上变化的代数簇族"

**(b)** **椭圆曲线的算术**：

设 $E$ 是 $\mathbb{Q}$ 上的椭圆曲线，由Weierstrass方程给出：
$$y^2 = x^3 + ax + b, \quad a, b \in \mathbb{Z}, \quad 4a^3 + 27b^2 \neq 0$$

1. 定义 $E$ 的整模型（integral model）$\mathcal{E} \to \operatorname{Spec} \mathbb{Z}$
2. 解释约化模 $p$ 的过程
3. 陈述Hasse定理：$|\#E(\mathbb{F}_p) - (p + 1)| \leq 2\sqrt{p}$

**(c)** **Weil猜想（陈述）**：

设 $X$ 是 $\mathbb{F}_q$ 上的光滑射影簇，维数 $n$。定义Zeta函数：
$$Z(X, t) = \exp\left(\sum_{m=1}^\infty \frac{\#X(\mathbb{F}_{q^m})}{m} t^m\right)$$

陈述Weil猜想（现在都是定理）：
1. 有理性
2. 函数方程
3. Riemann假设的类比

---

## 解题思路

### 思路概述

本题涉及**代数几何与数论的深刻联系**：
- **算术概形** - 在整数环上的概形
- **椭圆曲线** - 算术几何的核心对象
- **Weil猜想** - 20世纪数学的里程碑

### 算术几何图景

```
算术概形 X → Spec Z
    │
    ├─ 一般纤维 X_Q: 复代数簇（几何）
    │
    └─ 特殊纤维 X_Fp: 有限域上的簇（算术）
    
联系：
    几何性质 ←────→ 算术性质
    拓扑不变量      点计数
    上同调          Zeta函数
```

---

## 详细解答

### (a) 算术概形的基本构造

**设置**：$X \to \operatorname{Spec} \mathbb{Z}$ 有限型概形。

**1. 一般纤维 $X_\mathbb{Q}$**：

$$X_\mathbb{Q} = X \times_{\operatorname{Spec} \mathbb{Z}} \operatorname{Spec} \mathbb{Q}$$

**几何意义**：
- 这是"有理"部分，对应复数域上的代数簇
- 若 $X$ 是整的，$X_\mathbb{Q}$ 是一般点上的纤维
- $X(\mathbb{C}) = X_\mathbb{Q}(\mathbb{C})$ 是复解析空间

**例子**：$X = \operatorname{Spec} \mathbb{Z}[x, y]/(y^2 - x^3 - 1)$

$X_\mathbb{Q} = \operatorname{Spec} \mathbb{Q}[x, y]/(y^2 - x^3 - 1)$ 是椭圆曲线。

**2. 特殊纤维 $X_{\mathbb{F}_p}$**：

$$X_{\mathbb{F}_p} = X \times_{\operatorname{Spec} \mathbb{Z}} \operatorname{Spec} \mathbb{F}_p$$

**几何意义**：
- 这是模 $p$ 约化
- 点对应于模 $p$ 解
- 可能奇异（即使 $X_\mathbb{Q}$ 光滑）

**例子**：同上，$X_{\mathbb{F}_p} = \operatorname{Spec} \mathbb{F}_p[x, y]/(y^2 - x^3 - 1)$

**3. 族的观点**：

$X \to \operatorname{Spec} \mathbb{Z}$ 是概形族，基底是 $\operatorname{Spec} \mathbb{Z}$（"算术直线"）。

- 一般点 $\eta = (0)$ 对应 $X_\mathbb{Q}$
- 闭点 $(p)$ 对应 $X_{\mathbb{F}_p}$

这种"变化的几何"是算术几何的核心视角。∎

### (b) 椭圆曲线的算术

**1. 整模型**：

$E: y^2 = x^3 + ax + b$，$a, b \in \mathbb{Z}$。

整模型是：
$$\mathcal{E} = \operatorname{Spec} \mathbb{Z}[x, y]/(y^2 - x^3 - ax - b) \to \operatorname{Spec} \mathbb{Z}$$

**注意**：这不是光滑的（可能有坏约化）。

**Néron模型**：存在唯一的极小平滑群概形模型（若 $E$ 是椭圆曲线）。

**2. 约化模 $p$**：

$$\mathcal{E}_{\mathbb{F}_p} = \operatorname{Spec} \mathbb{F}_p[x, y]/(y^2 - x^3 - \bar{a}x - \bar{b})$$

**约化类型**：
- **好约化**：$\Delta = -(4a^3 + 27b^2) \not\equiv 0 \pmod{p}$
  - $\mathcal{E}_{\mathbb{F}_p}$ 是椭圆曲线
- **坏约化**：$\Delta \equiv 0 \pmod{p}$
  - 乘性约化（节点）
  - 加性约化（尖点）

**3. Hasse定理**：

**定理**：$E$ 是 $\mathbb{F}_p$ 上的椭圆曲线，则：
$$|\#E(\mathbb{F}_p) - (p + 1)| \leq 2\sqrt{p}$$

等价地，设 $a_p = p + 1 - \#E(\mathbb{F}_p)$（Frobenius的迹），则 $|a_p| \leq 2\sqrt{p}$。

**意义**：椭圆曲线上的点数大致等于 $p + 1$，误差 $O(\sqrt{p})$。

这是Weil猜想（Riemann假设类比）对椭圆曲线的特例。∎

### (c) Weil猜想

**Zeta函数**：

$$Z(X, t) = \exp\left(\sum_{m=1}^\infty \frac{\#X(\mathbb{F}_{q^m})}{m} t^m\right)$$

**等价形式**：
$$Z(X, t) = \prod_{x \in X_{\text{cl}}} \frac{1}{1 - t^{\deg(x)}}$$

**Weil猜想**（Dwork, Grothendieck, Deligne证明）：

设 $X$ 是 $\mathbb{F}_q$ 上光滑射影簇，维数 $n$。

**W1. 有理性**：
$$Z(X, t) = \frac{P_1(t) P_3(t) \cdots P_{2n-1}(t)}{P_0(t) P_2(t) \cdots P_{2n}(t)}$$

其中 $P_i(t) \in \mathbb{Z}[t]$，$P_0(t) = 1 - t$，$P_{2n}(t) = 1 - q^n t$。

**W2. 函数方程**：
$$Z(X, \frac{1}{q^n t}) = \pm q^{nE/2} t^E Z(X, t)$$

其中 $E$ 是Euler示性数。

**W3. Riemann假设**：

$P_i(t) = \prod_{j=1}^{b_i} (1 - \alpha_{ij}t)$，其中 $|\alpha_{ij}| = q^{i/2}$。

**等价表述**：$Z(X, t)$ 的零点和极点在 $|t| = q^{-i/2}$ 圆上。

**W4. Betti数**（Grothendieck证明）：

若 $X$ 是特征0良好约化的特殊纤维，则 $\deg P_i = b_i(X(\mathbb{C}))$。

---

## 关键概念

### 算术几何的基本对应

| 几何概念 | 算术对应 |
|----------|----------|
| 复代数簇 $X(\mathbb{C})$ | 算术概形 $X \to \operatorname{Spec} \mathbb{Z}$ |
| 拓扑上同调 $H^i(X, \mathbb{Q})$ | étale上同调 $H^i_{\text{ét}}(X, \mathbb{Q}_\ell)$ |
| Hodge结构 | Galois表示 |
| 周期积分 | 特殊值L-函数 |

### Weil猜想的意义

1. **联系算术与拓扑**：$\#X(\mathbb{F}_{q^m})$ 由拓扑不变量（Betti数）决定
2. **Riemann假设类比**：零点在"临界线"上
3. **Grothendieck的动机**：发展了étale上同调理论

---

## 重要结果

### BSD猜想（陈述）

设 $E$ 是 $\mathbb{Q}$ 上的椭圆曲线。

**猜想**（Birch and Swinnerton-Dyer）：
$$\operatorname{rank} E(\mathbb{Q}) = \operatorname{ord}_{s=1} L(E, s)$$

其中 $L(E, s)$ 是Hasse-Weil L-函数。

---

## 变式练习

### 变式 1: Zeta函数的计算

计算 $\mathbb{P}^n_{\mathbb{F}_q}$ 的Zeta函数，验证Weil猜想。

### 变式 2: 椭圆曲线的L-函数

定义椭圆曲线 $E/\mathbb{Q}$ 的L-函数：
$$L(E, s) = \prod_p L_p(p^{-s})^{-1}$$

其中 $L_p(T) = 1 - a_p T + pT^2$（好约化）。

### 变式 3: étale上同调

陈述étale上同调的基本性质，解释其与拓扑上同调的类比。

---

## 常见错误

| 错误 | 纠正 |
|------|------|
| 认为整模型总是光滑 | 可能有坏约化 |
| 混淆Zeta函数和L-函数 | Zeta是几何的，L-函数包含算术信息 |
| 忽略特征p的特殊性 | 需要特殊处理 |

---

## 学习建议

1. **理解算术概形的几何**：把数论对象看作几何对象
2. **学习椭圆曲线**：算术几何的入门点
3. **了解Weil猜想的证明**：Grothendieck和Deligne的伟大工作

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-015-算术几何应用.md`  
**创建日期**: 2026-04-10  
**最后更新**: 2026-04-10
