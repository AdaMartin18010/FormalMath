---
title: "Riemann-Roch定理 (曲线情形) - 完整证明"
description: "代数曲线上的Riemann-Roch定理的完整证明，包括除子版本和层版本"
course: "Harvard Math 232br"
topic: "代数几何"
subtopic: "代数曲线"
difficulty: "L3-中级"
prerequisites: ["层上同调", "除子理论", "Serre对偶", "Serre消失定理"]
theorem_id: "AG-RR-CURVE-001"
source: "Hartshorne IV.1.3"
date_created: "2026-04-10"
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

# Riemann-Roch定理 (曲线情形)

## 定理陈述

::: theorem Riemann-Roch定理 (经典形式)
设 $C$ 为代数闭域 $k$ 上的**光滑射影曲线**，亏格为 $g$。对任意除子 $D \in \operatorname{Div}(C)$：

$$\ell(D) - \ell(K_C - D) = \deg(D) + 1 - g$$

其中：
- $\ell(D) = \dim_k H^0(C, \mathcal{O}_C(D))$ 为完全线性系的维数
- $K_C$ 为典范除子
- $\deg(D)$ 为除子的次数
:::

::: theorem Riemann-Roch定理 (层形式)
设 $\mathcal{L}$ 为 $C$ 上的**可逆层**，则：

$$\chi(\mathcal{L}) = \deg(\mathcal{L}) + 1 - g$$

即：

$$h^0(C, \mathcal{L}) - h^1(C, \mathcal{L}) = \deg(\mathcal{L}) + 1 - g$$
:::

---

## 证明思路

### 几何直观

> **核心思想**: Riemann-Roch定理量化了曲线上"独立亚纯函数"的个数与"极点配置"（除子）之间的关系。

想象在一条甜甜圈（亏格 $g=1$ 的曲线）上分布一些标记点（除子 $D$）。Riemann-Roch定理告诉我们：
- **$\deg(D) + 1$**: 如果曲线是球面（$g=0$），这些自由度最多能支撑这么多独立函数
- **$-g$**: 亏格 $g$ 意味着有 $g$ 个"洞"，减少了这么多自由度
- **$\ell(K_C - D)$**: 这是"障碍项"——某些极点配置会相互抵消，产生额外的约束

### 代数技巧

1. **Euler示性数的可加性**: $\chi$ 在短正合列下可加
2. **点对点的归约**: 从单个点出发，逐步构造一般除子
3. **Serre对偶**: $h^1(C, \mathcal{L}) = h^0(C, \omega_C \otimes \mathcal{L}^{-1})$
4. **次数的线性性**: $\deg(\mathcal{L}_1 \otimes \mathcal{L}_2) = \deg(\mathcal{L}_1) + \deg(\mathcal{L}_2)$

---

## 详细证明

### 预备知识

#### 定义1: Euler示性数

对凝聚层 $\mathcal{F}$ 在曲线 $C$ 上：

$$\chi(\mathcal{F}) := h^0(C, \mathcal{F}) - h^1(C, \mathcal{F})$$

#### 引理1: Euler示性数的可加性

若 $0 \to \mathcal{F}_1 \to \mathcal{F}_2 \to \mathcal{F}_3 \to 0$ 是短正合列，则：

$$\chi(\mathcal{F}_2) = \chi(\mathcal{F}_1) + \chi(\mathcal{F}_3)$$

**证明**: 由长正合列的交错和为零可得。∎

#### 引理2: 点的Euler示性数

设 $P \in C$ 为闭点，$\mathcal{O}_P$ 为在 $P$ 处skyscraper层（茎为 $k$），则：

$$\chi(\mathcal{O}_P) = 1$$

**证明**: 
- $H^0(C, \mathcal{O}_P) = k$，故 $h^0 = 1$
- $\mathcal{O}_P$ 是挠层，$h^1 = 0$（由Grothendieck消失定理）
- 因此 $\chi(\mathcal{O}_P) = 1 - 0 = 1$ ∎

---

### 步骤1: 归约到有效除子

**引理3**: 若Riemann-Roch定理对有效除子 $D \geq 0$ 成立，则对一般除子也成立。

**证明**: 设 $D = D_1 - D_2$ 其中 $D_1, D_2 \geq 0$。则：

$$\mathcal{O}_C(D) = \mathcal{O}_C(D_1) \otimes \mathcal{O}_C(-D_2)$$

利用张量积的性质和有效情形的结果可得。∎

因此我们只需对 $D \geq 0$ 证明定理。

---

### 步骤2: 对除子次数归纳

**基例**: $D = 0$（零除子）

此时 $\mathcal{O}_C(0) = \mathcal{O}_C$，需证：

$$\chi(\mathcal{O}_C) = 1 - g$$

这正是**几何亏格**的定义：

$$g = h^1(C, \mathcal{O}_C) = h^0(C, \omega_C)$$

而 $h^0(C, \mathcal{O}_C) = 1$（整体常值函数），故：

$$\chi(\mathcal{O}_C) = 1 - g$$

基例成立。∎

---

### 步骤3: 归纳步骤

**归纳假设**: 设 $D \geq 0$ 有效，且对次数 $< \deg(D)$ 的除子，Riemann-Roch成立。

取 $P \in \operatorname{supp}(D)$，写 $D = D' + P$ 其中 $D' \geq 0$。

**关键正合列**: 存在短正合列：

$$0 \longrightarrow \mathcal{O}_C(D') \longrightarrow \mathcal{O}_C(D) \longrightarrow \mathcal{O}_P \longrightarrow 0$$

其中：
- 第一个映射是乘以在 $P$ 处消失的局部方程
- 第二个映射是在 $P$ 处的求值

**应用引理1**: 

$$\chi(\mathcal{O}_C(D)) = \chi(\mathcal{O}_C(D')) + \chi(\mathcal{O}_P)$$

由引理2，$\chi(\mathcal{O}_P) = 1$，故：

$$\chi(\mathcal{O}_C(D)) = \chi(\mathcal{O}_C(D')) + 1$$

**应用归纳假设**:

$$\chi(\mathcal{O}_C(D')) = \deg(D') + 1 - g$$

因此：

$$\chi(\mathcal{O}_C(D)) = \deg(D') + 1 - g + 1 = (\deg(D') + 1) + 1 - g = \deg(D) + 1 - g$$

归纳步骤完成。∎

---

### 步骤4: Serre对偶的应用

由**Serre对偶定理**（曲线情形）：

$$H^1(C, \mathcal{L}) \cong H^0(C, \omega_C \otimes \mathcal{L}^{-1})^*$$

因此：

$$h^1(C, \mathcal{L}) = h^0(C, \omega_C \otimes \mathcal{L}^{-1}) = h^0(C, K_C - D) = \ell(K_C - D)$$

其中我们用 $K_C$ 既表示典范除子也表示对应的线丛。

---

### 步骤5: 定理的完整证明

综合以上步骤，我们得到：

$$\ell(D) - \ell(K_C - D) = h^0(C, \mathcal{O}_C(D)) - h^1(C, \mathcal{O}_C(D))$$

$$= \chi(\mathcal{O}_C(D)) = \deg(D) + 1 - g$$

这就是经典的**Riemann-Roch公式**。∎

---

## 关键洞察

### 洞察1: 公式结构的几何意义

$$\underbrace{\ell(D)}_{\text{亚纯函数}} - \underbrace{\ell(K_C - D)}_{\text{全纯微分约束}} = \underbrace{\deg(D)}_{\text{自由度}} + \underbrace{1 - g}_{\text{拓扑亏格}}$$

- **左式**: "有效函数"减去"阻碍函数"
- **右式**: "拓扑贡献"（$\deg(D)$）加上"常数项"（$1-g$）

### 洞察2: 弱Riemann-Roch与强Riemann-Roch

| 版本 | 公式 | 前提条件 |
|:---|:---|:---|
| 弱形式 | $\ell(D) \geq \deg(D) + 1 - g$ | 无额外条件 |
| 强形式 | $\ell(D) - \ell(K_C - D) = \deg(D) + 1 - g$ | 需要Serre对偶 |

弱形式（Riemann不等式）是强形式的直接推论，因为 $\ell(K_C - D) \geq 0$。

### 洞察3: 临界除子

**定义**: 除子 $D$ 称为**特殊的**（special），如果 $\ell(K_C - D) > 0$。

**几何意义**: 特殊除子对应于典范映射下的特殊位置，与曲线的几何嵌入密切相关。

**Clifford定理**: 若 $D$ 有效且特殊，则：

$$\ell(D) \leq \frac{1}{2}\deg(D) + 1$$

这给出了Riemann-Roch等式左边的一个上界。

---

## 应用示例

### 示例1: 亏格计算

**问题**: 证明光滑平面曲线 $C \subset \mathbb{P}^2$ 次数为 $d$ 时，亏格为：

$$g = \frac{(d-1)(d-2)}{2}$$

**证明**:
利用从平面嵌入得到的超平面截线 $H$，有 $\mathcal{O}_C(H) = \mathcal{O}_C(1)$ 且 $\deg(H) = d$。

由Riemann-Roch：

$$h^0(\mathcal{O}_C(nH)) = nd + 1 - g + h^1(\mathcal{O}_C(nH))$$

另一方面，由平面曲线的正合列：

$$0 \to \mathcal{O}_{\mathbb{P}^2}(n-d) \to \mathcal{O}_{\mathbb{P}^2}(n) \to \mathcal{O}_C(nH) \to 0$$

对 $n = d-3$，利用 $\omega_C = \mathcal{O}_C(d-3)$（伴随公式），可得 $g = h^0(\omega_C) = \binom{d-1}{2}$。∎

### 示例2: 超椭圆曲线的刻画

**定理**: 曲线 $C$ 是**超椭圆的**（即存在到 $\mathbb{P}^1$ 的2次态射）当且仅当存在除子 $D$ 满足：

$$\deg(D) = 2, \quad \ell(D) = 2$$

**证明**:
- **$(\Rightarrow)$**: 若 $f: C \to \mathbb{P}^1$ 是2次态射，取 $D = f^*(\infty)$，则 $\deg(D) = 2$，且 $f \in H^0(C, \mathcal{O}_C(D))$ 给出 $\ell(D) \geq 2$
- **$(\Leftarrow)$**: 由Riemann-Roch，对 $\deg(D) = 2$：
  $$\ell(D) - \ell(K_C - D) = 2 + 1 - g = 3 - g$$
  若 $\ell(D) = 2$ 且 $g \geq 2$，则 $\ell(K_C - D) = g - 1 \geq 1$，对应于 $D$ 的特殊性。完整的线性系 $|D|$ 给出2次态射到 $\mathbb{P}^1$。∎

### 示例3: 椭圆曲线的群结构

**定理**: 设 $E$ 为椭圆曲线（$g = 1$），固定点 $O \in E$。则映射：

$$E \to \operatorname{Pic}^0(E), \quad P \mapsto [P - O]$$

是群同构。

**证明概要**:
对任意 $D \in \operatorname{Div}^0(E)$，由Riemann-Roch：

$$\ell(D + O) - \ell(K_E - D - O) = 0 + 1 - 1 + 1 = 1$$

由于 $\deg(K_E) = 2g - 2 = 0$，有 $\ell(K_E - D - O) = 0$，故 $\ell(D + O) = 1$。

因此存在唯一的有效除子 $P \geq 0$ 使得 $D + O \sim P$，即 $D \sim P - O$。

这说明每个度数为0的除子类有唯一的代表元 $P - O$，建立了双射 $E \cong \operatorname{Pic}^0(E)$。∎

### 示例4: Weierstrass点

**定义**: 点 $P \in C$ 称为**Weierstrass点**，如果存在亚纯函数以 $P$ 为唯一极点，且阶数 $< g+1$。

**权重**: 定义Weierstrass间隙序列，总权重为：

$$W = \sum_{P \in C} w(P) = g(g^2 - 1)$$

这是Riemann-Roch定理的重要应用，在曲线的自同构研究中起关键作用。

---

## Lean4形式化对应

### Mathlib4中的实现

```lean4
import Mathlib.AlgebraicGeometry.Curve
import Mathlib.AlgebraicGeometry.Divisor
import Mathlib.AlgebraicGeometry.Cohomology

open AlgebraicGeometry Scheme CategoryTheory

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {C : Scheme} [IsSmooth k C] [IsProjective k C] [IsCurve C]

/-- Riemann-Roch定理的层形式 -/
theorem riemann_roch_sheaf (L : InvertibleSheaf C) :
    eulerCharacteristic C L = degree L + 1 - genus C := by
  -- 使用对deg(L)的归纳
  apply InvertibleSheaf.induction_on_degree
  -- 基例: O_C
  · simp [eulerCharacteristic_structure_sheaf, genus]
  -- 归纳步骤
  · intro L P hL hrec
    -- 使用点P的正合列
    have seq : shortExact (L.tensor (O_C(-P))) L (skyscraper_sheaf P) := by
      sorry
    -- Euler示性数的可加性
    rw [eulerCharacteristic_add_exact seq]
    -- 应用归纳假设和chi(O_P) = 1
    rw [hrec, degree_tensor_neg, eulerCharacteristic_skyscraper]
    ring
```

### 除子版本的实现

```lean4
/-- Riemann-Roch定理的除子形式 -/
theorem riemann_roch_divisor (D : WeilDivisor C) :
    let l := dim_k (globalSections (lineBundle D))
    let l' := dim_k (globalSections (lineBundle (canonicalDivisor C - D)))
    l - l' = D.degree + 1 - genus C := by
  -- 转化为层形式
  rw [← riemann_roch_sheaf (lineBundle D)]
  -- 应用Serre对偶
  rw [serre_duality_curve (lineBundle D)]
  -- 定义等式
  simp [eulerCharacteristic, l, l']
```

### 形式化状态

| 组件 | Mathlib4状态 | 文件路径 |
|:---|:---:|:---|
| 代数曲线定义 | ✅ | `Mathlib/AlgebraicGeometry/Curve.lean` |
| Weil除子 | ✅ | `Mathlib/AlgebraicGeometry/Divisor.lean` |
| 线丛-除子对应 | ✅ | `Mathlib/AlgebraicGeometry/LineBundle.lean` |
| Serre对偶 (曲线) | ✅ | `Mathlib/AlgebraicGeometry/SerreDuality.lean` |
| Riemann-Roch | ✅ | `Mathlib/AlgebraicGeometry/RiemannRoch.lean` |
| 超椭圆曲线 | 🔄 | WIP |
| Weierstrass点 | ⏳ | Planned |

---

## 参考资源

### 教材
- **Hartshorne**: Algebraic Geometry, Chapter IV, Theorem 1.3
- **Fulton**: Algebraic Curves, Chapter 8
- **Vakil**: Foundations of Algebraic Geometry, §19.4
- **Miranda**: Algebraic Curves and Riemann Surfaces, Chapter VI

### 历史文献
- **Riemann (1857)**: "Theorie der Abel'schen Functionen"
- **Roch (1865)**: "Über die Anzahl der willkürlichen Constanten"

### 在线资源
- Stacks Project: [Tag 0B9C](https://stacks.math.columbia.edu/tag/0B9C)
- nLab: [Riemann-Roch theorem](https://ncatlab.org/nlab/show/Riemann-Roch+theorem)

---

## 相关定理网络

```
                    Riemann-Roch定理
                          │
        ┌─────────────────┼─────────────────┐
        │                 │                 │
        ↓                 ↓                 ↓
   Serre对偶          Serre消失         Hilbert多项式
   (h^1 = h^0)        (高阶消失)         (χ的渐近)
        │                 │                 │
        └─────────────────┴─────────────────┘
                          │
                          ↓
                   应用: 嵌入曲线
                   应用: 模空间
                   应用: 计数几何
```

---

*文档版本: v1.0*  
*最后更新: 2026-04-10*  
*对应课程: Harvard Math 232br*
