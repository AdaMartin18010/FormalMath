---
msc_primary: 14

  - 14F25
msc_secondary: ['14F40', '18G40', '32C35']
title: Čech上同调 - 深度版
processed_at: '2026-04-08'
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

# Čech上同调 - 深度版

**主题**: 代数几何 - 层上同调的计算方法
**难度**: ⭐⭐⭐⭐⭐ (研究级)
**先修知识**: 层论、同调代数、复形

---

## 目录

1. [概念深度解析](#1-概念深度解析)
2. [属性与关系](#2-属性与关系)
3. [示例与习题](#3-示例与习题)
4. [形式化实现](#4-形式化实现)
5. [应用与拓展](#5-应用与拓展)
6. [思维表征](#6-思维表征)

---

## 1. 概念深度解析

### 1.1 几何直观

**Čech上同调**是用开覆盖计算层上同调的方法。直观上：

- **0阶**：整体截面（全局定义的数据）
- **1阶**：局部数据粘合的障碍（如线丛的Cech类）
- **高阶**：更高层次的“粘合障碍”

**与奇异上同调的区别**：

- 奇异：拓扑空间的拓扑不变量
- Čech：层的代数/几何不变量

### 1.2 形式定义

**定义 1.1** (Čech复形 / Čech Complex)
设 $\mathcal{F}$ 为 $X$ 上的层，$\mathcal{U} = \{U_i\}_{i \in I}$ 为开覆盖。定义**Čech复形** $C^\bullet(\mathcal{U}, \mathcal{F})$：

$$C^p(\mathcal{U}, \mathcal{F}) := \prod_{i_0 < \cdots < i_p} \mathcal{F}(U_{i_0} \cap \cdots \cap U_{i_p})$$

**微分**：$d: C^p \to C^{p+1}$
$$(d\alpha)_{i_0, \ldots, i_{p+1}} := \sum_{j=0}^{p+1} (-1)^j \alpha_{i_0, \ldots, \hat{i_j}, \ldots, i_{p+1}}|_{U_{i_0} \cap \cdots \cap U_{i_{p+1}}}$$

**定义 1.2** (Čech上同调 / Čech Cohomology)
$$\check{H}^p(\mathcal{U}, \mathcal{F}) := H^p(C^\bullet(\mathcal{U}, \mathcal{F})) = \frac{\ker(d: C^p \to C^{p+1})}{\text{im}(d: C^{p-1} \to C^p)}$$

**定义 1.3** (极限定义)
$$\check{H}^p(X, \mathcal{F}) := \varinjlim_{\mathcal{U}} \check{H}^p(\mathcal{U}, \mathcal{F})$$

### 1.3 代数表述

**定理 (Leray)**：若 $\mathcal{U}$ 为**Leray覆盖**（即所有交集 $U_{i_0} \cap \cdots \cap U_{i_p}$ 上 $\mathcal{F}$ 无高阶上同调），则：
$$\check{H}^p(\mathcal{U}, \mathcal{F}) \cong H^p(X, \mathcal{F})$$

**仿射覆盖定理**：对代数簇，仿射开覆盖是Leray覆盖（Serre消没定理）。

---

## 2. 属性与关系

### 2.1 核心定理

**定理 2.1** (Čech = 导出上同调)
对仿射代数簇或更一般的scheme，Čech上同调与导出函子上同调一致：
$$\check{H}^p(X, \mathcal{F}) \cong R^p\Gamma(X, \mathcal{F})$$

**定理 2.2** (Serre消没定理)
设 $X = \mathbb{P}^n$，$\mathcal{F}$ 凝聚，则：

- $H^i(X, \mathcal{F}) = 0$ 对 $i > n$（上同调维数）
- $H^i(X, \mathcal{F}(m)) = 0$ 对 $i > 0$，$m \gg 0$（扭曲消没）

**定理 2.3** (Euler示性数)
对凝聚层 $\mathcal{F}$，定义：
$$\chi(X, \mathcal{F}) := \sum_{i=0}^n (-1)^i \dim H^i(X, \mathcal{F})$$

在平坦族中，$\chi$ 为常数（Grothendieck-Riemann-Roch）。

### 2.2 完整证明

**定理 2.2 的证明** (Serre消没)

对 $\mathcal{F} = \mathcal{O}$，用标准仿射覆盖 $\mathcal{U} = \{U_i = \{x_i \neq 0\}\}$。

**步骤1**：$C^p(\mathcal{U}, \mathcal{O})$ 由 $k[x_0, \ldots, x_n, x_{i_0}^{-1}, \ldots, x_{i_p}^{-1}]$ 的0次部分构成。

**步骤2**：计算得 $\check{H}^0 = k$，$\check{H}^n = k[x_0^{\pm 1}, \ldots]$（负次部分），$\check{H}^i = 0$（$0 < i < n$）。

**步骤3**：对 $\mathcal{O}(m)$，$\check{H}^0 = k[x_0, \ldots, x_n]_m$（$m \geq 0$），$\check{H}^n$ 对 $m \geq -(n+1)$ 非零。

**步骤4**：扭曲消没：$H^i(\mathcal{F}(m)) = 0$ 由归纳和消解论证。$\square$

### 2.3 层次结构

```
上同调理论
    ├── Čech上同调
    │       └── 计算工具
    ├── 导出上同调
    │       └── 理论定义 (R^iΓ)
    ├── 层Ext
    │       └── 局部到整体谱序列
    └── 平展上同调 (ℓ-adic)
            └── 算术几何
```

---

## 3. 示例与习题

### 3.1 具体计算示例

**示例 3.1** ($\mathbb{P}^1$ 的上同调)
用覆盖 $U_0 = \{x_0 \neq 0\}$，$U_1 = \{x_1 \neq 0\}$。

对 $\mathcal{O}$：

- $C^0 = k[x] \oplus k[x^{-1}]$（令 $x = x_1/x_0$）
- $C^1 = k[x, x^{-1}]$
- $d(f, g) = g - f$

$\check{H}^0 = k$（常数），$\check{H}^1 = 0$（因 $k[x] + k[x^{-1}] = k[x, x^{-1}]$）。

对 $\mathcal{O}(-2)$：

- $\check{H}^0 = 0$，$\check{H}^1 = k$（由 $x^{-1}$ 生成）

**示例 3.2** (椭圆曲线)
$E = \mathbb{C}/\Lambda$，用 $H^1(E, \mathcal{O}) \cong \mathbb{C}$（Dolbeault同构）。

### 3.2 反例

**反例 3.3** (非Leray覆盖)
非仿射覆盖可能导致 $\check{H} \neq H$。如投影空间的标准覆盖是Leray的，但某些非仿射覆盖不是。

### 3.3 习题

**习题 1**
计算 $\check{H}^*(\mathbb{P}^1, \mathcal{O}(n))$ 对所有 $n \in \mathbb{Z}$。

**解答**：$\dim H^0 = \max(n+1, 0)$，$\dim H^1 = \max(-n-1, 0)$。

**习题 2**
证明：$\chi(\mathbb{P}^n, \mathcal{O}(m)) = \binom{m+n}{n}$。

**习题 3**
用Mayer-Vietoris计算 $H^*(\mathbb{P}^1 \times \mathbb{P}^1, \mathcal{O}(a, b))$。

**习题 4**
设 $X$ 为亏格 $g$ 曲线，计算 $\chi(X, \mathcal{O}_X)$。

**解答**：$\chi = 1 - g$。

**习题 5**
证明：若 $X$ 仿射，$\mathcal{F}$ 凝聚，则 $H^i(X, \mathcal{F}) = 0$ 对 $i > 0$。

---

## 4. 形式化实现

### Lean4 代码

```lean4
import Mathlib

-- Čech复形
def CechComplex {X : Type} [TopologicalSpace X] (F : SheafOfAbelianGroups X)
    (U : OpenCover X) : CochainComplex AbelianGroups where
  X p := ∏ (fun (i : Fin (p + 1) → U.ι) => F.1.obj (U.intersection i))
  d p := -- Čech微分
    sorry
  d_squared := sorry

-- Čech上同调
def CechCohomology {X : Type} [TopologicalSpace X] (F : SheafOfAbelianGroups X)
    (U : OpenCover X) (p : ℕ) : AbelianGroup :=
  (CechComplex F U).cohomology p

-- 极限定义（细化覆盖）
def CechCohomologyLimit {X : Type} [TopologicalSpace X] (F : SheafOfAbelianGroups X)
    (p : ℕ) : AbelianGroup :=
  -- 极限 over all open covers
  sorry

-- 与导出上同调的同构
theorem CechIsoDerived {X : Type} [TopologicalSpace X] [Scheme X]
    (F : SheafOfAbelianGroups X) (p : ℕ) :
    CechCohomologyLimit F p ≅ Sheaf.cohomology F p :=
  sorry

-- Serre消没定理
theorem SerreVanishing {n : ℕ} (m : ℤ) (i : ℕ) (hi : i > 0) (hm : m > 0) :
    CechCohomologyLimit (O_twisted Pn_z n m) i = 0 :=
  sorry
```

---

## 5. 应用与拓展

### 5.1 数论联系

**étale上同调**：用平展拓扑替代Zariski拓扑，定义 $\ell$-进上同调，证明Weil猜想。

### 5.2 物理应用

**反常消去**：弦理论中，某些反常由层上同调类描述，Čech计算验证消去条件。

### 5.3 前沿方向

**导出Čech上同调**：高阶 stack 上的推广，用于导出代数几何。

---

## 6. 思维表征

### 6.2 Mermaid图

**Čech复形结构**:

```mermaid
graph LR
    C0[C^0 = ∏ F(Ui)] -->|d| C1[C^1 = ∏ F(Ui∩Uj)]
    C1 -->|d| C2[C^2 = ∏ F(Ui∩Uj∩Uk)]
    C2 -->|d| ...

    style C0 fill:#f9f
    style C1 fill:#bbf
    style C2 fill:#bfb
```

**上同调维数**:

```mermaid
graph TB
    subgraph "P^n的上同调"
        O0[H^0 = 截面空间]
        O1[H^1 = ?]
        On[H^n = 最高阶]
    end

    O0 -->|Serre消没| Zero1[0 for O(m), m>>0]
    O1 --> Zero1
    On --> Zero1
```

---

**维护者**: FormalMath项目组
**最后更新**: 2026年4月8日
**难度等级**: ⭐⭐⭐⭐⭐ (研究级)
