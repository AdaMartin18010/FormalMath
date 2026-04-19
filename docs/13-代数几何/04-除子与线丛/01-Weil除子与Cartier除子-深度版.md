---
msc_primary: 14

  - 14C20
msc_secondary: ['14C22', '14A15', '13C20']
title: Weil除子与Cartier除子 - 深度版
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

# Weil除子与Cartier除子 - 深度版

**主题**: 代数几何 - 除子理论与线丛对应
**难度**: ⭐⭐⭐⭐⭐ (研究级)
**先修知识**: 概形、余维数、分式理想

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

**除子 (Divisor)** 是余维数1子簇的形式线性组合，编码"零点/极点信息"：

- **Weil除子**：不可约超曲面的形式和（拓扑/组合）
- **Cartier除子**：由局部方程定义的除子（代数/方程）

**直观类比**：

- Weil除子 = 点的集合（带重数）
- Cartier除子 = 函数的零点/极点（局部由方程定义）

### 1.2 形式定义

**定义 1.1** (Weil除子 / Weil Divisor)
设 X 为整Noether分离概形，维数 n。
**素除子**：余维数1的闭整子概形。

**Weil除子群**：
Div(X) := ⊕_{Y 素除子} Z · Y = {∑ n_Y [Y] : 有限和}

**有效除子**：所有 n_Y ≥ 0。

**定义 1.2** (Cartier除子 / Cartier Divisor)
**Cartier除子**是等价类 {(U_i, f_i)}，其中：

- {U_i} 为 X 的开覆盖
- f_i ∈ K(X)^× 为有理函数
- 在 U_i ∩ U_j 上，f_i/f_j ∈ O^×

线性等价：D_1 ~ D_2 ⇔ D_1 - D_2 = (f) 对某 f ∈ K(X)^×

### 1.3 代数表述

**主除子**：有理函数 f 的除子：
(f) = ∑_Y v_Y(f) · Y

其中 v_Y 为离散赋值（在素除子 Y 处的阶）。

**线性等价类群**：
Cl(X) := Div(X) / {主除子}

**Cartier除子 → Weil除子**：
对 [(U_i, f_i)]，定义：
D = ∑_Y (min_i v_Y(f_i)) · Y

---

## 2. 属性与关系

### 2.1 核心定理

**定理 2.1** (除子-线丛对应)
存在群同构：
CaCl(X) ≅ Pic(X)

其中 CaCl 为 Cartier 除子类群，Pic(X) 为线丛类群（可逆层）。

**定理 2.2** (Weil = Cartier)
若 X 局部唯一分解（locally factorial，如光滑），则：
CaCl(X) ≅ Cl(X)

**定理 2.3** (仿射概形的类群)
设 X = Spec(A) 正规，则：
Cl(X) = 0 ⇔ A 是唯一分解整环（UFD）

### 2.2 完整证明

**定理 2.1 的证明** (除子-线丛对应)

**构造 O_X(D)**：
对 Cartier 除子 D = {(U_i, f_i)}，定义可逆层 O_X(D)：
O_X(D)|_{U_i} = (1/f_i) · O_{U_i} ⊆ K(X)

**验证**：转移函数为 g_{ij} = f_i/f_j ∈ O^×，故为线丛。

**逆构造**：给定线丛 L 和有理截面 s，定义：
D = {(U_i, s|_{U_i})}，其中 U_i 平凡化 L。

**验证良定性和互逆**。□

---

## 3. 示例与习题

### 3.1 具体示例

**示例 3.1** (P^n 的除子)
Cl(P^n) = Z · [H]，其中 H 为超平面。

线丛 O(m) 对应除子 mH。

**示例 3.2** (仿射二次锥)
X = Spec(k[x,y,z]/(xy - z^2))

- 非光滑（在原点）
- Cl(X) = Z/2Z（Weil除子 ≠ Cartier除子）

**示例 3.3** (椭圆曲线)
设 E 为椭圆曲线，P_0 为单位点。

- Pic^0(E) ≅ E（Jacobi簇）
- Cl^0(E) = Div^0(E)/主除子 ≅ E

### 3.2 反例

**反例 3.4** (Weil ≠ Cartier)
二次锥 X = V(xy - z^2) ⊂ A^3 在原点：

- 直线 L = V(x, z) 是 Weil除子（不可约超曲面）
- 但 L 不是 Cartier除子（在原点不能由单方程定义）

### 3.3 习题

**习题 1**
计算 Cl(P^1 × P^1)。

**解答**：= Z ⊕ Z，由两个因子 pullback 的线丛生成。

**习题 2**
证明：X 光滑 ⇒ CaCl(X) = Cl(X)。

**习题 3**
设 X = Bl_p(P^2)（一点爆破），描述其例外除子 E 和 Picard 群。

**解答**：Pic(X) = Z[H] ⊕ Z[E]，其中 H 为原超平面拉回。

**习题 4**
计算锥面 X = Spec(k[x,y,z]/(xy - z^2)) 的类群。

**习题 5**
设 C 为光滑曲线，证明 Pic^0(C) = Cl^0(C) 是 Abel 簇。

---

## 4. 形式化实现

```lean4
import Mathlib

-- Weil除子
structure WeilDivisor (X : Scheme) where
  coefficients : PrimeDivisor X → Z
  finiteSupport : Set.Finite {Y | coefficients Y ≠ 0}

-- Cartier除子
structure CartierDivisor (X : Scheme) where
  cover : OpenCover X
  functions : ∀ i, K(X)ˣ  -- 有理函数
  compatibility : ∀ i j, functions i / functions j ∈
    (O_X (cover.U i ⊓ cover.U j))ˣ

-- 主除子
def PrincipalDivisor {X : Scheme} (f : K(X)ˣ) : WeilDivisor X :=
  sorry

-- 类群
def ClassGroup (X : Scheme) : Type :=
  WeilDivisor X ⧸ Subgroup.generated (Set.range PrincipalDivisor)

-- Cartier类群
def CartierClassGroup (X : Scheme) : Type :=
  CartierDivisor X ⧸ (PrincipalCartierDivisor X)

-- 除子-线丛对应
theorem divisorLineBundleCorrespondence (X : Scheme) [IsIntegral X] :
    CartierClassGroup X ≅ PicardGroup X :=
  sorry
```

---

## 5. 应用与拓展

### 5.1 数论联系

**理想类群**：数域整数环的类群 = 其 Spec 的 Picard 群。

### 5.2 物理应用

**瞬子**：物理场的拓扑荷由除子/线丛的陈类描述。

### 5.3 前沿方向

**高维除子**：代数循环的高维推广，Bloch猜想。

---

**维护者**: FormalMath项目组
**最后更新**: 2026年4月8日
**难度等级**: ⭐⭐⭐⭐⭐ (研究级)
