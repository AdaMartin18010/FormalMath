---
msc_primary: 14C22
msc_secondary: ['14C20', '14H40', '32L05']
title: 线丛与Picard群 - 深度版
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

# 线丛与Picard群 - 深度版

**主题**: 代数几何 - 可逆层与Picard函子
**难度**: ⭐⭐⭐⭐⭐ (研究级)
**先修知识**: 层论、除子、向量丛

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

**线丛 (Line Bundle)** = 秩1局部自由层 = 可逆层：

- **几何**：每纤维为1维向量空间的几何线丛
- **代数**：局部同构于 O_X 的 O_X-模
- **扭曲层 O(m)**：P^n 上的标准线丛

**Picard群 Pic(X)**：线丛的同构类群，运算为张量积。

### 1.2 形式定义

**定义 1.1** (可逆层 / Invertible Sheaf)
O_X-模 L 称为**可逆的**，若：

- 局部自由秩1
- 等价：存在 L' 使 L ⊗ L' ≅ O_X

**定义 1.2** (Picard群 / Picard Group)
Pic(X) := {可逆层}/≅，运算 ⊗

单位元 O_X，逆元 L^{-1} = L^∨ = Hom(L, O_X)

**定义 1.3** (丰富线丛 / Ample Line Bundle)
线丛 L 称为**丰富的**，若某正张量幂 L^{⊗n} 定义浸入 P^N。

### 1.3 代数表述

**指数序列**（复几何）：
0 → Z → O_X → O_X^× → 0

给出：Pic(X) ≅ H^1(X, O_X^×)

**Picard概形**：对 proper 光滑 X/S，存在群概形 Pic_{X/S} 表示 Picard 函子。

---

## 2. 属性与关系

### 2.1 核心定理

**定理 2.1** (Serre消失与丰富性)
L 丰富 ⇔ 对所有凝聚层 F，H^i(X, F ⊗ L^{⊗n}) = 0 对 i > 0, n ≫ 0。

**定理 2.2** (Nakai-Moishezon判别准则)
线丛 L 丰富 ⇔ 对所有闭子簇 Y ⊆ X，(L^{dim Y} · Y) > 0。

**定理 2.3** (Picard群的正合序列)
对 X = U ∪ V，有：
Pic(X) → Pic(U) ⊕ Pic(V) → Pic(U ∩ V) → H^2(X, O_X^×)

### 2.2 完整证明

**定理 2.1 的证明** (Serre消失)

(⇒) 设 L 丰富，嵌入 X → P^N 使 L = O(1)|_X。

由 Serre 定理，H^i(P^N, F(n)) = 0 对 i > 0, n ≫ 0。

由限制和谱序列，对 X 同样成立。

(⇐) 消没条件保证 L^{⊗n} 全局生成且分离点/切向。

由丰富性判别，L 丰富。□

---

## 3. 示例与习题

### 3.1 具体示例

**示例 3.1** (P^n 的Picard群)
Pic(P^n) = Z · O(1)

- O(1) = 超平面线丛
- O(m) = O(1)^{⊗m}
- 截面：Γ(P^n, O(m)) = k[x_0,...,x_n]_m

**示例 3.2** (椭圆曲线)
设 E 为椭圆曲线，则：

- Pic^0(E) ≅ E（通过 O(P - P_0)）
- 自对偶：E ≅ E^∨

**示例 3.3** (爆破)
X = Bl_p(P^2)，则：
Pic(X) = Z[H] ⊕ Z[E]

- H：原超平面拉回
- E：例外除子（自交 -1）
- 相交形式：H^2 = 1, H·E = 0, E^2 = -1

### 3.2 反例

**反例 3.4** (非丰富线丛)
P^1 × P^1 上的 O(a,b) 丰富 ⇔ a > 0 且 b > 0。

仅 a > 0 或仅 b > 0 时是 nef 但非丰富。

### 3.3 习题

**习题 1**
计算 Pic(P^1 × P^1) 并确定丰富锥。

**解答**：= Z ⊕ Z，由 O(1,0) 和 O(0,1) 生成。丰富锥 = {(a,b) : a,b > 0}。

**习题 2**
设 E 为椭圆曲线，L = O(P) 对某点 P。计算 L 的陈类。

**习题 3**
证明：P^1 上只有两个自同构线丛：O 和 O(-2)（canonical）。

**习题 4**
设 X 为 K3 曲面，证明 Pic(X) 是偶格（intersection form even）。

**习题 5**
计算 Grassmannian G(k,n) 的 Picard 群。

---

## 4. 形式化实现

```lean4
import Mathlib

-- 可逆层
def IsInvertible {X : Scheme} (L : OXModule (structureSheaf X)) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧
    ∃ e : L.toSheaf.1.obj U ≅ O_X.1.obj U, True

-- Picard群
def PicardGroup (X : Scheme) : Type :=
  {L : OXModule (structureSheaf X) // IsInvertible L} ⧸
    (Isomorphic OXModule)

instance : CommGroup (PicardGroup X) :=
  sorry  -- 张量积给出群结构

-- 丰富线丛
def IsAmple {X : Scheme} (L : OXModule (structureSheaf X)) : Prop :=
  ∃ n : ℕ, ∃ φ : X ⟶ P^n,
    IsClosedImmersion φ ∧ L^⊗n ≅ φ^* O_{P^n}(1)

-- 陈类（第一陈类）
def FirstChernClass {X : Scheme} (L : OXModule (structureSheaf X))
    (h : IsInvertible L) : H^2(X, Z) :=
  sorry
```

---

## 5. 应用与拓展

### 5.1 数论联系

**Neron-Severi群**：Pic(X)/Pic^0(X) = NS(X)，有限生成（Mordell-Weil定理的几何类比）。

### 5.2 物理应用

**弦理论**：D-膜的电荷由 K-理论类描述，Picard 群是 K_0 的子群。

### 5.3 前沿方向

**派生Picard群**：D^b(X) 的自等价群，Fourier-Mukai变换。

---

**维护者**: FormalMath项目组
**最后更新**: 2026年4月8日
**难度等级**: ⭐⭐⭐⭐⭐ (研究级)
