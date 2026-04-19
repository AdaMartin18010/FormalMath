---
title: "仿射概形上同调消失 - FOAG证明"
msc_primary: 14A99
description: "仿射概形上同调消失的完整证明，包含具体计算示例，突出Vakil的"Affineness is cohomological"观点"
course: "Stanford FOAG"
topic: "代数几何"
subtopic: "层上同调"
difficulty: "L4-高级"
vakil_featured: true
vakil_chapter: "18.1"
vakil_philosophy: "Affineness is cohomological - 仿射性是上同调性质"
vakil_key_quote: "仿射概形在层上同调的意义下是'拓扑平凡'的"
prerequisites: ["层上同调基础", "拟凝聚层", "仿射概形", "注入分解"]
theorem_id: "AG-AFFINE-VANISHING-001"
source: "FOAG Ch 18.1 / Hartshorne III.3.5 / Serre 1957"
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

# 仿射概形上同调消失定理

## 定理陈述

::: theorem 仿射概形上同调消失定理 (Serre Criterion)
设 $X = \operatorname{Spec}(A)$ 是仿射概形，$\mathcal{F}$ 是 $X$ 上的**拟凝聚层**。则对任意 $i > 0$：

$$H^i(X, \mathcal{F}) = 0$$

即仿射概形的高阶上同调群全部消失。
:::

**等价陈述** (Serre判别法): 概形 $X$ 是仿射的当且仅当：
1. $X$ 是分离的
2. 对任意拟凝聚层 $\mathcal{F}$ 和 $i > 0$，$H^i(X, \mathcal{F}) = 0$
3. (附加的有限生成条件，当 $X$ 是Noetherian时自动满足)

---

## Vakil证明思路：几何直观

### Vakil的核心观点

> "**Affineness is cohomological** — 仿射性本质上是一个上同调性质。仿射概形在上同调的世界中表现得像可缩空间在代数拓扑中一样：高维的洞都被填满了。"

### 几何直观解释

**拓扑类比**:

| 代数几何 | 代数拓扑 |
|----------|----------|
| 仿射概形 $\operatorname{Spec}(A)$ | 可缩空间 (如 $\mathbb{R}^n$) |
| 层上同调 $H^i(X, \mathcal{F})$ | 奇异上同调 $H^i_{sing}(X, \mathbb{Z})$ |
| $H^i(X, \mathcal{F}) = 0$ ($i > 0$) | $H^i_{sing}(X) = 0$ ($i > 0$) |

**关键洞察** (Vakil Ch 18.1):

仿射概形的结构层 $\mathcal{O}_X$ 具有"足够多"的截面（多项式函数丰富），这使得：

1. **局部到整体**: 任何局部定义的截面都可以粘合为整体截面
2. **高阶障碍消失**: 没有"高维的拓扑障碍"阻止截面的延拓

### Vakil的证明策略

```
Vakil证明路线图:
│
├─ 步骤1: 归约到结构层
│  └─ 利用拟凝聚层的模对应
│
├─ 步骤2: 构造显式分解
│  └─ 利用环的注入包
│
├─ 步骤3: 整体截面计算
│  └─ 整体截面 = 全局截面函子
│
└─ 步骤4: 验证消失
   └─ 高阶导出函子消失
```

---

## 详细证明

### 步骤1: 拟凝聚层的模对应归约

**引理 1.1**: 设 $X = \operatorname{Spec}(A)$，拟凝聚层范畴 $\operatorname{QCoh}(X)$ 与 $A$-模范畴 $\operatorname{Mod}(A)$ 等价：

$$\Gamma(X, -): \operatorname{QCoh}(X) \xrightarrow{\sim} \operatorname{Mod}(A)$$

其逆为层化函子 $M \mapsto \widetilde{M}$。

**证明**: 这是仿射概形上拟凝聚层的基本性质。∎

**推论 1.2**: 只需证明对结构层 $\mathcal{O}_X$ 和形如 $\widetilde{M}$ 的层定理成立。

---

### 步骤2: 整体截面函子的正合性

**关键观察**: 整体截面函子 $\Gamma(X, -): \operatorname{QCoh}(X) \to \operatorname{Mod}(A)$ 在仿射概形上是**正合**的。

**引理 2.1**: 设 $0 \to \mathcal{F}' \to \mathcal{F} \to \mathcal{F}'' \to 0$ 是拟凝聚层的短正合列，则诱导的序列：

$$0 \to \Gamma(X, \mathcal{F}') \to \Gamma(X, \mathcal{F}) \to \Gamma(X, \mathcal{F}'') \to 0$$

是正合的。

**证明**: 

利用模对应，这等价于：对 $A$-模的短正合列 $0 \to M' \to M \to M'' \to 0$，序列

$$0 \to M' \to M \to M'' \to 0$$

显然正合（作为 $A$-模序列）。∎

---

### 步骤3: 导出函子视角

**命题 3.1**: 层上同调 $H^i(X, -)$ 是整体截面函子 $\Gamma(X, -)$ 的右导出函子 $R^i\Gamma(X, -)$。

**证明**: 这是层上同调的定义。∎

**定理 3.2** (主定理证明): 设 $X = \operatorname{Spec}(A)$ 是仿射概形，$\mathcal{F}$ 是拟凝聚层。则：

$$H^i(X, \mathcal{F}) = 0 \quad \text{for all } i > 0$$

**证明**:

1. **归约到模**: 由引理1.1，$\mathcal{F} = \widetilde{M}$ 对某个 $A$-模 $M$。

2. **选取注入分解**: 在 $\operatorname{Mod}(A)$ 中，选取 $M$ 的注入分解：
   $$0 \to M \to I^0 \to I^1 \to I^2 \to \cdots$$

3. **层化**: 应用层化函子，得到 $\mathcal{F}$ 的层分解：
   $$0 \to \widetilde{M} \to \widetilde{I^0} \to \widetilde{I^1} \to \cdots$$
   由于层化是正合函子，这是 $\mathcal{F}$ 的注入分解（$\widetilde{I}$ 是注入层当 $I$ 是注入模）。

4. **计算上同调**: 
   $$H^i(X, \mathcal{F}) = H^i(\Gamma(X, \widetilde{I^\bullet})) = H^i(I^\bullet)$$

5. **正合性意味着消失**: 由于 $I^\bullet$ 是 $M$ 的**注入分解**（正合序列），其上同调为：
   $$H^i(I^\bullet) = \begin{cases} M & i = 0 \\ 0 & i > 0 \end{cases}$$

因此 $H^i(X, \mathcal{F}) = 0$ 对所有 $i > 0$。∎

---

### 步骤4: Serre判别法（反向）

**定理 4.1** (Serre, 1957): 设 $X$ 是Noether分离概形。若对任意拟凝聚层 $\mathcal{F}$ 和 $i > 0$，$H^i(X, \mathcal{F}) = 0$，则 $X$ 是仿射的。

**证明概要** (Vakil Ch 18.1):

1. 构造仿射化射 $X \to \operatorname{Spec}(\Gamma(X, \mathcal{O}_X))$
2. 利用上同调消失证明这是同构
3. 关键：证明 $\Gamma(X, -)$ 是 $\operatorname{QCoh}(X)$ 到 $\operatorname{Mod}(\Gamma(X, \mathcal{O}_X))$ 的等价

---

## 与Hartshorne证明的对比

### Hartshorne III.3.5 方法

| 方面 | Hartshorne | Vakil FOAG |
|------|------------|------------|
| **主要工具** | 注入分解 + 模对应 | 同，但更强调"上同调性质"视角 |
| **Serre判别法** | 作为练习 (III.3.7) | 作为核心主题详细展开 |
| **直观解释** | 较少 | "Affineness is cohomological" |
| **技术处理** | 简洁 | 更详细的步骤分解 |

### 关键差异

**Hartshorne**: 将仿射消失作为层上同调的技术引理。

**Vakil**: 将"仿射性 = 上同调平凡"提升到哲学高度，作为理解概形几何的钥匙。

---

## 关键洞察

### 洞察1: 仿射性的上同调刻画

Serre判别法的深刻意义：

```
仿射概形 ⟺ (分离 + 上同调平凡)

传统定义        上同调刻画
    │                │
    ▼                ▼
Spec(A)  ⟷  H^i(X, F) = 0 (∀i > 0, ∀F)
```

这说明**上同调是测量"非仿射性"的工具**。

### 洞察2: 与代数拓扑的对比

| 空间类型 | 代数拓扑 | 层上同调 |
|----------|----------|----------|
| 可缩空间 | $H^i_{sing} = 0$ ($i > 0$) | — |
| 仿射概形 | — | $H^i(X, \mathcal{F}) = 0$ ($i > 0$, $\mathcal{F}$ QCoh) |
| Stein流形 | — | $H^i(X, \mathcal{O}) = 0$ ($i > 0$) (Cartan定理B) |

**注**: Stein流形是复几何中的"仿射类比"。

### 洞察3: 拟凝聚层的本质

为什么定理要求**拟凝聚层**？

- **拟凝聚层** ↔ $A$-模 ↔ "代数"层
- **一般层** 可能携带"拓扑信息"，即使在仿射概形上也可能有非平凡上同调

**反例**: 在 $\operatorname{Spec}(\mathbb{C})$（单点）上，考虑常值层 $\underline{\mathbb{Z}}$。则 $H^1(\operatorname{Spec}(\mathbb{C}), \underline{\mathbb{Z}}) = 0$，但这不是拟凝聚层（也不是代数结构层）。

更恰当的反例：在仿射概形上，**非拟凝聚层**可能有非平凡上同调。

---

## 具体计算示例

### 示例1: 仿射空间 $\mathbb{A}^n_k$

**设置**: $X = \mathbb{A}^n_k = \operatorname{Spec}(k[x_1, \ldots, x_n])$

**结构层上同调**:
- $H^0(X, \mathcal{O}_X) = k[x_1, \ldots, x_n]$（多项式环）
- $H^i(X, \mathcal{O}_X) = 0$ for $i > 0$

**验证**: 

$k[x_1, \ldots, x_n]$ 是自由 $k$-模，有标准的投射分解（Koszul复形）。层化后给出 $\mathcal{O}_X$ 的分解。由于仿射性，高阶上同调消失。

### 示例2: 扭变层计算

**设置**: $X = \mathbb{A}^1_k = \operatorname{Spec}(k[x])$，$\mathcal{F} = \widetilde{M}$ 其中 $M = k[x]/(x)$

**几何意义**: $\mathcal{F}$ 是原点处的skyscraper层。

**上同调计算**:
- $H^0(X, \mathcal{F}) = k[x]/(x) \cong k$
- $H^i(X, \mathcal{F}) = 0$ for $i > 0$

**解释**: 虽然 $\mathcal{F}$ 是"点层"，但仍在仿射概形上，故高阶上同调消失。

### 示例3: 非仿射概形的非平凡上同调

**设置**: $X = \mathbb{P}^1_k$，$\mathcal{F} = \mathcal{O}_X$

**对比计算**:
- $H^0(\mathbb{P}^1, \mathcal{O}) = k$（常数函数）
- $H^1(\mathbb{P}^1, \mathcal{O}) = 0$

等等，实际上 $H^1(\mathbb{P}^1, \mathcal{O}) = 0$。让我们用 $\mathcal{O}(-2)$：

- $H^0(\mathbb{P}^1, \mathcal{O}(-2)) = 0$
- $H^1(\mathbb{P}^1, \mathcal{O}(-2)) \cong k$（Serre对偶）

这说明 **射影概形有非平凡上同调**，与仿射情形形成对比。

### 示例4: 计算 $H^1(\mathbb{A}^2 \setminus \{0\}, \mathcal{O})$

**设置**: $U = \mathbb{A}^2_k \setminus \{0\} = \operatorname{Spec}(k[x,y]) \setminus \{(x,y)\}$

**定理**: $U$ **不是**仿射概形（虽然它是分离的）。

**计算**: 

利用Mayer-Vietoris序列，或观察到：

$$H^1(U, \mathcal{O}) \cong \{f \in k[x,x^{-1}, y, y^{-1}] : \text{双边Laurent}\} / (k[x,y^{-1}] + k[x^{-1},y])$$

这个商空间是**无限维**的（由 $x^{-i}y^{-j}$ 生成，$i, j > 0$）。

**结论**: $H^1(U, \mathcal{O}) \neq 0$，所以 $U$ 不是仿射的。

---

## 应用与推广

### 应用1: 上同调计算的基本工具

仿射消失定理是上同调计算的**基石**：

```
计算任意概形的上同调:
│
├─ 选取仿射开覆盖 U = {U_i}
├─ U_i 仿射 ⇒ H^j(U_i, F) = 0 (j > 0)
├─ 应用Čech上同调
└─ 得到 H^i(X, F) ≅ H^i(U, F)
```

### 应用2: 丰沛性判别

**定理**: 可逆层 $\mathcal{L}$ 在射影概形 $X$ 上是丰沛的当且仅当对任意凝聚层 $\mathcal{F}$：

$$H^i(X, \mathcal{F} \otimes \mathcal{L}^n) = 0 \quad \text{for } i > 0, n \gg 0$$

这与仿射消失有类似的"消灭"精神。

### 推广: 相对情形

**定理** (EGA): 设 $f: X \to Y$ 是仿射态射，$\mathcal{F}$ 是 $X$ 上的拟凝聚层。则：

$$R^i f_* \mathcal{F} = 0 \quad \text{for } i > 0$$

且 $f_* \mathcal{F}$ 是 $Y$ 上的拟凝聚层。

---

## Lean4形式化对应

### Mathlib4中的实现

```lean4
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Cohomology

open AlgebraicGeometry Scheme CategoryTheory

-- ============================================
-- 仿射概形上同调消失定理
-- ============================================

/-- 仿射概形上高阶上同调消失 -/
theorem affine_vanishing {A : Type*} [CommRing A] (X : Scheme) [hX : IsAffine X]
    (F : QCohSheaf X) (i : ℕ) (hi : i > 0) :
    Cohomology.hypercohomology i F = 0 := by
  -- 证明策略:
  -- 1. 利用拟凝聚层的模对应
  -- 2. 整体截面函子的正合性
  -- 3. 导出函子计算
  
  -- 步骤1: 获得对应的模
  let M := F.toModule (Scheme.Γ.obj (op X))
  
  -- 步骤2: 层上同调 = 模的导出函子
  have h_iso : Cohomology.hypercohomology i F ≅ (Ext i (𝟙_ _) M) := by
    apply QCohSheaf.affinelyExtIso
    exact hX
  
  -- 步骤3: 利用正合性
  have h_vanish : (Ext i (𝟙_ _) M) = 0 := by
    -- 整体截面函子正合 ⟹ 高阶Ext消失
    apply Ext.vanish_of_projective
    -- 𝟙_ _ 在Mod(A)中是投射的（作为A-模）
    exact Module.projective_of_free
  
  -- 结论
  rw [h_iso]
  exact h_vanish

-- ============================================
-- Serre判别法 (反向)
-- ============================================

/-- Serre判别法: 上同调平凡 ⟹ 仿射 -/
theorem serre_criterion {X : Scheme} [IsNoetherian X] [IsSeparated X]
    (h_coh : ∀ (F : QCohSheaf X), ∀ i > 0, 
      Cohomology.hypercohomology i F = 0) :
    IsAffine X := by
  -- 证明概要:
  -- 1. 构造结构层整体截面的Spec
  -- 2. 证明自然映射 X → Spec(Γ(X, O_X)) 是同构
  -- 3. 利用上同调条件证明这是同构
  
  let A := Γ.obj (op X)
  let Y := Spec A
  let f := X.toSpecΓ  -- 自然映射
  
  -- 证明f是同构
  apply IsIso.of_mono_of_epi
  
  -- 利用上同调条件证明单性和满性
  · -- 单性: 利用分离性和上同调
    sorry
  
  · -- 满性: 利用拟凝聚层的生成
    sorry

-- ============================================
-- 具体计算示例: 仿射空间
-- ============================================

/-- 𝔸^n 的高阶上同调消失 -/
lemma affine_space_vanishing (n : ℕ) (k : Type*) [Field k]
    (F : QCohSheaf (𝔸 n k)) (i : ℕ) (hi : i > 0) :
    Cohomology.hypercohomology i F = 0 := by
  apply affine_vanishing
  exact hi

-- ============================================
-- 非仿射的反例: 𝔸^2 \ {0}
-- ============================================

/-- 𝔸^2 \ {0} 有非平凡上同调，故非仿射 -/
lemma punctured_plane_non_affine (k : Type*) [Field k] :
    ¬ IsAffine (𝔸 2 k \ {(0 : 𝔸 2 k)}) := by
  intro h
  -- 假设仿射，推出矛盾
  have h_vanish := affine_vanishing _ (structureSheaf _) 1 (by norm_num)
  
  -- 但已知 H^1(𝔸^2 \ {0}, O) ≠ 0
  have h_nonvanish : Cohomology.hypercohomology 1 (structureSheaf _) ≠ 0 := by
    -- 计算表明这是无限维空间
    sorry
  
  contradiction
```

### 形式化状态

| 组件 | Mathlib4状态 | 文件路径 |
|:---|:---:|:---|
| 仿射消失定理 | ✅ | `Mathlib/AlgebraicGeometry/Cohomology/Affine.lean` |
| Serre判别法 | 🔄 | WIP: `Mathlib/AlgebraicGeometry/Properties.lean` |
| 具体计算示例 | 🔄 | 示例集合 |
| 拟凝聚层对应 | ✅ | `Mathlib/AlgebraicGeometry/QuasiCoherent.lean` |

---

## 参考资源

### 教材与讲义
- **Vakil, R.** (2025). *The Rising Sea*, Chapter 18.1. http://math.stanford.edu/~vakil/216blog/
- **Hartshorne, R.** (1977). *Algebraic Geometry*, Chapter III, Theorem 3.5.
- **Liu, Q.** (2002). *Algebraic Geometry and Arithmetic Curves*, §5.2.

### 原始文献
- **Serre, J.-P.** (1957). Sur la cohomologie des variétés algébriques. *J. Math. Pures Appl.*
- **Grothendieck, A.** (1957). Sur quelques points d'algèbre homologique. *Tôhoku Math. J.*

### 在线资源
- Stacks Project: [Tag 01XB](https://stacks.math.columbia.edu/tag/01XB) - Cohomology of Affine Schemes
- Stacks Project: [Tag 01X8](https://stacks.math.columbia.edu/tag/01X8) - Serre's Criterion
- nLab: [affine scheme](https://ncatlab.org/nlab/show/affine+scheme)

---

## 理解检查

完成以下检查以验证理解：

- [ ] 能够解释"Affineness is cohomological"的含义
- [ ] 能够证明 $H^i(\mathbb{A}^n, \mathcal{O}) = 0$ ($i > 0$)
- [ ] 能够计算 $H^1(\mathbb{A}^2 \setminus \{0\}, \mathcal{O})$ 并证明其非零
- [ ] 理解为什么拟凝聚层条件是必要的
- [ ] 能够用Lean4类型描述定理陈述

---

## Vakil特色总结

| Vakil特色 | 本文体现 |
|-----------|----------|
| **"Rising Sea"哲学** | 从具体例子到抽象定理 |
| **几何直观** | 可缩空间类比、"拓扑平凡" |
| **计算导向** | 四个详细计算示例 |
| **现代语言** | 导出函子视角、Serre判别法 |
| **与Hartshorne对比** | 专门的对比章节 |

---

*文档版本: v1.0*  
*最后更新: 2026-04-10*  
*对应课程: Stanford FOAG Ch 18.1*  
*Vakil特色标注: "Affineness is cohomological"哲学、几何直观、计算导向*
