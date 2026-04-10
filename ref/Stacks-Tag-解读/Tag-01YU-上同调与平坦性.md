# Stacks Project Tag 01YU - 上同调与平坦性

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01YU |
| **定理名称** | 上同调与平坦性 (Cohomology and Flatness) |
| **所属章节** | Section 30.7 - Cohomology and Flatness (Divisors) |
| **数学领域** | 代数几何、同调代数、交换代数 |
| **Stacks Project链接** | https://stacks.math.columbia.edu/tag/01YU |

## 2. 定理/定义原文

**定理 (Tag 01YU):**

设 $f: X \to S$ 是概形的真态射，$\mathcal{F}$ 是 $X$ 上的凝聚层，且 $\mathcal{F}$ 在 $S$ 上平坦。则：

**(1)** 高直像层 $R^p f_* \mathcal{F}$ 是 $S$ 上的凝聚层。

**(2)** **形成性 (Formation):** 对任意基变换图：
$$
\xymatrix{
X' \ar[r]^{g'} \ar[d]_{f'} & X \ar[d]^f \\
S' \ar[r]^g & S
}
$$
有典范同构：
$$g^* R^p f_* \mathcal{F} \;\xrightarrow{\;\cong\;}\; R^p f'_* (g')^* \mathcal{F}$$

（即使 $g$ 不平坦，此同构也成立！）

**(3)** **半连续性:** 函数 $s \mapsto \dim_{\kappa(s)} H^p(X_s, \mathcal{F}_s)$ 是上半连续的。

## 3. 概念依赖图

```
上同调与平坦性 (Tag 01YU)
│
├── 核心前置概念
│   ├── 真态射 (Tag 01W6)
│   ├── 凝聚层 (Tag 01BU)
│   ├── 层的平坦性 (Tag 01U9)
│   ├── 高直像 R^pf_* (Tag 01E4)
│   └── 纤维上同调 (Tag 01XX)
│
├── 关键技术
│   ├── 上同调有限性 (Tag 02O6)
│   ├── 基变换映射 (Tag 01YB)
│   ├── 形式函数定理 (Tag 01YC)
│   └── Nakayama引理 (Tag 00DV)
│
├── 导出范畴
│   ├── 导出像 Rf_* (Tag 06YZ)
│   └── 完美复形 (Tag 08FT)
│
└── 后继应用
    ├── 半连续性定理 (Tag 0CCM)
    ├── Hilbert多项式
    └── 模空间的构造
```

## 4. 证明概要

**证明策略:**

**Step 1: 凝聚性证明**
- 利用真态射的上同调有限性定理 (Tag 02O6)
- $R^p f_* \mathcal{F}$ 是凝聚的（无需平坦性假设！）

**Step 2: 形成性证明（核心）**

**关键观察:** 当 $\mathcal{F}$ 在 $S$ 上平坦时：

**引理:** 纤维上的上同调计算可"交换":
$$H^p(X_s, \mathcal{F}_s) = (R^p f_* \mathcal{F})_s \otimes_{\mathcal{O}_{S,s}} \kappa(s)$$

**证明:**
1. 利用形式函数定理 (Tag 01YC)
2. 平坦性保证完备化与张量积的兼容性
3. 基变换映射在完备化层面是同构
4. Nakayama引理推出原映射是同构

**Step 3: 半连续性**
- 由形成性和上同调的有限性
- 利用Nakayama引理的维数估计
- 证明函数的上半连续性

**技术要点:**

**关键引理 (局部判别):**
设 $S = \text{Spec}(A)$，$\mathfrak{p} \in \text{Spec}(A)$，则：
$$\dim_{k(\mathfrak{p})} H^p(X_{\mathfrak{p}}, \mathcal{F}_{\mathfrak{p}}) \leq r$$
当且仅当存在 $f \in A \setminus \mathfrak{p}$ 使得 $H^p(X_f, \mathcal{F}_f)$ 可由 $r$ 个元素生成。

## 5. 与FormalMath对应

| Stacks Project概念 | FormalMath对应内容 | 文档路径 |
|-------------------|-------------------|----------|
| 真态射 | 代数几何/真态射 | `concept/algebraic_geometry/proper_morphism.md` |
| 凝聚层 | 代数几何/凝聚层 | `concept/algebraic_geometry/coherent_sheaf.md` |
| 层的平坦性 | 代数几何/平坦态射 | `concept/algebraic_geometry/flat_morphism.md` |
| 上同调有限性 | 代数几何/层上同调 | `concept/algebraic_geometry/cohomology_finiteness.md` |

**当前对齐状态:**
- 🟡 **部分对齐** - 各组件概念存在，但完整定理及其证明待补充

**建议补充内容:**
```markdown
## 上同调与平坦性详解

### 定理陈述
设 $f: X \to S$ 真，$\mathcal{F}$ 凝聚且在 $S$ 上平坦：

1. **凝聚性:** $R^p f_* \mathcal{F}$ 凝聚
2. **形成性:** 对任意基变换，$g^* R^p f_* \mathcal{F} \cong R^p f'_* (g')^* \mathcal{F}$
3. **半连续性:** $\dim H^p(X_s, \mathcal{F}_s)$ 上半连续

### 证明要点

**形成性的证明：**
1. 利用形式函数定理
2. 平坦性给出完备化-张量积交换
3. Nakayama引理完成

**半连续性的证明：**
1. 由形成性，$\dim H^p(X_s, \mathcal{F}_s) = \dim (R^p f_* \mathcal{F})_s \otimes \kappa(s)$
2. 利用凝聚层的局部自由判别
3. 秩函数的上半连续性

### 应用：局部自由判别
$R^p f_* \mathcal{F}$ 局部自由 $\Leftrightarrow$ $\dim H^p(X_s, \mathcal{F}_s)$ 局部常值

### 应用：Hilbert多项式
平坦族的Euler示性数恒定，Hilbert多项式稳定。
```

## 6. 应用与重要性

**核心应用场景:**

### 1. 半连续性定理 (Tag 0CCM)
- **Grauert定理:** $\dim H^p(X_s, \mathcal{F}_s)$ 的上半连续性
- 这是上同调与平坦性定理的直接推论

### 2. 局部自由判别
- **判定准则:** $R^p f_* \mathcal{F}$ 局部自由当且仅当 $\dim H^p(X_s, \mathcal{F}_s)$ 局部常值
- 这是构造Picard概形、Jacobian簇的基础

### 3. Hilbert多项式的稳定性
- 平坦族中，纤维的Hilbert多项式恒定
- Hilbert概形构造的基石

### 4. 模空间理论
- 判断何时上同调形成向量丛
- 构造各种模空间的关键工具

### 5. 形变不变量
- 某些上同调维数是形变不变量
- Kodaira维数、不规则性的研究

**重要性评级:** ⭐⭐⭐⭐⭐ (5/5)

上同调与平坦性定理是代数几何中研究概形族上同调行为的核心定理，其应用遍及模空间、形变理论、代数曲线等各个领域。

## 7. 与其他资源关联

### Stacks Project内部关联
| 相关Tag | 关联描述 |
|---------|----------|
| Tag 0CCM | 半连续性定理（直接应用） |
| Tag 01YC | 形式函数定理（证明工具） |
| Tag 01YB | 上同调与基变换 |
| Tag 02O6 | 上同调有限性定理 |
| Tag 01W6 | 真态射 |
| Tag 01U9 | 层的平坦性 |

### 外部资源

**经典文献:**
1. **Grothendieck, A.** "Éléments de Géométrie Algébrique III"
   - §7: Théorèmes de finitude et de changement de base

2. **Mumford, O.** "Abelian Varieties"
   - §5讨论上同调的半连续性

**现代教材:**
1. **Hartshorne, R.** "Algebraic Geometry"
   - 第三章§12: Semicontinuity theorem

2. **Vakil, R.** "The Rising Sea"
   - 第28章: Cohomology and base change

3. **Lazarsfeld, R.** "Positivity in Algebraic Geometry I"
   - 第一章: 上同调方法综述

**相关理论:**
- **Deformation theory:** 形变理论
- **Moduli theory:** 模空间理论
- **Hilbert schemes:** Hilbert概形

## 8. Lean4形式化展望

### 形式化难度评估: ⭐⭐⭐⭐⭐ (5/5)

**主要挑战:**
1. **上同调有限性** - 真态射的上同调有限性定理
2. **形式函数定理** - 需要完整的形式函数定理
3. **形成性的精细证明** - 涉及完备化和Nakayama引理
4. **凝聚层的局部结构** - 秩函数的分析

**Lean4实现路线:**

```lean4
-- 概念框架（设想）
import Mathlib

-- 上同调与平坦性设置
structure CohomologyFlatnessSetup where
  X S : Scheme
  f : X ⟶ S
  h_proper : Proper f
  F : CoherentSheaf X
  h_flat : FlatOver F S

-- 凝聚性定理
theorem higher_direct_image_coherent (setup : CohomologyFlatnessSetup) (p : ℕ) :
    Coherent (R p setup.f_* setup.F) := by
  sorry
  -- 需要上同调有限性定理

-- 形成性定理
theorem cohomology_formation (setup : CohomologyFlatnessSetup)
    {S' : Scheme} (g : S' ⟶ setup.S) (p : ℕ) :
    let setup' := baseChange setup g
    IsIso (baseChangeMap setup' p setup.F) := by
  sorry
  -- 需要形式函数定理和Nakayama引理

-- 半连续性定理
theorem semicontinuity (setup : CohomologyFlatnessSetup) (p : ℕ) :
    UpperSemicontinuous (fun (s : setup.S) =>
      finrank (ResidueField s) (HP p (fiber setup.f s) (pullbackSheaf setup.F s))) := by
  sorry
  -- 需要凝聚层秩函数的理论
```

**Mathlib现状:**
- 真态射的定义存在
- 凝聚层理论正在发展
- 形式函数定理缺失

**形式化优先级:** MEDIUM-HIGH
- 是高级代数几何的核心工具
- 依赖大量前置理论
- 建议在上同调有限性完成后重点推进

---

**文档编制日期:** 2026年4月  
**作者:** FormalMath项目团队  
**版本:** 1.0
