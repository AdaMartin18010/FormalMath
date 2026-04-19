---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 03Q5 - Étale上同调与正向极限交换

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 03Q5 |
| **章节位置** | Chapter 59: Étale Cohomology > Section 59.51: Colimits and Étale Cohomology |
| **数学领域** | 代数几何 / Étale上同调 |
| **文档类型** | 引理 (Lemma) |
| **重要性** | ⭐⭐⭐⭐ ( Étale上同调的基础性质) |
| **相关Tags** | 03Q4, 03Q6, 03Q7 (极限与上同调系列) |

---

## 2. 定理原文

### 英文原文 (Stacks Project)

> **Lemma 59.51.3.** Let $f: X \to Y$ be a quasi-compact and quasi-separated morphism of schemes. Let $\mathcal{F} = \text{colim} \mathcal{F}_i$ be a filtered colimit of abelian sheaves on $X_{\text{étale}}$. Then for any $p \geq 0$ we have
>
> $$R^p f_* \mathcal{F} = \text{colim} R^p f_* \mathcal{F}_i$$

### 中文翻译

> **引理 59.51.3.** 设 $f: X \to Y$ 是概形的拟紧且拟分离态射。设 $\mathcal{F} = \text{colim} \mathcal{F}_i$ 是 $X_{\text{étale}}$ 上Abel层的滤过正向极限。则对任意 $p \geq 0$ 有
>
> $$R^p f_* \mathcal{F} = \text{colim} R^p f_* \mathcal{F}_i$$

---

## 3. 概念依赖图

```
Étale上同调与正向极限交换 (03Q5)
│
├── 前置概念
│   ├── 拟紧态射 (Quasi-compact Morphism)
│   ├── 拟分离态射 (Quasi-separated Morphism)
│   ├── Étale景 (Étale Site) X_étale
│   ├── Abel层 (Abelian Sheaf)
│   ├── 滤过正向极限 (Filtered Colimit)
│   └── 高阶正向像 (Higher Direct Image) R^p f_*
│
├── 关键工具
│   ├── 层化的正向极限交换
│   ├── 导出函子与正向极限
│   └── 仿射情形约化
│
├── 证明核心
│   └── 局部上同调与正向极限交换
│       └── 通过Čech上同调或导出范畴
│
└── 推论与应用
    ├── 茎的计算
    ├── 上同调与正向极限交换
    └── Noetherian逼近
```

### 依赖关系详解

| 概念 | 说明 | 在FormalMath中的位置 |
|------|------|---------------------|
| 拟紧态射 | 逆像保持拟紧性 | `concept/代数几何/拟紧态射.md` |
| 拟分离态射 | 对角线拟紧 | `concept/代数几何/拟分离态射.md` |
| Étale景 | 平展拓扑 site | `concept/代数几何/Étale拓扑.md` |
| 滤过正向极限 | 有向集上的余极限 | `concept/范畴论/正向极限.md` |
| 高阶正向像 | $R^p f_*$ 导出函子 | `concept/层论/高阶正向像.md` |

---

## 4. 证明概要

### 核心思想

证明的关键是**局部化到仿射情形**，并利用：

1. 在仿射情形下，Étale上同调可用Čech上同调计算
2. Čech上同调作为截面函子，显然与正向极限交换
3. 通过Leray谱序列将一般情形约化到仿射情形

### 详细证明步骤

**Step 1: 层化与正向极限交换**

引理：若 $\mathcal{F}_i$ 是预层的正向系统，则：

$$(\text{colim} \mathcal{F}_i)^+ = \text{colim} (\mathcal{F}_i^+)$$

其中 $(-)^+$ 表示层化。这说明Abel层范畴是Grothendieck Abel范畴，具有足够内射对象且滤过正向极限正合。

**Step 2: 仿射基情形的证明**

设 $Y = \text{Spec}(A)$ 仿射。考虑 étale 态射 $U \to Y$：

$$(R^p f_* \mathcal{F})(U) = H^p(X \times_Y U, \mathcal{F}|_{X \times_Y U})$$

由 Čech-to-导出谱序列，Čech上同调计算 étale 上同调：

$$\check{H}^p(\mathcal{V}, \mathcal{F}) \Rightarrow H^p(X \times_Y U, \mathcal{F})$$

Čech复形的每一项：

$$\check{C}^q(\mathcal{V}, \mathcal{F}) = \prod_{i_0, \ldots, i_q} \mathcal{F}(V_{i_0 \ldots i_q})$$

由于截面函子 $\Gamma(V, -)$ 与正向极限交换，Čech复形与正向极限交换。

**Step 3: 谱序列的收敛性**

需证明 Čech 谱序列的行为在取正向极限后保持良好。关键在于：

- 滤过正向极限保持正合性（在Grothendieck范畴中）
- 谱序列的 $E_2$ 页与极限交换
- 通过比较定理，导出上同调与极限交换

**Step 4: 一般情形的约化**

对于一般的拟紧拟分离态射 $f: X \to Y$：

1. 问题对 $Y$ 局部，可设 $Y$ 仿射
2. $X$ 可表示为有限个仿射开集的并
3. 用Mayer-Vietoris序列和归纳法
4. 或用Leray谱序列约化到仿射源情形

∎

### 关键引理依赖

| 引理 | Tag | 作用 |
|------|-----|------|
| 正向极限与茎交换 | 03Q4 | 层水平的基础 |
| 拟紧拟分离态射的性质 | 03KW | 约化到仿射情形 |
| Čech-to-导出 | 03Q2 | 计算工具 |

---

## 5. 与FormalMath的对应关系

### FormalMath相关文档

| 文档路径 | 内容对应 | 完成状态 |
|----------|----------|----------|
| `concept/代数几何/拟紧态射.md` | 基本概念 | ✅ 已完成 |
| `concept/代数几何/拟分离态射.md` | 基本概念 | ✅ 已完成 |
| `concept/代数几何/Étale拓扑.md` | Étale景理论 | 🚧 部分完成 |
| `concept/层论/高阶正向像.md` | 导出函子 | 🚧 部分完成 |
| `concept/代数几何/Étale上同调.md` | 综合理论 | 🚧 进行中 |

### 概念映射

```yaml
Stacks Project Tag: 03Q5
FormalMath概念:
  - path: "concept/代数几何/Étale上同调.md"
    sections:
      - "与正向极限的交换性"
      - "高阶正向像的性质"
    relation: "核心定理"
  
  - path: "concept/范畴论/Grothendieck范畴.md"
    relation: "理论基础 (滤过余极限正合)"
  
  - path: "concept/层论/Čech上同调.md"
    relation: "证明工具"
```

---

## 6. 应用与重要性

### 核心应用

#### 1. 茎的计算

对于几何点 $\bar{y}: \text{Spec}(k^{sep}) \to Y$：

$$(R^p f_* \mathcal{F})_{\bar{y}} = H^p(X \times_Y \text{Spec}(\mathcal{O}_{Y,\bar{y}}^{sh}), \mathcal{F})$$

利用正向极限交换性，可将计算约化到有限型情形。

#### 2. Noetherian逼近

设 $X = \lim X_i$ 是有限呈現概形的逆向极限，则：

$$H^p_{\text{ét}}(X, \mathcal{F}) = \text{colim} H^p_{\text{ét}}(X_i, \mathcal{F}_i)$$

这在约化一般问题到Noetherian情形时至关重要。

#### 3. 可构造层的上同调

可构造层是有限局部常值层的正向极限，因此：

| 应用 | 说明 |
|------|------|
| 上积理论 | 用有限层逼近 |
| Poincaré对偶 | 一般情形从有限层推出 |
| Lefschetz不动点 | 迹公式的证明 |

### 重要性评估

| 方面 | 重要性 |
|------|--------|
| 理论架构 | Grothendieck范畴性质的直接应用 |
| 计算方法 | 将问题约化到有限/Noetherian情形 |
| 算术几何 | 与绝对Galois群上同调的联系 |
| 动机理论 | ℓ进层的理论基础 |

---

## 7. 与其他资源的关联

### nLab 对应条目

| nLab页面 | URL | 对应内容 |
|----------|-----|----------|
| étale cohomology | https://ncatlab.org/nlab/show/%C3%A9tale+cohomology | 理论概述 |
| quasi-compact morphism | https://ncatlab.org/nlab/show/quasi-compact+morphism | 基础概念 |
| quasi-separated morphism | https://ncatlab.org/nlab/show/quasi-separated+morphism | 基础概念 |
| filtered colimit | https://ncatlab.org/nlab/show/filtered+colimit | 范畴论基础 |

### 经典教材与文献

| 文献 | 章节 | 特色 |
|------|------|------|
| Milne's *Étale Cohomology* | Chapter III, Lemma 1.15 | 标准参考 |
| SGA 4 | Exposé VII | 原始来源 |
| Freitag-Kiehl | Chapter I, §2 | 较现代的表述 |
| Tamme | Chapter II, §3 | 教材风格 |

### Milne的处理 (标准参考)

在Milne的《Étale Cohomology》中，此结果表述为：

> 若 $f: X \to Y$ 是拟紧拟分离的，则 $R^p f_*$ 与滤过正向极限交换。

证明使用 Čech 上同调和层的极限行为。

---

## 8. Lean4形式化展望

### 当前形式化状态

| 项目 | 状态 | 说明 |
|------|------|------|
| mathlib4 (Étale Cohomology) | ❌ 早期规划 | 基础景理论存在 |
| mathlib4 (Grothendieck Topos) | 🚧 进行中 | 层理论框架 |
| **具体本Tag** | ❌ 未开始 | 依赖大量基础 |

### 形式化挑战

Étale上同调的形式化面临巨大挑战：

| 挑战 | 难度 | 说明 |
|------|------|------|
| Étale景的构造 | ⭐⭐⭐⭐ | 需要良好的 site 理论 |
| 层化函子 | ⭐⭐⭐⭐ | Grothendieck topos 理论 |
| 导出函子 | ⭐⭐⭐⭐⭐ | 高阶导出范畴 |
| 极限交换 | ⭐⭐⭐⭐ | 需要Grothendieck范畴API |
| 仿射态射的上同调 | ⭐⭐⭐⭐⭐ | Galois上同调的联系 |

### 推荐形式化路线图

#### 阶段1：基础景理论 (2-3年)
- [ ] Grothendieck拓扑的完整形式化
- [ ] 层范畴作为Grothendieck topos
- [ ] 景的态射与像函子

#### 阶段2：Étale景 (2-3年)
- [ ] Étale态射的定义与性质
- [ ] Étale site的构造
- [ ] 几何点的stalk理论

#### 阶段3：上同调 (3-5年)
- [ ] 层上同调的导出函子定义
- [ ] Čech上同调理论
- [ ] 比较定理

#### 阶段4：高级性质 (3-5年)
- [ ] 本Tag：极限交换性
- [ ] 紧支上同调
- [ ] 平滑基变换
- [ ] 纯性定理

### Lean4代码框架建议

```lean4
-- 滤过正向极限与étale上同调交换
import Mathlib.AlgebraicGeometry.EtaleTopology
import Mathlib.CategoryTheory.Limits.Filtered

open CategoryTheory Limits

variable {X Y : Scheme} (f : X ⟶ Y)
variable [QuasiCompact f] [QuasiSeparated f]

-- 滤过正向极限与高阶正向像交换
theorem colimits_commute_with_higher_direct_image
    {ι : Type u} [Category ι] [IsFiltered ι]
    (F : ι ⥤ (X.EtaleSite).AbelianSheaves) :
    ∀ p ≥ 0,
    let F_colim := colimit F
    RpEtaleDirectImage f p F_colim ≅ colimit (F ⋙ RpEtaleDirectImage f p) := by
  -- 证明思路：
  -- 1. 局部化到Y仿射
  -- 2. 使用Čech上同调计算
  -- 3. 利用截面函子与极限交换
  -- 4. 谱序列退化论证
  sorry

-- 特别情形：整体截面
theorem colimits_commute_with_etale_cohomology
    {ι : Type u} [Category ι] [IsFiltered ι]
    (F : ι ⥤ (X.EtaleSite).AbelianSheaves) :
    ∀ p ≥ 0,
    EtaleCohomology p (colimit F) ≅ colimit (F ⋙ EtaleCohomology p) := by
  -- 作为f = X → Spec(Z)的特例
  sorry
```

### 相关项目参考

- **UniMath (Coq):** 有部分层论和景理论
- **HoTT/UF:** 高阶拓扑视角的上同调
- **Liquid Tensor Experiment:** 展示了复杂同调代数的形式化可能

---

## 参考链接

- **Stacks Project Tag 03Q5:** https://stacks.math.columbia.edu/tag/03Q5
- **Milne's Étale Cohomology:** https://www.jmilne.org/math/Books/EC.pdf
- **SGA 4:** https://arxiv.org/abs/math/0206203 (半公开版本)
- **nLab - Étale Cohomology:** https://ncatlab.org/nlab/show/%C3%A9tale+cohomology

---

*文档创建日期：2026年4月*  
*FormalMath Stacks Project Tag解读系列*
