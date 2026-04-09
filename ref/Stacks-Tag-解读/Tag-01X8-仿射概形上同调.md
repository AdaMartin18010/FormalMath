# Stacks Project Tag 01X8 解读：仿射概形上同调

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01X8 |
| **章节** | Schemes, Section 30.2: Čech cohomology of quasi-coherent sheaves |
| **类型** | 引理 (Lemma) |
| **重要性** | ⭐⭐⭐⭐⭐ (核心定理) |
| **Stacks Project链接** | https://stacks.math.columbia.edu/tag/01X8 |

---

## 2. 定理原文与翻译

### 英文原文

**Lemma 30.2.2 (Serre's criterion for affineness).** Let $X$ be a scheme. Assume that

1. $X$ is quasi-compact,
2. for every quasi-coherent $\mathcal{O}_X$-module $\mathcal{F}$ we have $H^1(X, \mathcal{F}) = 0$.

Then $X$ is affine.

### 中文翻译

**引理 30.2.2 (Serre仿射判别法).** 设 $X$ 是概形。假设：

1. $X$ 是拟紧的；
2. 对每个拟凝聚 $\mathcal{O}_X$-模 $\mathcal{F}$，有 $H^1(X, \mathcal{F}) = 0$。

则 $X$ 是仿射的。

**相关Tag 01X8内容**：设 $X = \text{Spec}(A)$ 是仿射概形，$\mathcal{F}$ 是 $X$ 上的拟凝聚层，则对所有 $i > 0$，有 $H^i(X, \mathcal{F}) = 0$。

---

## 3. 概念依赖图

```
Tag 01X8: 仿射概形上同调
│
├── 前置概念
│   ├── 概形 (Scheme)
│   ├── 仿射概形 (Affine Scheme)
│   │   └── Spec(A) 的构造
│   ├── 拟凝聚层 (Quasi-coherent Sheaf)
│   │   └── Tag 01LC
│   └── 层上同调 (Sheaf Cohomology)
│       └── 导出函子定义
│       └── Čech上同调
│
├── 核心定理
│   ├── Serre消失定理 (Tag 01X8)
│   │   └── 仿射概形上H^i = 0 (i>0)
│   └── Serre仿射判别法
│       └── H^1消失 + 拟紧 ⟹ 仿射
│
├── 证明技术
│   ├── Čech上同调计算
│   ├── 主开覆盖
│   ├── 局部化与极限论证
│   └── 增广Čech复形
│
└── 相关Tags
    ├── Tag 01LC: 拟凝聚层定义
    ├── Tag 01X7: Čech上同调定义
    ├── Tag 01XD: 仿射概形的上同调消失
    └── Tag 01XG: Serre判别法的证明
```

---

## 4. 证明概要

### 4.1 主要定理陈述

**定理 (Serre, 1957)**: 设 $X = \text{Spec}(A)$ 是仿射概形，$\mathcal{F}$ 是拟凝聚层，则：

$$H^i(X, \mathcal{F}) = 0 \quad \text{对所有 } i > 0$$

### 4.2 证明策略

**步骤1: 化简到Čech上同调**

利用Čech上同调与导出函子上同调的一致性（在适当条件下）。

**步骤2: 主开覆盖**

取 $X = \text{Spec}(A)$ 的有限主开覆盖 $\mathcal{U} = \{D(f_1), \ldots, D(f_n)\}$，其中 $(f_1, \ldots, f_n) = A$。

**步骤3: Čech复形**

拟凝聚层 $\mathcal{F} = \widetilde{M}$ 对应的Čech复形为：

$$\check{C}^\bullet(\mathcal{U}, \mathcal{F}) : \quad 0 \to \prod_i M_{f_i} \to \prod_{i<j} M_{f_i f_j} \to \prod_{i<j<k} M_{f_i f_j f_k} \to \cdots$$

**步骤4: 增广复形正合性**

关键观察：增广复形

$$0 \to M \to \prod_i M_{f_i} \to \prod_{i<j} M_{f_i f_j} \to \cdots$$

是正合的。这是局部化理论中的标准结果（对应于 $(f_1, \ldots, f_n) = A$ 的条件）。

**步骤5: 结论**

增广Čech复形的正合性意味着 $\check{H}^i(\mathcal{U}, \mathcal{F}) = 0$ 对 $i > 0$。

### 4.3 Serre判别法的证明思路

**给定**: 拟紧概形 $X$，$H^1(X, \mathcal{F}) = 0$ 对所有拟凝聚 $\mathcal{F}$。

**目标**: 证明 $X \cong \text{Spec}(\mathcal{O}_X(X))$。

**关键步骤**:

1. 由拟紧性，选取有限仿射开覆盖 $X = U_1 \cup \cdots \cup U_n$
2. 构造态射 $f: X \to \text{Spec}(A)$，其中 $A = \mathcal{O}_X(X)$
3. 利用 $H^1$ 消失证明 $f$ 是同构：
   - **单射性**：由分离性条件可得
   - **满射性**：利用理想层的 $H^1$ 消失
   - **局部同构**：由 $H^1$ 条件可得限制映射满射

---

## 5. 与FormalMath的对应关系

| FormalMath概念 | 对应内容 | 文档位置 |
|----------------|----------|----------|
| 层上同调 | 导出函子上同调 | `concept/层论/层上同调.md` |
| Čech上同调 | 开覆盖上的计算 | `concept/层论/Čech上同调.md` |
| 拟凝聚层 | 仿射对应 | `concept/代数几何/拟凝聚层.md` |
| 仿射概形 | Spec(A) | `concept/代数几何/仿射概形.md` |
| 局部化 | 环的局部化 | `concept/交换代数/局部化.md` |

### 学习路径

```
FormalMath: 层上同调理论
├── 前置
│   ├── 同调代数基础
│   ├── 层论基础
│   ├── 拟凝聚层
│   └── 导出函子
├── 当前 ← Tag 01X8
│   ├── 仿射概形上同调消失
│   └── Serre判别法
└── 后续
    ├── 射影空间上同调 (Tag 02O3)
    ├── Serre对偶
    └── Grothendieck消失定理
```

---

## 6. 应用与重要性

### 6.1 核心意义

Serre定理及其判别法是代数几何的基石：

| 意义 | 说明 |
|------|------|
| 刻画仿射性 | 上同调消失完全刻画仿射概形 |
| 计算工具 | 提供计算上同调的基本方法 |
| 理论框架 | 建立仿射与射影/拟射影情形的对比 |
| 判别准则 | 实践中验证概形是否仿射 |

### 6.2 与Stein空间理论的类比

| 代数几何 | 复几何 |
|----------|--------|
| 仿射概形 | Stein空间 |
| 拟凝聚层 | 凝聚解析层 |
| $H^i(X, \mathcal{F}) = 0$ ($i>0$) | Cartan定理B |
| Serre判别法 | 上同调判别Stein性 |

### 6.3 应用实例

1. **仿射性的验证**：证明特定概形是仿射的
   - 例如：$\mathbb{A}^n \setminus \{0\}$ 对 $n \geq 2$ 不是仿射的（通过计算上同调）

2. **维数理论**：
   - 若 $X$ 是 $n$ 维诺特概形，则 $H^i(X, \mathcal{F}) = 0$ 对 $i > n$（Grothendieck消失）

3. **对偶理论的基础**：Serre对偶的证明依赖于上同调消失

4. **模空间理论**：研究层上同调的形变

---

## 7. 与其他资源的关联

### 7.1 教科书对应

| 教科书 | 章节 | 内容 |
|--------|------|------|
| Hartshorne | III.3 | Cohomology of a Noetherian affine scheme |
| Liu Qing | 5.2 | Cech cohomology and Serre's criterion |
| Görtz-Wedhorn | 12 | Cohomology of sheaves |
| Vakil FOAG | 18 | Čech cohomology and Serre's criterion |
| EGA III | §1 | Cohomologie des faisceaux quasi-cohérents |

### 7.2 nLab条目

- [Serre's criterion for affineness](https://ncatlab.org/nlab/show/Serre%27s+criterion+for+affineness)
- [cohomology of a sheaf of modules](https://ncatlab.org/nlab/show/cohomology+of+a+sheaf+of+modules)
- [Čech cohomology](https://ncatlab.org/nlab/show/%C4%8Cech+cohomology)

### 7.3 原始文献

```bibtex
@article{serre1957faisceaux,
  title     = {Faisceaux alg{\'e}briques coh{\'e}rents},
  author    = {Serre, Jean-Pierre},
  journal   = {Annals of Mathematics},
  volume    = {61},
  number    = {2},
  pages     = {197--278},
  year      = {1955},
  publisher = {JSTOR}
}
```

### 7.4 相关Stacks Tags

| Tag | 内容 | 关系 |
|-----|------|------|
| 01X7 | Čech上同调定义 | 基础 |
| 01XD | 仿射概形上同调消失 | 核心结果 |
| 01XG | Serre判别法证明 | 逆方向 |
| 01Y0 | 层上同调的长正合列 | 工具 |
| 02O3 | 射影空间上同调 | 对比 |

---

## 8. Lean4形式化展望

### 8.1 Mathlib4现状

Mathlib4中相关组件：

```lean
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.CechCohomology

-- 层上同调定义（导出函子）
#check sheafCohomology

-- Čech上同调
#check chechCohomology
```

**当前状态**: 层上同调的基础定义已有，但具体计算和消失定理仍在开发中。

### 8.2 形式化路线图

| 组件 | 状态 | 优先级 |
|------|------|--------|
| Čech上同调定义 | 🟡 部分完成 | 高 |
| 仿射开覆盖计算 | 🔴 待完成 | 高 |
| 增广复形正合性 | 🔴 待完成 | 高 |
| H^i(Spec A, M̃) = 0 (i>0) | 🔴 待完成 | 高 |
| Serre判别法 | 🔴 待完成 | 中 |

### 8.3 形式化代码框架

```lean
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Derived.DerivedCategory

namespace AlgebraicGeometry

variable {A : CommRingCat} {X : Scheme} [IsAffine X]

-- 定理: 仿射概形上的拟凝聚层上同调消失
theorem affine_cohomology_vanishing
    (F : QuasiCoherentSheaf X) (i : ℕ) (hi : i > 0) :
    cohomology X F i = 0 := by
  -- 步骤1: 化简到Čech上同调
  rw [cohomology_eq_cech]
  -- 步骤2: 取主开覆盖
  let U : AffineOpenCover X := standardAffineCover X
  -- 步骤3: 计算Čech复形
  have : chechComplex U F = alternatingCechComplex U F := by
    sorry
  -- 步骤4: 证明增广复形正合
  have exactness : (augmentedCechComplex U F).Exact := by
    sorry
  -- 步骤5: 结论
  sorry

-- Serre判别法
theorem serre_criterion_for_affineness
    [CompactSpace X]
    (h : ∀ F : QuasiCoherentSheaf X, cohomology X F 1 = 0) :
    IsAffine X := by
  -- 构造态射到Spec(O_X(X))
  let f : X ⟶ Spec (X.presheaf.obj (op ⊤)) :=
    ΓSpec.adjunction.unit.app X
  -- 证明是同构
  sorry

-- 辅助引理: 增广Čech复形的正合性
lemma augmented_cech_exact {n : ℕ} (f : Fin (n+1) → A)
    (hf : Ideal.span (Set.range f) = ⊤) (M : ModuleCat A) :
    (augmentedAlternatingCechComplex f M).Exact := by
  -- 使用局部化理论
  sorry

end AlgebraicGeometry
```

### 8.4 形式化挑战

**技术挑战**：
1. **Čech复形构造**：处理无限乘积和交错符号
2. **正合性证明**：涉及复杂的交换代数论证
3. **极限论证**：局部化与直极限的交换
4. **泛性质应用**：需要仔细处理范畴论构造

**建议策略**：
1. 先完成增广Čech复形的正合性（纯代数）
2. 建立Čech上同调与导出上同调的同构
3. 最后处理Serre判别法的几何部分

### 8.5 与现有工作的协调

Mathlib4中已有：
- 层论基础 (`Mathlib.CategoryTheory.Sites`)
- 导出范畴框架 (`Mathlib.CategoryTheory.Derived`)
- 环的局部化 (`Mathlib.RingTheory.Localization`)

可复用的成果：
- 局部化序列的正合性
- 层上同调的函子性
- 拟凝聚层的范畴结构

---

## 参考引用

```bibtex
@misc{stacks-project,
  author       = {The Stacks Project Authors},
  title        = {Stacks Project},
  howpublished = {\url{https://stacks.math.columbia.edu}},
  year         = {2024},
  note         = {Tag 01X8}
}

@article{serre1955faisceaux,
  title     = {Faisceaux alg{\'e}briques coh{\'e}rents},
  author    = {Serre, Jean-Pierre},
  journal   = {Annals of Mathematics},
  volume    = {61},
  pages     = {197--278},
  year      = {1955}
}
```

---

*文档版本: 1.0 | 创建日期: 2026-04-09 | 最后更新: 2026-04-09*
