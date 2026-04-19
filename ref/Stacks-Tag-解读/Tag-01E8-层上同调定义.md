---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 01E8 解读：层上同调定义

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01E8 |
| **章节** | Cohomology of Sheaves, Section 20.2: Cohomology of sheaves |
| **类型** | 定义 (Definition) |
| **重要性** | ⭐⭐⭐⭐⭐ (层论核心) |
| **Stacks Project链接** | https://stacks.math.columbia.edu/tag/01E8 |

---

## 2. 定义原文与翻译

### 英文原文

**Definition 20.2.1.** Let $X$ be a topological space. Let $\mathcal{F}$ be an abelian sheaf on $X$. The *cohomology groups* $H^i(X, \mathcal{F})$ are defined as the right derived functors of the global sections functor $\Gamma(X, -)$.

More explicitly, choose an injective resolution $\mathcal{F} \to \mathcal{I}^\bullet$ in the category of abelian sheaves on $X$. Then set

$$H^i(X, \mathcal{F}) = H^i(\Gamma(X, \mathcal{I}^\bullet)) = \frac{\ker(\Gamma(X, \mathcal{I}^i) \to \Gamma(X, \mathcal{I}^{i+1}))}{\text{im}(\Gamma(X, \mathcal{I}^{i-1}) \to \Gamma(X, \mathcal{I}^i))}$$

### 中文翻译

**定义 20.2.1.** 设 $X$ 是拓扑空间，$\mathcal{F}$ 是 $X$ 上的Abel层。定义**上同调群** $H^i(X, \mathcal{F})$ 为全局截面函子 $\Gamma(X, -)$ 的右导出函子。

更具体地说，在 $X$ 上的Abel层范畴中选取内射分解 $\mathcal{F} \to \mathcal{I}^\bullet$，然后定义：

$$H^i(X, \mathcal{F}) = H^i(\Gamma(X, \mathcal{I}^\bullet)) = \frac{\ker(\Gamma(X, \mathcal{I}^i) \to \Gamma(X, \mathcal{I}^{i+1}))}{\text{im}(\Gamma(X, \mathcal{I}^{i-1}) \to \Gamma(X, \mathcal{I}^i))}$$

---

## 3. 概念依赖图

```
Tag 01E8: 层上同调定义
│
├── 前置概念
│   ├── 拓扑空间
│   ├── 层 (Sheaf)
│   │   ├── 预层与层的公理
│   │   ├── 茎与截面
│   │   └── Abel层范畴
│   ├── 全局截面函子 Γ(X, -)
│   │   ├── 左正合性
│   │   └── 非右正合的例子
│   ├── 右导出函子 (Tag 05T7)
│   │   └── 内射分解
│   │   └── 同调计算
│   └── 内射层 (Injective Sheaf)
│       └── Godement构造
│
├── 核心构造
│   ├── 层上同调 H^i(X, F)
│   │   └── 定义：R^iΓ(X, F)
│   │   └── H^0(X, F) = Γ(X, F)
│   └── 计算方法
│       ├── 内射分解
│       ├── 软层分解
│       ├── 松散层分解
│       └── Čech上同调
│
├── 基本性质
│   ├── 长正合列
│   ├── 函子性
│   ├── 连接同态
│   └── 局部化性质
│
└── 相关Tags
    ├── Tag 05T7: 右导出函子
    ├── Tag 01ED: 上同调长正合列
    ├── Tag 01EE: 高阶像层
    ├── Tag 01X7: Čech上同调
    └── Tag 01X8: 仿射概形上同调
```

---

## 4. 详细内容与证明概要

### 4.1 为什么需要层上同调

**问题**：全局截面函子 $\Gamma(X, -)$ 仅左正合。

**经典反例**：设 $X = \mathbb{C}^\times$，考虑指数短正合列：

$$0 \to 2\pi i\mathbb{Z} \to \mathcal{O}_X \xrightarrow{\exp} \mathcal{O}_X^\times \to 0$$

取全局截面得到：

$$0 \to 2\pi i\mathbb{Z} \to \mathbb{C} \xrightarrow{\exp} \mathbb{C}^\times \to H^1(X, \mathbb{Z}) \to \cdots$$

指数映射在整体截面**不满**（无全局对数），丢失的信息由 $H^1$ 捕捉。

### 4.2 内射层的存在性

**Godement构造**：任意层 $\mathcal{F}$ 可典范嵌入内射层：

$$\mathcal{F} \hookrightarrow \mathcal{G}^0(\mathcal{F}) = \prod_{x \in X} (i_x)_* \mathcal{F}_x$$

其中 $i_x: \{x\} \hookrightarrow X$，$\mathcal{F}_x$ 是茎。

**性质**：

- $\mathcal{G}^0(\mathcal{F})$ 是flasque（松散）层，从而是内射的
- Abel层范畴有足够内射对象

### 4.3 基本性质证明

**性质 1: $H^0(X, \mathcal{F}) = \Gamma(X, \mathcal{F})$**

*证明*：由内射分解 $0 \to \mathcal{F} \to \mathcal{I}^0 \to \mathcal{I}^1 \to \cdots$ 和 $\Gamma$ 的左正合性，$0 \to \Gamma(X, \mathcal{F}) \to \Gamma(X, \mathcal{I}^0) \to \Gamma(X, \mathcal{I}^1)$ 正合，故 $H^0 = \ker(\Gamma(\mathcal{I}^0) \to \Gamma(\mathcal{I}^1)) = \Gamma(X, \mathcal{F})$。

**性质 2: 长正合列**

对短正合列 $0 \to \mathcal{F} \to \mathcal{G} \to \mathcal{H} \to 0$，存在连接同态 $\delta^i: H^i(X, \mathcal{H}) \to H^{i+1}(X, \mathcal{F})$ 使得：

$$0 \to H^0(\mathcal{F}) \to H^0(\mathcal{G}) \to H^0(\mathcal{H}) \xrightarrow{\delta^0} H^1(\mathcal{F}) \to H^1(\mathcal{G}) \to \cdots$$

正合。

**性质 3: 函子性**

层态射 $f: \mathcal{F} \to \mathcal{G}$ 诱导 $f^*: H^i(X, \mathcal{F}) \to H^i(X, \mathcal{G})$。

### 4.4 可计算分解

实际计算中，可用比内射层更广的类：

| 层类 | 性质 | 应用场景 |
|------|------|----------|
| Flasque（松散） | 限制映射满射 | 一般拓扑空间 |
| Soft（软） | 闭集上截面可延拓 | 仿紧空间（如流形） |
| Fine（精细） | 有单位分解 | 仿紧Hausdorff空间 |
| 内射 | Hom(-, I)正合 | 理论构造 |

**关键定理**：Flasque层的高阶上同调消失：$H^i(X, \mathcal{F}) = 0$ 对 $i > 0$ 若 $\mathcal{F}$ flasque。

---

## 5. 与FormalMath的对应关系

| FormalMath概念 | 对应内容 | 文档位置 |
|----------------|----------|----------|
| 层论基础 | 层、茎、截面 | `concept/层论/层的基本概念.md` |
| Abel层范畴 | 层范畴的Abel结构 | `concept/层论/层的范畴.md` |
| 全局截面函子 | Γ(X, -)的定义与性质 | `concept/层论/截面函子.md` |
| 内射层 | 内射对象与分解 | `concept/层论/内射层.md` |
| 导出函子 | 右导出函子理论 | `concept/同调代数/导出函子.md` |
| 层上同调 | 定义与计算 | `concept/层论/层上同调.md` |

### 学习路径

```
FormalMath: 层上同调理论
├── 前置
│   ├── 层论基础
│   ├── Abel范畴
│   ├── 导出函子
│   └── 同调代数工具
├── 当前 ← Tag 01E8
│   ├── 层上同调定义
│   ├── 长正合列
│   └── 计算工具
└── 后续
    ├── Čech上同调 (Tag 01X7)
    ├── 代数几何应用
    │   ├── 仿射上同调 (Tag 01X8)
    │   └── 射影上同调 (Tag 02O3)
    └── 复几何应用
        ├── de Rham上同调
        └── Dolbeault上同调
```

---

## 6. 应用与重要性

### 6.1 跨领域应用

层上同调是连接多个数学领域的桥梁：

| 领域 | 应用 | 具体例子 |
|------|------|----------|
| 代数几何 | 黎曼-罗赫定理 | 曲线上的除子上同调 |
| 复几何 | Hodge理论 | $H^{p,q}$ 分解 |
| 代数拓扑 | 局部系数上同调 | 纤维丛的谱序列 |
| 数论 | Étale上同调 | Weil猜想 |
| 表示论 | 旗簇的上同调 | Borel-Weil-Bott定理 |

### 6.2 经典计算

**球面S^n的常值层上同调**：

$$H^i(S^n, \mathbb{Z}) = \begin{cases} \mathbb{Z} & i = 0, n \\ 0 & \text{其他} \end{cases}$$

**复射影空间** (Tag 02O3)：

$$H^q(\mathbb{P}^n, \mathcal{O}(d)) = \begin{cases} \mathbb{C}^{\binom{n+d}{n}} & q = 0, d \geq 0 \\ \mathbb{C}^{\binom{-d-1}{n}} & q = n, d \leq -n-1 \\ 0 & \text{其他} \end{cases}$$

### 6.3 现代发展

- **Étale上同调** (Grothendieck, Artin, Deligne)：解决Weil猜想
- **晶体上同调**：特征p几何
- **刚性上同调**：p进上同调理论
- **导出代数几何**：将上同调提升到导出范畴层次

---

## 7. 与其他资源的关联

### 7.1 教科书对应

| 教科书 | 章节 | 内容 |
|--------|------|------|
| Hartshorne | III.2 | Cohomology of sheaves |
| Godement | Chapter II | Cohomologie à valeur dans un faisceau |
| Bredon | Chapter III | Sheaf cohomology |
| Warner | Chapter V | Sheaves and cohomology |
| Wells (DMO) | Chapter II | Sheaf cohomology |

### 7.2 nLab条目

- [sheaf cohomology](https://ncatlab.org/nlab/show/sheaf+cohomology)
- [abelian sheaf cohomology](https://ncatlab.org/nlab/show/abelian+sheaf+cohomology)
- [derived functor](https://ncatlab.org/nlab/show/derived+functor)

### 7.3 Wikipedia条目

- [Sheaf cohomology](https://en.wikipedia.org/wiki/Sheaf_cohomology)
- [Čech cohomology](https://en.wikipedia.org/wiki/%C4%8Cech_cohomology)

### 7.4 相关Stacks Tags

| Tag | 内容 | 关系 |
|-----|------|------|
| 05T7 | 右导出函子 | 理论基础 |
| 01ED | 上同调长正合列 | 基本性质 |
| 01EE | 高阶像层 | 推广 |
| 01X7 | Čech上同调 | 计算工具 |
| 01X8 | 仿射概形上同调 | 代数几何应用 |
| 02O3 | 射影空间上同调 | 经典计算 |

---

## 8. Lean4形式化展望

### 8.1 Mathlib4现状

Mathlib4在层上同调方面的进展：

```lean
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Sites.Cohomology
import Mathlib.Algebra.Category.ModuleCat.Abelian

-- 层上同调的基本定义
#check CategoryTheory.Abelian.sheafCohomology

-- Godement分解
#check CategoryTheory.GodementResolution

-- 高阶像层
#check CategoryTheory.Abelan.higherDirectImage
```

**状态评估**：基础框架正在建立，具体计算和几何应用待发展。

### 8.2 形式化路线图

| 组件 | 状态 | 说明 |
|------|------|------|
| Abel层范畴 | ✅ 完整 | Mathlib核心 |
| 全局截面函子 | ✅ 完整 | 基本定义 |
| 内射层构造 | 🟡 部分 | Godement构造 |
| 层上同调定义 | 🟡 部分 | Tag 01E8目标 |
| 长正合列 | 🟡 部分 | 需要连接同态 |
| Flasque层性质 | 🔴 待开发 | 消失定理 |
| Čech上同调 | 🔴 待开发 | 计算工具 |
| 具体计算 | 🔴 待开发 | 射影空间等 |

### 8.3 形式化代码框架

```lean
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Abelian.Derived.RightDerived
import Mathlib.Algebra.Category.ModuleCat.Abelian

namespace CategoryTheory

variable {C : Type*} [Category C] [S : GrothendieckTopology C]
variable (X : C) (F : SheafOfAbelianGroups S)

-- 层上同调定义（使用右导出函子）
def sheafCohomology (i : ℕ) : AbelianGroup :=
  (RightDerivedFunctor (globalSectionsFunctor S X) i).obj F

-- H^0 = 全局截面
theorem H0_eq_globalSections :
    sheafCohomology S X F 0 ≅ F.sections X := by
  -- 利用左正合性
  sorry

-- 长正合列
theorem longExactSequence {F G H : SheafOfAbelianGroups S}
    (f : F ⟶ G) (g : G ⟶ H) (h : ShortExact f g) :
    ExactSequence AbelianGroup (ComplexShape.down ℕ) := by
  -- 导出函子的标准性质
  sorry

-- Flasque层的消失定理
theorem flasque_vanishing (F : SheafOfAbelianGroups S)
    [Flasque F] (i : ℕ) (hi : i > 0) :
    sheafCohomology S X F i = 0 := by
  -- Flasque层是Γ-零调的
  sorry

-- 与Čech上同调的比较
theorem sheafCohomology_eq_cech (U : Cover S X) (i : ℕ)
    [U.IsLeray F] :
    sheafCohomology S X F i ≅ CechCohomology U F i := by
  -- Leray定理
  sorry

end CategoryTheory
```

### 8.4 代数几何中的具体化

```lean
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.AffineScheme

namespace AlgebraicGeometry

variable {X : Scheme} (F : SheafOfModules X.ringCatSheaf)

-- 概形上的层上同调
def schemeCohomology (i : ℕ) : ModuleCat (X.presheaf.obj (op ⊤)) :=
  sheafCohomology X.topology F i

-- 仿射概形上同调消失
theorem affineCohomologyVanishing [IsAffine X] (i : ℕ) (hi : i > 0) :
    schemeCohomology F i = 0 := by
  -- Serre定理的形式化
  sorry

-- 射影空间上同调计算
theorem projectiveSpaceCohomology (n : ℕ) (d : ℤ) (i : ℕ) :
    schemeCohomology (twistingSheaf n d) i =
    match i with
    | 0 => ...
    | n => ...
    | _ => 0 := by
  -- Tag 02O3的形式化
  sorry

end AlgebraicGeometry
```

### 8.5 发展建议

**短期目标**：

- 完成层上同调的基本定义（Tag 01E8）
- 建立长正合列框架
- 实现Flasque层消失定理

**中期目标**：

- 建立Čech上同调理论（Tag 01X7）
- 证明比较定理
- 完成仿射上同调消失（Tag 01X8）

**长期目标**：

- 射影空间上同调计算（Tag 02O3）
- Serre对偶的形式化
- 导出范畴视角的层上同调

---

## 参考引用

```bibtex
@misc{stacks-project,
  author       = {The Stacks Project Authors},
  title        = {Stacks Project},
  howpublished = {\url{https://stacks.math.columbia.edu}},
  year         = {2024},
  note         = {Tag 01E8}
}

@book{godement1958topologie,
  title     = {Topologie Alg{\'e}brique et Th{\'e}orie des Faisceaux},
  author    = {Godement, Roger},
  year      = {1958},
  publisher = {Hermann}
}
```

---

*文档版本: 1.0 | 创建日期: 2026-04-09 | 最后更新: 2026-04-09*
