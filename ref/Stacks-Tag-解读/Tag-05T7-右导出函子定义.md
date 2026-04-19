---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 05T7 解读：右导出函子定义

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 05T7 |
| **章节** | Homology, Section 12.14: Derived functors in general |
| **类型** | 定义 (Definition) |
| **重要性** | ⭐⭐⭐⭐⭐ (同调代数基础) |
| **Stacks Project链接** | https://stacks.math.columbia.edu/tag/05T7 |

---

## 2. 定义原文与翻译

### 英文原文

**Definition 12.14.2.** Let $F : \mathcal{A} \to \mathcal{B}$ be a left exact additive functor between abelian categories. Assume $\mathcal{A}$ has enough injectives. The *right derived functors* $R^iF$, $i \geq 0$ are defined as follows:

1. For an object $A$ of $\mathcal{A}$ choose an injective resolution $A[0] \to I^\bullet$ and set $R^iF(A) = H^i(F(I^\bullet))$.
2. For a morphism $f : A \to B$ of $\mathcal{A}$ choose a morphism of resolutions $I^\bullet \to J^\bullet$ lying over $f$ and define $R^iF(f)$ to be the induced map $H^i(F(I^\bullet)) \to H^i(F(J^\bullet))$.

### 中文翻译

**定义 12.14.2.** 设 $F : \mathcal{A} \to \mathcal{B}$ 是Abel范畴间的左正合加性函子。假设 $\mathcal{A}$ 有足够内射对象。定义**右导出函子** $R^iF$（$i \geq 0$）如下：

1. 对 $\mathcal{A}$ 的对象 $A$，选取内射分解 $A[0] \to I^\bullet$，定义 $R^iF(A) = H^i(F(I^\bullet))$。

2. 对 $\mathcal{A}$ 的态射 $f : A \to B$，选取覆盖 $f$ 的分解态射 $I^\bullet \to J^\bullet$，定义 $R^iF(f)$ 为诱导映射 $H^i(F(I^\bullet)) \to H^i(F(J^\bullet))$。

---

## 3. 概念依赖图

```
Tag 05T7: 右导出函子定义
│
├── 前置概念
│   ├── Abel范畴 (Abelian Category)
│   │   ├── 可加范畴
│   │   ├── 核与余核
│   │   └── 正合序列
│   ├── 加性函子 (Additive Functor)
│   │   └── 保持有限直和
│   ├── 左正合函子 (Left Exact Functor)
│   │   └── 保持核与有限极限
│   │   └── 0 → A → B → C 正合 ⟹ 0 → FA → FB → FC 正合
│   ├── 内射对象 (Injective Object)
│   │   └── Hom(-, I)是正合函子
│   │   └── 足够内射性
│   └── 内射分解 (Injective Resolution)
│       └── A → I^0 → I^1 → I^2 → ...
│       └── 正合复形，I^i内射
│
├── 核心构造
│   ├── 右导出函子 R^iF
│   │   └── 定义：R^iF(A) = H^i(F(I^•))
│   │   └── R^0F ≅ F（左正合性）
│   └── 函子性
│       └── 分解间的态射（在同伦意义下唯一）
│
├── 基本性质
│   ├── δ-函子结构
│   ├── 长正合列
│   ├── 泛性质
│   └── 导出范畴视角
│
└── 相关Tags
    ├── Tag 0106: Abel范畴定义
    ├── Tag 013G: 加性函子
    ├── Tag 013N: 左正合函子
    ├── Tag 013P: 内射对象
    └── Tag 013U: δ-函子
```

---

## 4. 详细内容与证明概要

### 4.1 构造动机

**问题**：左正合函子 $F$ 不保持右正合性，即若 $0 \to A \to B \to C \to 0$ 短正合，则 $0 \to FA \to FB \to FC$ 正合但 $FB \to FC$ 不必满射。

**解决**：通过**内射分解**延长序列，捕捉丢失的信息。

### 4.2 内射分解的存在性

**引理**：若 $\mathcal{A}$ 有足够内射对象，则每个对象 $A$ 有内射分解。

**构造**：
1. 因足够内射，存在单射 $A \hookrightarrow I^0$（$I^0$内射）
2. 令 $A^1 = \text{coker}(A \to I^0)$，取单射 $A^1 \hookrightarrow I^1$
3. 归纳继续：$A^{n+1} = \text{coker}(A^n \to I^n) \hookrightarrow I^{n+1}$

### 4.3 良定义性证明

**问题**：内射分解不唯一，$R^iF(A)$ 是否依赖选择？

**定理**：$R^iF(A)$ 在同构意义下唯一。

**证明概要**：

1. **分解间的比较定理**：给定 $f: A \to B$，任意两个内射分解 $I^\bullet, J^\bullet$ 间存在（同伦意义下唯一）的链映射。

2. **同伦不变性**：若 $f \sim g: I^\bullet \to J^\bullet$ 链同伦，则 $H^i(F(f)) = H^i(F(g))$。

3. **特别地**：当 $f = \text{id}_A$，得到 $H^i(F(I^\bullet)) \cong H^i(F(J^\bullet))$。

### 4.4 基本性质

**定理 1**: $R^0F \cong F$

**证明**：因 $F$ 左正合，$0 \to FA \to FI^0 \to FI^1$ 正合，故 $H^0(F(I^\bullet)) = FA$。

**定理 2 (长正合列)**：对短正合列 $0 \to A \to B \to C \to 0$，存在连接同态使得：

$$0 \to FA \to FB \to FC \to R^1F(A) \to R^1F(B) \to \cdots$$

是正合的。

**定理 3 (泛性质)**：$(R^iF, \delta)$ 是泛 δ-函子。

### 4.5 导出范畴视角

现代观点：右导出函子是导出范畴间的函子

$$RF : D^+(\mathcal{A}) \to D^+(\mathcal{B})$$

$R^iF(A) = H^i(RF(A[0]))$ 是第 $i$ 次上同调。

---

## 5. 与FormalMath的对应关系

| FormalMath概念 | 对应内容 | 文档位置 |
|----------------|----------|----------|
| Abel范畴 | 定义与基本性质 | `concept/范畴论/Abel范畴.md` |
| 加性函子 | 范畴论中的函子 | `concept/范畴论/加性函子.md` |
| 正合序列 | 短正合与长正合 | `concept/同调代数/正合序列.md` |
| 内射对象 | 内射模与内射对象 | `concept/同调代数/内射对象.md` |
| 内射分解 | 分解与消解 | `concept/同调代数/内射分解.md` |
| 导出函子 | 同调代数核心 | `concept/同调代数/导出函子.md` |

### 学习路径

```
FormalMath: 同调代数核心
├── 前置
│   ├── 范畴论基础
│   ├── Abel范畴
│   ├── 正合性
│   └── 内射/投射对象
├── 当前 ← Tag 05T7
│   ├── 右导出函子
│   ├── 左导出函子
│   └── δ-函子理论
└── 后续
    ├── 层上同调 (Tag 01E8)
    ├── Ext与Tor函子
    ├── 谱序列
    └── 导出范畴
```

---

## 6. 应用与重要性

### 6.1 核心理论地位

右导出函子是同调代数的**核心构造**，统一了：

| 应用 | 函子 | 右导出函子 |
|------|------|-----------|
| 层上同调 | 全局截面 Γ | $H^i(X, -) = R^i\Gamma(X, -)$ |
| Ext函子 | Hom(A, -) | $Ext^i(A, B) = R^iHom(A, -)(B)$ |
| 局部上同调 | 支撑截面 Γ_Z | $H^i_Z(X, -) = R^i\Gamma_Z(X, -)$ |
| 导出Hom | 内Hom | $R\mathcal{H}om$ |
| 推出 | 直接像 $f_*$ | $R^if_*$ |

### 6.2 层上同调的例子

设 $X$ 是拓扑空间，$\Gamma(X, -): \text{Sh}(X) \to \text{Ab}$ 是全局截面函子。

- **左正合性**：$0 \to \mathcal{F} \to \mathcal{G} \to \mathcal{H}$ 正合 ⟹ $0 \to \Gamma(X, \mathcal{F}) \to \Gamma(X, \mathcal{G}) \to \Gamma(X, \mathcal{H})$ 正合

- **层上同调定义**：$H^i(X, \mathcal{F}) = R^i\Gamma(X, \mathcal{F})$

- **计算**：使用内射层（flasque/软层）分解

### 6.3 Ext函子的计算

对 $R$-模，$Ext^i_R(M, N)$ 可通过 $N$ 的内射分解或 $M$ 的投射分解计算。

**应用**：
- 扩张分类：$Ext^1$ 分类模的扩张
- 障碍理论：形变理论中的障碍类

---

## 7. 与其他资源的关联

### 7.1 教科书对应

| 教科书 | 章节 | 内容 |
|--------|------|------|
| Weibel | Chapter 2 | Derived functors |
| Rotman | Chapter 6 | Homology of functors |
| Hilton-Stammbach | Chapter IV | Derived functors |
| Gelfand-Manin | Chapter 3 | Derived categories and functors |
| Stacks Project | Tag 05T7 | General derived functors |

### 7.2 nLab条目

- [derived functor](https://ncatlab.org/nlab/show/derived+functor)
- [right derived functor](https://ncatlab.org/nlab/show/right+derived+functor)
- [homological algebra](https://ncatlab.org/nlab/show/homological+algebra)

### 7.3 Wikipedia条目

- [Derived functor](https://en.wikipedia.org/wiki/Derived_functor)
- [Homological algebra](https://en.wikipedia.org/wiki/Homological_algebra)

### 7.4 相关Stacks Tags

| Tag | 内容 | 关系 |
|-----|------|------|
| 0106 | Abel范畴 | 基础 |
| 013G | 加性函子 | 函子类型 |
| 013N | 左正合函子 | 前提条件 |
| 013P | 内射对象 | 构造工具 |
| 013U | δ-函子 | 结构 |
| 013Y | 长正合列 | 基本性质 |
| 0140 | 导出范畴 | 现代观点 |

---

## 8. Lean4形式化展望

### 8.1 Mathlib4现状

Mathlib4已有大量相关基础设施：

```lean
import Mathlib.Algebra.Homology.Homology
import Mathlib.CategoryTheory.Abelian.Injective
import Mathlib.CategoryTheory.Abelian.Derived.RightDerived

-- Abel范畴
#check CategoryTheory.Abelian

-- 内射对象
#check CategoryTheory.Injective

-- 内射分解
#check CategoryTheory.InjectiveResolution

-- 右导出函子
#check CategoryTheory.Abelian.RightDerived
```

**状态评估**：核心定义和基本性质已有，正在完善具体计算和应用。

### 8.2 形式化路线图

| 组件 | 状态 | 说明 |
|------|------|------|
| Abel范畴框架 | ✅ 完整 | Mathlib核心 |
| 内射对象理论 | ✅ 完整 | 包含足够内射性 |
| 内射分解 | ✅ 完整 | 构造与唯一性 |
| 右导出函子定义 | ✅ 完整 | Tag 05T7已完成 |
| 长正合列 | 部分 | 连接同态构造 |
| δ-函子公理 | 部分 | 泛性质 |
| 层上同调应用 | 进行中 | 需要层论基础 |
| Ext函子 | 进行中 | 双变量导出 |

### 8.3 形式化代码示例

```lean
import Mathlib.CategoryTheory.Abelian.Derived.RightDerived
import Mathlib.Algebra.Homology.Homology

namespace CategoryTheory.Abelian

variable {C D : Type*} [Category C] [Category D]
  [Abelian C] [Abelian D] [EnoughInjectives C]
  (F : C ⥤ D) [Functor.Additive F] [LeftExactFunctor F]

-- 右导出函子 R^iF
def RightDerivedFunctor (i : ℕ) : C ⥤ D where
  obj X := (F.mapHomologicalComplex _ _).homology i (injectiveResolution X)
  map f := -- 使用分解间的态射诱导
    sorry

-- R^0F ≅ F
theorem rightDerived_zero_iso : RightDerivedFunctor F 0 ≅ F := by
  -- 利用左正合性
  sorry

-- 短正合列诱导长正合列
theorem long_exact_sequence {A B C : C} (f : A ⟶ B) (g : B ⟶ C)
    (h : ShortExact f g) :
    ExactSequence D (ComplexShape.down ℕ) := by
  -- 构造连接同态
  sorry

-- 内射对象的消失
theorem injective_vanishing (I : C) [Injective I] (n : ℕ) (hn : n > 0) :
    (RightDerivedFunctor F n).obj I = 0 := by
  -- 使用平凡分解 I[0]
  sorry

end CategoryTheory.Abelian
```

### 8.4 与层上同调的衔接

```lean
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Abelian.Derived.RightDerived

-- 层上同调作为右导出函子
def SheafCohomology {X : Scheme} (i : ℕ) :
    SheafOfModules X.ringCatSheaf ⥤ ModuleCat _ :=
  RightDerivedFunctor (globalSectionsFunctor X) i

-- 与具体计算的对应
theorem sheafCohomology_eq_cech {X : Scheme} (F : SheafOfModules X.ringCatSheaf)
    (U : OpenCover X) (i : ℕ) [U.IsAffine] :
    SheafCohomology i F ≅ CechCohomology U F i := by
  -- 使用Cartan定理或其他比较定理
  sorry
```

### 8.5 进一步发展方向

1. **计算工具**：建立与Čech上同调、超覆盖的具体联系
2. **谱序列**：Leray谱序列的形式化
3. **对偶性**：Grothendieck对偶的形式化基础
4. **导出范畴**：从经典导出函子到导出范畴函子的过渡

---

## 参考引用

```bibtex
@misc{stacks-project,
  author       = {The Stacks Project Authors},
  title        = {Stacks Project},
  howpublished = {\url{https://stacks.math.columbia.edu}},
  year         = {2024},
  note         = {Tag 05T7}
}

@book{weibel1994introduction,
  title     = {An Introduction to Homological Algebra},
  author    = {Weibel, Charles A.},
  year      = {1994},
  publisher = {Cambridge University Press}
}
```

---

*文档版本: 1.0 | 创建日期: 2026-04-09 | 最后更新: 2026-04-09*
