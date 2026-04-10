# Stacks Tag 013T - 内射分解

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 013T |
| **概念名称** | 内射分解 (Injective Resolutions) |
| **所属章节** | Chapter 13: Derived Categories, Section 13.18 |
| **概念类型** | 定义与构造 (Definition & Construction) |
| ** Stacks原文** | Definition 13.18.1 / Lemma 13.18.3 |

---

## 2. 定理/定义原文

**定义陈述：**

设 $\mathcal{A}$ 是一个阿贝尔范畴，$A \in \text{Ob}(\mathcal{A})$ 是一个对象。

**内射分解**是指一个正合序列：
$$0 \to A \to I^0 \to I^1 \to I^2 \to \cdots$$

其中每个 $I^n$ 都是内射对象。

等价地，这是一个拟同构（quasi-isomorphism）：
$$A[0] \to I^\bullet$$

其中 $I^\bullet$ 是有界下复形，且每个 $I^n$ 内射。

**存在性定理：**

若阿贝尔范畴 $\mathcal{A}$ 有足够内射对象，则每个对象都有内射分解。

**英文原文：**
> Let $\mathcal{A}$ be an abelian category. Let $A \in \text{Ob}(\mathcal{A})$. An *injective resolution of $A$* is a complex $I^\bullet$ together with a map $A \to I^0$ such that:
> 1. We have $I^n = 0$ for $n < 0$.
> 2. Each $I^n$ is an injective object of $\mathcal{A}$.
> 3. The map $A \to I^0$ induces an isomorphism $A \to H^0(I^\bullet)$ and for $n \neq 0$ we have $H^n(I^\bullet) = 0$.

---

## 3. 概念依赖图

```
Tag 013T: 内射分解
│
├── 前置概念
│   ├── 阿贝尔范畴 (Abelian Category) [Tag 009B]
│   ├── 复形 (Complex) [Tag 010G]
│   ├── 内射对象 (Injective Object) [Tag 013N]
│   ├── 足够内射对象 (Enough Injectives) [Tag 013P]
│   ├── 拟同构 (Quasi-Isomorphism) [Tag 010U]
│   └── 同调 (Homology) [Tag 010N]
│
├── 构造方法
│   ├── 逐次构造：利用内射包
│   ├── 函子性：态射的提升
│   └── 同伦唯一性：在同伦意义下唯一
│
├── 重要性质
│   ├── 存在性：有足够内射则存在
│   ├── 唯一性：同伦等价意义下唯一
│   ├── 函子性：导出函子的基础
│   └── 与投影分解的对偶 [Tag 013U]
│
└── 后续应用
    ├── 右导出函子 [Tag 013W]
    ├── 层上同调 [Tag 01FV]
    ├── Ext函子 [Tag 00DV]
    └── 导出范畴等价 [Tag 013Y]
```

---

## 4. 证明概要（存在性与唯一性）

### 4.1 存在性证明

**定理：** 若阿贝尔范畴 $\mathcal{A}$ 有足够内射对象，则每个对象 $A \in \mathcal{A}$ 都有内射分解。

**构造性证明：**

**步骤1：** 构造 $I^0$

由于 $\mathcal{A}$ 有足够内射，存在单射 $A \hookrightarrow I^0$，其中 $I^0$ 是内射对象。

令 $B^1 = \text{coker}(A \to I^0)$ 为余核。

**步骤2：** 归纳构造 $I^n$

假设已构造到 $I^{n-1}$，得到余核 $B^n = \text{coker}(I^{n-2} \to I^{n-1})$。

由于有足够内射，存在单射 $B^n \hookrightarrow I^n$，其中 $I^n$ 内射。

定义微分 $d^{n-1}: I^{n-1} \to I^n$ 为复合：
$$I^{n-1} \twoheadrightarrow B^n \hookrightarrow I^n$$

**步骤3：** 验证正合性

由构造，$\text{im}(d^{n-1}) = B^n = \ker(d^n)$，因此序列正合。

### 4.2 同伦唯一性

**定理：** 设 $I^\bullet$ 和 $J^\bullet$ 都是 $A$ 的内射分解，则存在同伦等价：
$$I^\bullet \simeq J^\bullet$$

**证明概要：**

**步骤1：** 构造态射 $f: I^\bullet \to J^\bullet$

利用 $J^0$ 的内射性，将 $A \to J^0$ 提升为 $f^0: I^0 \to J^0$。

归纳地，利用 $J^n$ 的内射性提升。

**步骤2：** 构造同伦

若 $f, g: I^\bullet \to J^\bullet$ 都覆盖 $A$ 上的恒等，则它们同伦。

利用内射对象的内射性构造同伦算子 $h^n: I^n \to J^{n-1}$。

### 4.3 函子性

**定理：** 设 $\varphi: A \to B$ 是态射，$I^\bullet$ 和 $J^\bullet$ 分别是 $A$ 和 $B$ 的内射分解，则存在复形态射：
$$\tilde{\varphi}: I^\bullet \to J^\bullet$$

在复形同伦意义下唯一。

**意义：** 这使得我们可以定义**右导出函子**。

---

## 5. 与FormalMath对应

### 5.1 概念映射

| Stacks Project概念 | FormalMath对应内容 | 文件路径 |
|-------------------|-------------------|----------|
| 内射对象 | Injective | `concept/范畴论/内射对象.md` |
| 足够内射 | EnoughInjectives | `concept/同调代数/阿贝尔范畴.md` |
| 内射分解 | InjectiveResolution | `concept/同调代数/分解.md` |
| 拟同构 | QuasiIso | `concept/同调代数/导出范畴.md` |
| 右导出函子 | RightDerivedFunctor | `concept/同调代数/导出函子.md` |

### 5.2 知识体系位置

```
FormalMath知识体系
├── 范畴论基础
│   └── 阿贝尔范畴
│       ├── 内射对象 ←── 核心概念
│       └── 足够内射 ←── 存在性条件
│
├── 同调代数
│   ├── 复形理论
│   │   └── 复形的构造
│   │
│   ├── 分解理论
│   │   ├── 内射分解 ←── Tag 013T
│   │   └── 投影分解 ←── Tag 013U
│   │
│   └── 导出函子
│       └── 右导出函子 ←── 主要应用
```

### 5.3 学习路径建议

```
学习路径：
阿贝尔范畴
    ├── 正合序列
    ├── 内射对象 ←── 关键前置
    └── 足够内射 ←── 存在性保证
            ↓
复形与分解
    ├── 复形的定义
    ├── 同调代数基础
    └── 内射分解 ←── Tag 013T
            ↓
导出函子
    └── 右导出函子的构造
```

---

## 6. 应用与重要性

### 6.1 理论重要性

**同调代数的基石：**

内射分解是定义**导出函子**和**导出范畴**的核心工具。它是将"非正合"函子转化为长正合序列的桥梁。

**核心作用：**
1. **导出函子**：$R^nF(A) = H^n(F(I^\bullet))$
2. **导出范畴**：$D^+(\mathcal{A})$ 的内射复形实现
3. **层上同调**：Sheaf cohomology 的标准计算工具

### 6.2 实际应用场景

#### 场景1：层上同调

设 $X$ 是拓扑空间，$\mathcal{F}$ 是阿贝尔群层。

**定义：** $H^n(X, \mathcal{F}) = R^n\Gamma(X, \mathcal{F})$

**计算：** 取 $\mathcal{F}$ 的内射分解 $\mathcal{F} \to \mathcal{I}^\bullet$，则：
$$H^n(X, \mathcal{F}) = H^n(\Gamma(X, \mathcal{I}^\bullet))$$

**例：** 对于仿射概形 $X = \text{Spec}(A)$，Serre消失定理说：
$$H^n(X, \widetilde{M}) = 0, \quad n > 0$$

#### 场景2：Ext函子

设 $R$ 是环，$M, N$ 是 $R$-模。

**定义：** $\text{Ext}^n_R(M, N) = R^n\text{Hom}_R(M, -)(N)$

**计算：** 取 $N$ 的内射分解 $N \to I^\bullet$，则：
$$\text{Ext}^n_R(M, N) = H^n(\text{Hom}_R(M, I^\bullet))$$

#### 场景3：群上同调

设 $G$ 是群，$M$ 是 $G$-模。

**定义：** $H^n(G, M) = R^n(-)^G(M)$（取 $G$-不变量）

**计算：** 通过内射分解计算。

### 6.3 具体例子

**例1：常值层的内射分解**

设 $X$ 是流形，$\underline{\mathbb{R}}$ 是常值层。其内射分解由微分形式给出：
$$0 \to \underline{\mathbb{R}} \to \Omega^0 \xrightarrow{d} \Omega^1 \xrightarrow{d} \Omega^2 \to \cdots$$

（这是软弱分解，也是内射分解的特殊情形）

**例2：模的内射包**

在模范畴中，内射分解的第一步是**内射包**（injective hull）：
$$0 \to M \to E(M)$$

其中 $E(M)$ 是 $M$ 的内射包。

### 6.4 现代发展

- **K-内射复形**：推广到无界复形
- **导出范畴的等价**：内射复形实现 $D^+(\mathcal{A})$
- **模型范畴**：内射分解作为余纤维替换

---

## 7. 与其他资源关联

### 7.1 Stacks Project内部关联

| 相关Tag | 关系类型 | 说明 |
|--------|---------|------|
| **Tag 013N** (内射对象) | 核心概念 | 分解的基本单元 |
| **Tag 013P** (足够内射) | 存在性条件 | 保证分解存在 |
| **Tag 013U** (投影分解) | 对偶概念 | 对偶范畴中的对应 |
| **Tag 013W** (右导出函子) | 主要应用 | 导出函子的定义基础 |
| **Tag 01FV** (层上同调) | 核心应用 | 层上同调的标准计算 |
| **Tag 010U** (拟同构) | 同伦理论 | 分解的同伦等价 |

### 7.2 外部参考资源

**经典教材：**

1. **Weibel, An Introduction to Homological Algebra**
   - Chapter 2: 导出函子与分解
   - 内射分解的标准参考

2. **Gelfand-Manin, Methods of Homological Algebra**
   - Chapter III: 导出范畴与分解
   - 更范畴化的视角

3. **Hartshorne, Algebraic Geometry**
   - Chapter III, §1-2: 层上同调与分解
   - 几何应用视角

4. **Rotman, An Introduction to Homological Algebra**
   - Chapter 6: 导出函子
   - 详细的例子和计算

**在线资源：**
- [Stacks Project 第13章](https://stacks.math.columbia.edu/tag/013T)
- [nLab: injective resolution](https://ncatlab.org/nlab/show/injective+resolution)

---

## 8. Lean4形式化展望

### 8.1 形式化难度评估

| 方面 | 难度 | 说明 |
|------|------|------|
| 概念复杂度 | ★★★★☆ | 涉及阿贝尔范畴、复形、同伦 |
| 证明技术 | ★★★★☆ | 需要同伦代数技术 |
| 依赖链条 | ★★★★★ | 需要完整的同调代数基础 |
| 预计工作量 | 大 | 需要4-6个月 |

### 8.2 mathlib4现状

**当前已有基础：**
```
mathlib4
├── Algebra
│   └── Homology (同调代数) ✅
│       ├── Homology.lean
│       ├── ShortComplex.lean
│       └── Homotopy.lean
│
└── CategoryTheory
    ├── Abelian (阿贝尔范畴) ✅
    ├── Injective (内射对象) 🔄
    └── Derived (导出范畴) 📝 计划中
```

### 8.3 形式化路线图

**阶段1：内射对象理论 (2个月)**

```lean
import Mathlib.CategoryTheory.Abelian.Injective

namespace CategoryTheory

-- 内射对象的定义
class Injective (X : C) : Prop where
  factors : ∀ (Y Z : C) [Mono (f : Y ⟶ Z)] (g : Y ⟶ X),
    ∃ h : Z ⟶ X, f ≫ h = g

-- 足够内射
def HasEnoughInjectives (C : Type*) [Category C] [Abelian C] : Prop :=
  ∀ X : C, ∃ I : C, Injective I ∧ Nonempty (Mono (X ⟶ I))

end CategoryTheory
```

**阶段2：内射分解 (2个月)**

```lean
-- 内射分解的结构
structure InjectiveResolution (X : C) where
  c : CochainComplex C ℕ
  ι : X ⟶ c.X 0
  injective : ∀ n, Injective (c.X n)
  exact : ∀ n, (c.d n).Exact
  mono : Mono ι

-- 存在性定理
theorem exists_injective_resolution [HasEnoughInjectives C] (X : C) :
    Nonempty (InjectiveResolution X) := by
  sorry
```

**阶段3：函子性与同伦 (2个月)**

```lean
-- 内射分解之间的态射
def InjectiveResolution.map {X Y : C} (f : X ⟶ Y)
    (I : InjectiveResolution X) (J : InjectiveResolution Y) :
    I.c ⟶ J.c := ...

-- 同伦唯一性
theorem homotopy_uniqueness {X : C} {I J : InjectiveResolution X}
    (f g : I.c ⟶ J.c) (hf : f.commute_ι) (hg : g.commute_ι) :
    Homotopy f g := by
  sorry
```

### 8.4 技术挑战与解决方案

| 挑战 | 解决方案 |
|------|---------|
| 同伦的形式化 | 使用 `Homotopy` 类型类 |
| 复形的索引 | 使用 `CochainComplex` 结构 |
| 足够内射的构造 | 分范畴逐个实现 |
| 与导出范畴的整合 | 参考mathlib4的导出范畴设计 |

---

## 附录

### A. 符号速查表

| 符号 | 含义 | LaTeX |
|------|------|-------|
| $I^\bullet$ | 内射复形 | `I^\bullet` |
| $A[0]$ | 集中在0度的复形 | `A[0]` |
| $\simeq$ | 同伦等价 | `\simeq` |
| $R^nF$ | 第$n$右导出函子 | `R^nF` |
| $\text{Ext}^n$ | Ext函子 | `\text{Ext}^n` |

### B. 常见阿贝尔范畴的足够内射性

| 范畴 | 足够内射？ | 说明 |
|------|----------|------|
| $R$-模范畴 | ✓ | 内射模存在 |
| 层范畴 | ✓ | 内射层存在 |
| 凝聚层范畴 | ✗ | 一般没有足够内射 |
| 拟凝聚层 | ✓ | 有足够内射 |

---

*文档版本: 1.0*  
*创建日期: 2026年4月*  
*对应Stacks Project版本: 2024.02*
