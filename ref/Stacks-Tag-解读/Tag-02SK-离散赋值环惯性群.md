---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 02SK 解读：离散赋值环惯性群

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 02SK |
| **章节** | Commutative Algebra, Section 15.108: Inertia theory |
| **类型** | 引理 (Lemma) |
| **重要性** | ⭐⭐⭐⭐ (代数数论/几何核心) |
| **最新评论** | 2026-04-07 有更新讨论 |
| **Stacks Project链接** | https://stacks.math.columbia.edu/tag/02SK |

---

## 2. 定理原文与翻译

### 英文原文

**Lemma 15.108.6.** Let $A$ be a discrete valuation ring with fraction field $K$. Let $L/K$ be a finite Galois extension. Let $\mathfrak{m}$ be a maximal ideal of the integral closure $B$ of $A$ in $L$. Let $I \subset G$ be the inertia group of $\mathfrak{m}$. Then $B^I$ is the integral closure of $A$ in $L^I$ and $A \to (B^I)_{B^I \cap \mathfrak{m}}$ is etale.

### 中文翻译

**引理 15.108.6.** 设 $A$ 是以 $K$ 为分式域的离散赋值环，$L/K$ 是有限Galois扩张，$B$ 是 $A$ 在 $L$ 中的整闭包，$\mathfrak{m}$ 是 $B$ 的极大理想，$I \subset G$ 是 $\mathfrak{m}$ 的惯性群。则：

1. $B^I$ 是 $A$ 在 $L^I$ 中的整闭包；
2. $A \to (B^I)_{B^I \cap \mathfrak{m}}$ 是etale扩张。

---

## 3. 概念依赖图

```
Tag 02SK: 离散赋值环惯性群
│
├── 前置概念
│   ├── 离散赋值环 (DVR)
│   │   ├── 定义：局部PID，非零极大理想
│   │   ├── 赋值v: K* → Z
│   │   └── 完备化
│   ├── 整闭包
│   │   └── A在L中的整闭包B
│   ├── Galois扩张
│   │   ├── Galois群G = Gal(L/K)
│   │   └── 正规且可分
│   ├── 分歧理论
│   │   ├── 分歧指数e
│   │   └── 剩余次数f
│   └── 惯性群I
│       └── 保持剩余域的Galois元素
│
├── 核心构造
│   ├── 惯性群I
│   │   └── I = {σ ∈ G | σ(x) ≡ x (mod m), ∀x ∈ B}
│   ├── 惯性域L^I
│   │   └── Galois对应中的固定子域
│   ├── 惯性环B^I
│   │   └── B在I作用下的不变子环
│   └── etale性
│       └── 无分歧且平坦
│
├── 理论框架
│   ├── 分歧滤过
│   │   └── G ⊇ I ⊇ R (ramification群)
│   ├── Hilbert理论
│   │   └── 分解群、惯性群、Frobenius
│   └── 扩张类型
│       ├── 非分歧扩张
│       ├── 惯性扩张
│       └── 完全分歧扩张
│
└── 相关Tags
    ├── Tag 00PB: DVR定义
    ├── Tag 09E8: 整闭包
    ├── Tag 02SH: 惯性群定义
    └── Tag 02SL: 高阶分歧群
```

---

## 4. 详细内容与证明概要

### 4.1 背景：分歧理论

设 $A$ 是DVR，$K = \text{Frac}(A)$，$L/K$ 有限Galois扩张，$B$ 是 $A$ 在 $L$ 中的整闭包。

**基本数据**：
- 分歧指数：$e = [L:K]_i$（惯性次数）
- 剩余次数：$f = [\kappa_B : \kappa_A]$
- 基本等式：$[L:K] = e \cdot f \cdot g$（$g$ 是素理想个数）

### 4.2 惯性群的定义

**分解群** $D$：保持素理想 $\mathfrak{m}$ 的Galois元素
$$D = \{\sigma \in G \mid \sigma(\mathfrak{m}) = \mathfrak{m}\}$$

**惯性群** $I$：在剩余域上作用平凡的元素
$$I = \{\sigma \in D \mid \sigma(x) \equiv x \pmod{\mathfrak{m}}, \forall x \in B\}$$

**等价刻画**：$I = \ker(D \to \text{Aut}(\kappa_B/\kappa_A))$

### 4.3 惯性域的性质

**定理**：设 $L^I = L^I$ 是 $I$ 的固定域，$B^I = B \cap L^I$，则：

1. $B^I$ 是 $A$ 在 $L^I$ 中的整闭包
2. $\mathfrak{m}^I = \mathfrak{m} \cap B^I$ 是 $B^I$ 中位于 $\mathfrak{m}_A$ 上的唯一素理想
3. $(B^I)_{\mathfrak{m}^I}$ 是DVR
4. 剩余域扩张 $\kappa_{B^I}/\kappa_A$ 是纯不可分的

### 4.4 Etale性证明

**核心结论**：$A \to (B^I)_{\mathfrak{m}^I}$ 是etale的。

**证明概要**：

1. **平坦性**：整闭包在DVR上是平坦的（因为无挠）

2. **无分歧判别**：需证：
   - 分歧指数 $e(B^I/A) = 1$
   - 剩余域扩张 $\kappa_{B^I}/\kappa_A$ 是可分且有限的

3. **分歧指数**：由惯性群的定义，$L/L^I$ 是完全分歧的，故 $L^I/K$ 是非分歧的，$e(B^I/A) = 1$

4. **剩余域**：$\text{Gal}(\kappa_B/\kappa_A) \cong D/I$，而 $I$ 在 $B^I$ 上作用平凡，故 $\kappa_{B^I} = \kappa_B^{D/I} \cong \kappa_A$（在Galois情形）

### 4.5 高阶分歧群（补充）

对于 $i \geq 0$，定义**高阶惯性群**：

$$G_i = \{\sigma \in G \mid v_L(\sigma(x) - x) \geq i+1, \forall x \in B\}$$

- $G_0 = I$（惯性群）
- $G_1 = R$（分歧群，wild inertia）
- $G_i/G_{i+1}$ 有具体的群结构描述

---

## 5. 与FormalMath的对应关系

| FormalMath概念 | 对应内容 | 文档位置 |
|----------------|----------|----------|
| 离散赋值环 | DVR | `concept/交换代数/离散赋值环.md` |
| 整闭包 | Integral closure | `concept/交换代数/整闭包.md` |
| Galois扩张 | Galois theory | `concept/Galois理论/Galois扩张.md` |
| 分歧理论 | Ramification theory | `concept/代数数论/分歧理论.md` |
| Etale扩张 | Etale morphisms | `concept/代数几何/etale态射.md` |

### 学习路径

```
FormalMath: 代数数论与几何
├── 前置
│   ├── DVR理论
│   ├── 整闭包
│   ├── Galois理论
│   └── 赋值论
├── 当前 ← Tag 02SK
│   ├── 分歧理论
│   ├── 惯性群
│   └── Hilbert理论
└── 后续
    ├── 类域论基础
    ├── etale上同调
    └── 代数几何中的分歧
```

---

## 6. 应用与重要性

### 6.1 代数数论中的应用

| 应用 | 说明 |
|------|------|
| 局部类域论 | 惯性群对应局部Artin映射的核 |
| 整体类域论 | 分歧理论在射线类域中的应用 |
| L-函数 | Euler因子中的惯性部分 |
| 互反律 | Artin互反律的局部版本 |

### 6.2 代数几何中的应用

**覆叠理论**：

Galois扩张 $L/K$ 对应于概形的etale覆叠：

$$\text{Spec}(B) \to \text{Spec}(A)$$

惯性群 $I$ 对应于覆叠的**单值群**（monodromy）。

**Etale基本群**：

$$\pi_1^{\text{et}}(\text{Spec}(A)) \cong \text{Gal}(K^{\text{unr}}/K)$$

其中 $K^{\text{unr}}$ 是 $K$ 的极大非分歧扩张。

### 6.3 最新研究动态 (2026-04-07)

Stacks Project 社区对Tag 02SK区域的持续讨论：

1. **高阶分歧群的精细化**：在混合特征情形下的新结果
2. **p进Hodge理论联系**：惯性群与p进周期环的关系
3. **完美胚空间**：在完美胚空间上的推广
4. **相对情形**：相对Galois扩张的惯性理论

### 6.4 与表示论的联系

**Artin表示**：Galois群 $G$ 在 $L$ 的加法群上的表示，其惯性子空间给出重要的表示论信息。

**Langlands对应**：局部Langlands对应中，惯性群与Weil-Deligne群的联系。

---

## 7. 与其他资源的关联

### 7.1 教科书对应

| 教科书 | 章节 | 内容 |
|--------|------|------|
| Serre, Local Fields | Chapter 1 | Ramification groups |
| Neukirch ANT | Chapter 2 | Hilbert's ramification theory |
| Liu Qing | 8.2 | Ramification theory |
| Stacks Project | Tag 02SK | Inertia theory |
| Cornell-Silverman | - | Arithmetic geometry applications |

### 7.2 nLab条目

- [ramification](https://ncatlab.org/nlab/show/ramification)
- [inertia group](https://ncatlab.org/nlab/show/inertia+group)
- [etale morphism](https://ncatlab.org/nlab/show/etale+morphism)
- [decomposition group](https://ncatlab.org/nlab/show/decomposition+group)

### 7.3 Wikipedia条目

- [Ramification (mathematics)](https://en.wikipedia.org/wiki/Ramification_(mathematics))
- [Inertia group](https://en.wikipedia.org/wiki/Inertia_group)
- [Hilbert's theorem 90](https://en.wikipedia.org/wiki/Hilbert%27s_theorem_90)

### 7.4 相关Stacks Tags

| Tag | 内容 | 关系 |
|-----|------|------|
| 00PB | DVR定义 | 基础 |
| 09E8 | 整闭包 | 基础 |
| 02SH | 惯性群定义 | 前置 |
| 02SL | 高阶分歧群 | 后续 |
| 02SM | 分歧群结构 | 深化 |
| 04EX | Etale态射 | 应用 |

---

## 8. Lean4形式化展望

### 8.1 Mathlib4现状

Mathlib4中相关理论：

```lean
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.FieldTheory.Galois.Basic

-- 离散赋值
#check Valuation.IsDiscrete

-- DVR
#check DiscreteValuationRing

-- Galois扩张
#check IsGalois

-- 整闭包
#check integralClosure

-- 分歧理论（待开发）
-- #check ramificationIndex
-- #check inertiaGroup
```

### 8.2 形式化路线图

| 组件 | 状态 | 优先级 |
|------|------|--------|
| DVR理论 | 完整 | 基础 |
| 赋值论 | 部分 | 基础 |
| 整闭包 | 完整 | 基础 |
| Galois理论 | 完整 | 基础 |
| 分歧指数 | 待开发 | 高 |
| 惯性群定义 | 待开发 | 高 |
| Hilbert理论 | 待开发 | 中 |
| Etale性证明 | 待开发 | 中 |

### 8.3 形式化代码框架

```lean
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

namespace AlgebraicNumberTheory

variable {A : Type*} [CommRing A] [IsDomain A] [DiscreteValuationRing A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type*} [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

-- 整闭包
def B : Subalgebra A L := integralClosure A L

-- 分歧指数
def ramificationIndex (Q : Ideal B) [Q.IsPrime] : ℕ :=
  sorry  -- v_L(uniformizer_A)

-- 惯性群
def inertiaGroup (Q : Ideal B) [Q.IsPrime] : Subgroup (L ≃ₐ[K] L) where
  carrier := {σ | ∀ x : B, (σ x : L) - (x : L) ∈ Q}
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

-- 惯性域
def inertiaField (Q : Ideal B) [Q.IsPrime] : IntermediateField K L :=
  FixedPoints.subfield (L ≃ₐ[K] L) (inertiaGroup Q)

-- 惯性环
def inertiaRing (Q : Ideal B) [Q.IsPrime] : Subalgebra A (inertiaField Q) :=
  (B ⊓ inertiaField Q).restrictScalars A

-- Tag 02SK核心定理
theorem inertiaRing_is_integralClosure :
    inertiaRing Q = integralClosure A (inertiaField Q) := by
  sorry

theorem inertiaRing_localization_is_etale :
    IsEtale (Localization.AtPrime (maximalIdeal A))
      (Localization (inertiaRing Q ⊓ Q).primesCompl) := by
  -- 证明分歧指数=1且剩余域可分
  sorry

end AlgebraicNumberTheory
```

### 8.4 与代数几何的衔接

```lean
import Mathlib.AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

-- DVR对应曲线的局部环
def DVRFromCurve {C : Scheme} [IsCurve C] (p : C) [IsClosedPoint p] :
    DiscreteValuationRing :=
  sorry  -- O_{C,p}

-- 分歧与覆叠
variable {X Y : Scheme} (f : X ⟶ Y) [IsFinite f] [IsGaloisCover f]

def ramificationDivisor : WeilDivisor X :=
  sorry  -- 分歧点的形式和

def inertiaSheaf : SheafOfGroups X :=
  sorry  -- 惯性群构成的层

end AlgebraicGeometry
```

### 8.5 发展建议

**近期目标**：
- 完成分歧指数的完整定义与基本性质
- 实现惯性群和分解群的形式化
- 建立Hilbert分歧理论的基本框架

**中长期目标**：
- 完成Tag 02SK的核心证明（惯性环的etale性）
- 建立与etale上同调的联系
- 发展局部类域论的基础形式化

---

## 参考引用

```bibtex
@misc{stacks-project,
  author       = {The Stacks Project Authors},
  title        = {Stacks Project},
  howpublished = {\url{https://stacks.math.columbia.edu}},
  year         = {2024},
  note         = {Tag 02SK}
}

@book{serre1979local,
  title     = {Local Fields},
  author    = {Serre, Jean-Pierre},
  year      = {1979},
  publisher = {Springer}
}

@book{neukirch1999algebraic,
  title     = {Algebraic Number Theory},
  author    = {Neukirch, Jürgen},
  year      = {1999},
  publisher = {Springer}
}
```

---

*文档版本: 1.0 | 创建日期: 2026-04-09 | 最后更新: 2026-04-09*

**备注**：本Tag在2026-04-07有最新评论更新，反映Stacks Project社区对惯性理论区域持续活跃的研究兴趣，特别是在p进Hodge理论和完美胚空间推广方面。
