---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Tag 00E1 - 素理想定义

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 00E1 |
| **概念名称** | 素理想 (Prime Ideal) |
| **所属章节** | Chapter 10: Commutative Algebra, Section 10.17 |
| **概念类型** | 定义 (Definition) |
| ** Stacks原文** | Definition 10.17.1 |

---

## 2. 定义原文

**定义陈述：**

设 $R$ 是一个环。$R$ 的理想 $\mathfrak{p}$ 称为**素理想**，如果：

1. $\mathfrak{p} \neq R$（真理想）
2. 若 $a, b \in R$ 且 $ab \in \mathfrak{p}$，则 $a \in \mathfrak{p}$ 或 $b \in \mathfrak{p}$

等价地，$\mathfrak{p}$ 是素理想当且仅当商环 $R/\mathfrak{p}$ 是整环。

**英文原文：**
> Let $R$ be a ring. A ideal $\mathfrak{p} \subset R$ is said to be a *prime ideal* if 
> 1. $\mathfrak{p} \neq R$, and 
> 2. $a, b \in R$ and $ab \in \mathfrak{p}$ implies $a \in \mathfrak{p}$ or $b \in \mathfrak{p}$.

---

## 3. 概念依赖图

```
Tag 00E1: 素理想
│
├── 前置概念
│   ├── 环 (Ring) [Tag 001H]
│   ├── 理想 (Ideal) [Tag 001W]
│   ├── 商环 (Quotient Ring) [Tag 00DR]
│   └── 整环 (Integral Domain) [Tag 00BC]
│
├── 等价刻画
│   ├── 原始定义：乘积条件
│   ├── 代数刻画：$R/\mathfrak{p}$ 是整环
│   └── 理想刻画：$\mathfrak{p}$ 是真理想，且若 $IJ \subseteq \mathfrak{p}$ 则 $I \subseteq \mathfrak{p}$ 或 $J \subseteq \mathfrak{p}$
│
├── 基本性质
│   ├── 存在性：任意非零环都有素理想 [Tag 00E0]
│   ├── 极大理想都是素理想 [Tag 00E2]
│   ├── 素理想的交 [Tag 00E4]
│   └── 素理想的原像 [Tag 00E3]
│
└── 后续应用
    ├── 素谱 $\text{Spec}(R)$ [Tag 00DZ]
    ├── 局部化 $R_{\mathfrak{p}}$ [Tag 00E5]
    ├── 整扩张 [Tag 00GH]
    └── Krull维数 [Tag 00KF]
```

---

## 4. 基本性质证明概要

### 4.1 等价刻画

**命题：** 以下条件等价：
1. $\mathfrak{p}$ 是素理想（定义）
2. $R/\mathfrak{p}$ 是整环
3. $R \setminus \mathfrak{p}$ 对乘法封闭

**证明：**

**(1) $\Rightarrow$ (2):**  
设 $\bar{a}, \bar{b} \in R/\mathfrak{p}$ 且 $\bar{a} \cdot \bar{b} = \bar{0}$。  
这意味着 $ab \in \mathfrak{p}$。由素理想定义，$a \in \mathfrak{p}$ 或 $b \in \mathfrak{p}$，即 $\bar{a} = \bar{0}$ 或 $\bar{b} = \bar{0}$。

**(2) $\Rightarrow$ (1):**  
反之，若 $R/\mathfrak{p}$ 是整环，则 $ab \in \mathfrak{p}$ 意味着在 $R/\mathfrak{p}$ 中 $\bar{a}\bar{b} = \bar{0}$，由整环性质得 $\bar{a} = \bar{0}$ 或 $\bar{b} = \bar{0}$。

**(1) $\Leftrightarrow$ (3):**  
$ab \in \mathfrak{p} \Rightarrow a \in \mathfrak{p}$ 或 $b \in \mathfrak{p}$  当且仅当  $a, b \notin \mathfrak{p} \Rightarrow ab \notin \mathfrak{p}$。

### 4.2 与极大理想的关系

**命题：** 任意极大理想都是素理想。

**证明：**

设 $\mathfrak{m}$ 是极大理想。则 $R/\mathfrak{m}$ 是域（极大理想的定义）。  
域是整环，因此由等价刻画，$\mathfrak{m}$ 是素理想。

**注：** 逆命题不成立。例如在 $\mathbb{Z}$ 中，$(0)$ 是素理想但不是极大理想。

### 4.3 素理想的原像

**命题：** 设 $\varphi: R \to S$ 是环同态，$\mathfrak{q} \subseteq S$ 是素理想，则 $\varphi^{-1}(\mathfrak{q})$ 是 $R$ 的素理想。

**证明：**

考虑诱导的单射 $R/\varphi^{-1}(\mathfrak{q}) \hookrightarrow S/\mathfrak{q}$。  
$S/\mathfrak{q}$ 是整环，其子环也是整环，因此 $R/\varphi^{-1}(\mathfrak{q})$ 是整环。

### 4.4 理想的根与素理想

**命题：** 任意理想 $I$ 的根 $\sqrt{I}$ 等于包含 $I$ 的所有素理想的交：
$$\sqrt{I} = \bigcap_{\mathfrak{p} \supseteq I} \mathfrak{p}$$

---

## 5. 与FormalMath对应

### 5.1 概念映射

| Stacks Project概念 | FormalMath对应内容 | 文件路径 |
|-------------------|-------------------|----------|
| 素理想 | PrimeIdeal | `concept/交换代数/理想理论.md` |
| 整环 | IsDomain | `concept/抽象代数/环.md` |
| 素谱 | PrimeSpectrum | `concept/代数几何/素谱.md` |
| 局部化 | Localization | `concept/交换代数/局部化.md` |
| 商环 | QuotientRing | `concept/抽象代数/商环.md` |

### 5.2 知识体系位置

```
FormalMath知识体系
├── 抽象代数基础
│   └── 环论
│       ├── 环的定义
│       ├── 理想 ←── 前置
│       ├── 素理想 ←── Tag 00E1
│       ├── 极大理想 ←── Tag 00E2
│       └── 整环 ←── 等价刻画
│
└── 交换代数
    └── 理想理论
        ├── 素理想
        ├── 准素分解
        └── Krull维数
```

### 5.3 学习路径建议

```
学习路径：
群论基础
    ↓
环的定义
    ├── 子环
    ├── 理想 ←── 关键前置
    ├── 商环 ←── 等价刻画需要
    └── 素理想 ←── Tag 00E1
            ↓
    交换代数
        ├── 素谱 → 代数几何
        └── 局部化 → 层论
```

---

## 6. 应用与重要性

### 6.1 理论重要性

**交换代数的基石：**

素理想是交换代数中最基本、最重要的概念之一。它是连接**抽象代数**与**代数几何**的桥梁。

**核心作用：**
1. **素谱的构造**：$\text{Spec}(R)$ 是所有素理想的集合，是代数几何的基本空间
2. **局部化**：在素理想处局部化 $R_{\mathfrak{p}}$ 是局部环，反映"局部"信息
3. **维数理论**：Krull维数由素理想链的长度定义

### 6.2 实际应用场景

#### 场景1：代数几何中的点

**几何解释：** 素理想 $\mathfrak{p} \subseteq k[x_1, \ldots, x_n]$ 对应仿射空间 $\mathbb{A}^n_k$ 中的一个**不可约子簇**。

**特例：**
- 极大理想对应闭点（经典点）
- 非极大素理想对应非闭点（概形理论的新点）

**例：** 在 $\mathbb{C}[x]$ 中：
- $(x - a)$ 对应点 $a \in \mathbb{C}$
- $(0)$ 对应泛点（generic point）

#### 场景2：数论中的应用

**整数环 $\mathbb{Z}$：** 素理想为 $(0)$ 和 $(p)$，其中 $p$ 是素数。

**代数整数环：** 研究素理想的分解（素理想分解），是代数数论的核心问题。

**例：** 在 $\mathbb{Z}[i]$ 中：
- $(1+i)$ 是素理想，范数为2
- $(p)$ 当 $p \equiv 1 \pmod{4}$ 时分裂：$(p) = \mathfrak{p}\bar{\mathfrak{p}}$

#### 场景3：函数环中的零点集

设 $X$ 是拓扑空间，$C(X)$ 是连续函数环。

**命题：** $C(X)$ 的极大理想与 $X$ 的点一一对应（若 $X$ 是紧Hausdorff的）。

素理想则对应更一般的"广义点"。

### 6.3 现代发展

- **概形理论**：素理想作为点的推广
- **非交换几何**：非交换环的"素理想"
- **实代数几何**：实素理想与实簇

---

## 7. 与其他资源关联

### 7.1 Stacks Project内部关联

| 相关Tag | 关系类型 | 说明 |
|--------|---------|------|
| **Tag 00E2** (极大理想) | 强化版本 | 极大理想都是素理想 |
| **Tag 00DZ** (素谱) | 几何应用 | $\text{Spec}(R)$ 的定义基础 |
| **Tag 00E5** (局部化) | 代数应用 | $R_{\mathfrak{p}}$ 在素理想处局部化 |
| **Tag 00KF** (Krull维数) | 维数理论 | 维数由素理想链定义 |
| **Tag 00GH** (整扩张) | 扩张理论 |  lying over 定理涉及素理想 |
| **Tag 01F5** (导出函子) | 高阶应用 | 层上同调需要素理想基础 |

### 7.2 外部参考资源

**经典教材：**

1. **Atiyah-Macdonald, Introduction to Commutative Algebra**
   - Chapter 1: 素理想的基本理论
   - 最经典的交换代数入门教材

2. **Matsumura, Commutative Ring Theory**
   - Chapter 2: 理想理论
   - 更深入、更系统的论述

3. **Dummit-Foote, Abstract Algebra**
   - Chapter 7: 素理想与极大理想
   - 作为抽象代数课程的标准参考

4. **Reid, Undergraduate Commutative Algebra**
   - 本科水平的友好介绍
   - 包含大量例子

**在线资源：**
- [Stacks Project 第10章](https://stacks.math.columbia.edu/tag/00E1)
- [Wikipedia: Prime Ideal](https://en.wikipedia.org/wiki/Prime_ideal)
- [nLab: prime ideal](https://ncatlab.org/nlab/show/prime+ideal)

---

## 8. Lean4形式化展望

### 8.1 形式化难度评估

| 方面 | 难度 | 说明 |
|------|------|------|
| 概念复杂度 | ★☆☆☆☆ | 基础概念，定义清晰 |
| 证明技术 | ★☆☆☆☆ | 基本代数技巧 |
| 依赖链条 | ★★☆☆☆ | 需要环和理想的基础 |
| 预计工作量 | 小 | 需要1-2周 |

### 8.2 mathlib4现状

**当前已有基础：**
```
mathlib4
├── Algebra
│   ├── Ring ✅
│   ├── Ideal ✅
│   └── Prime (素性) ✅
│
└── RingTheory
    ├── PrimeIdeal ✅  -- 已有完整定义
    └── Spectrum ✅   -- 素谱的定义
```

**已有的相关定义：**

```lean
-- 素理想的定义 (mathlib4)
structure PrimeIdeal (R : Type*) [CommRing R] extends Ideal R where
  ne_top' : carrier ≠ ⊤
  mem_or_mem' : ∀ {x y : R}, x * y ∈ carrier → x ∈ carrier ∨ y ∈ carrier

-- 等价刻画：商环是整域
theorem PrimeIdeal.quotient_isDomain (P : PrimeIdeal R) :
    IsDomain (R ⧸ P.toIdeal) := ...
```

### 8.3 形式化路线图

**阶段1：基本定义（已完成）**

mathlib4 已经完整定义了素理想：

```lean
import Mathlib.RingTheory.Prime
import Mathlib.RingTheory.Ideal.Quotient

variable {R : Type*} [CommRing R]

-- 素理想的定义
structure Ideal.IsPrime (I : Ideal R) : Prop where
  ne_top : I ≠ ⊤
  mem_or_mem : ∀ {x y : R}, x * y ∈ I → x ∈ I ∨ y ∈ I
```

**阶段2：基本性质证明（已完成）**

```lean
-- 商环是整域 ↔ 理想是素理想
theorem Ideal.isPrime_iff_quotient_isDomain (I : Ideal R) :
    I.IsPrime ↔ IsDomain (R ⧸ I) := ...

-- 极大理想是素理想
theorem Ideal.IsMaximal.isPrime {I : Ideal R} (h : I.IsMaximal) : I.IsPrime := ...

-- 素理想的原像
theorem Ideal.comap_isPrime {S : Type*} [CommRing S] (f : R →+* S)
    (P : Ideal S) [hP : P.IsPrime] : (P.comap f).IsPrime := ...
```

**阶段3：素谱构造（已完成）**

```lean
-- 素谱的定义
def PrimeSpectrum (R : Type*) [CommRing R] : Type _ :=
  { I : Ideal R // I.IsPrime }

-- Zariski拓扑
def PrimeSpectrum.zariskiTopology (R : Type*) [CommRing R] :
    TopologicalSpace (PrimeSpectrum R) := ...
```

### 8.4 教学示例

```lean
-- ℤ中的素理想
example : (Ideal.span {p}).IsPrime ↔ Nat.Prime p := by
  sorry

-- 多项式环中的素理想
example {k : Type*} [Field k] (a : k) :
    (Ideal.span {X - C a} : Ideal (Polynomial k)).IsPrime := by
  sorry

-- 零理想是素理想当且仅当环是整域
example : (⊥ : Ideal R).IsPrime ↔ IsDomain R := by
  sorry
```

### 8.5 与其他形式化项目的联系

- **Lean-Stacks**: 包含素理想的完整形式化
- **mathlib4**: 有最完整的环论形式化
- **ForMath**: 欧盟形式化数学项目

---

## 附录

### A. 符号速查表

| 符号 | 含义 | LaTeX |
|------|------|-------|
| $\mathfrak{p}$ | 素理想 | `\mathfrak{p}` |
| $\text{Spec}(R)$ | 素谱 | `\text{Spec}` |
| $R_{\mathfrak{p}}$ | 在 $\mathfrak{p}$ 处的局部化 | `R_{\mathfrak{p}}` |
| $R/\mathfrak{p}$ | 商环 | `R/\mathfrak{p}` |
| $\sqrt{I}$ | 理想 $I$ 的根 | `\sqrt{I}` |

### B. 素理想的例子

| 环 | 素理想 | 说明 |
|----|-------|------|
| $\mathbb{Z}$ | $(0), (p)$ | $p$ 为素数 |
| $k[x]$ | $(0), (f(x))$ | $f$ 为不可约多项式 |
| $k[x,y]$ | $(0), (f), (x-a, y-b)$ | 多种类型 |
| $\mathbb{Z}[x]$ | $(p), (f(x)), (p, f(x))$ | 更复杂的结构 |
| $C[0,1]$ | 极大理想 $M_x = \{f : f(x) = 0\}$ | 连续函数环 |

---

*文档版本: 1.0*  
*创建日期: 2026年4月*  
*对应Stacks Project版本: 2024.02*
