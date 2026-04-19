---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Tag 00E2 - 极大理想定义

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 00E2 |
| **概念名称** | 极大理想 (Maximal Ideal) |
| **所属章节** | Chapter 10: Commutative Algebra, Section 10.17 |
| **概念类型** | 定义 (Definition) |
| ** Stacks原文** | Definition 10.17.1 (部分) / Lemma 10.17.2 |

---

## 2. 定义原文

**定义陈述：**

设 $R$ 是一个环。$R$ 的理想 $\mathfrak{m}$ 称为**极大理想**，如果：

1. $\mathfrak{m} \neq R$（真理想）
2. 对任意理想 $I \subseteq R$，若 $\mathfrak{m} \subseteq I$，则 $I = \mathfrak{m}$ 或 $I = R$

等价地，$\mathfrak{m}$ 是极大理想当且仅当商环 $R/\mathfrak{m}$ 是域。

**英文原文：**
> An ideal $\mathfrak{m} \subset R$ is called a *maximal ideal* if 
> 1. $\mathfrak{m} \neq R$, and 
> 2. for any ideal $I \subset R$ with $\mathfrak{m} \subset I$ we have $I = \mathfrak{m}$ or $I = R$.
> 
> Equivalently, $\mathfrak{m}$ is maximal if and only if $R/\mathfrak{m}$ is a field.

---

## 3. 概念依赖图

```
Tag 00E2: 极大理想
│
├── 前置概念
│   ├── 环 (Ring) [Tag 001H]
│   ├── 理想 (Ideal) [Tag 001W]
│   ├── 商环 (Quotient Ring) [Tag 00DR]
│   ├── 域 (Field) [Tag 0032]
│   └── 素理想 (Prime Ideal) [Tag 00E1]
│
├── 等价刻画
│   ├── 原始定义：理想偏序集的极大元
│   ├── 代数刻画：$R/\mathfrak{m}$ 是域
│   └── 集合刻画：不存在严格包含它的真理想
│
├── 基本性质
│   ├── 存在性：非零环都有极大理想 (Zorn引理) [Tag 00E0]
│   ├── 极大理想都是素理想 [Tag 00E1]
│   ├── Jacobson根 [Tag 00DT]
│   └── 中国剩余定理 [Tag 00DV]
│
└── 后续应用
    ├── 局部环 $R_{\mathfrak{m}}$ [Tag 00E8]
    ├── Hilbert零点定理 [Tag 00FV]
    ├── Zariski拓扑的闭点 [Tag 00E0]
    └── 代数的几何：点与极大理想
```

---

## 4. 基本性质证明概要

### 4.1 等价刻画

**命题：** 以下条件等价：
1. $\mathfrak{m}$ 是极大理想（定义）
2. $R/\mathfrak{m}$ 是域
3. 对任意 $x \notin \mathfrak{m}$，有 $(\mathfrak{m}, x) = R$

**证明：**

**(1) $\Leftrightarrow$ (2):**  

设 $\mathfrak{m}$ 是极大理想。考虑 $R/\mathfrak{m}$ 中的非零元 $\bar{a}$。  
则 $a \notin \mathfrak{m}$，所以 $(\mathfrak{m}, a) = R$（由极大性）。  
因此存在 $r \in R$ 和 $m \in \mathfrak{m}$ 使得 $ra + m = 1$。  
在 $R/\mathfrak{m}$ 中，$\bar{r}\bar{a} = \bar{1}$，即 $\bar{a}$ 可逆。

反之，若 $R/\mathfrak{m}$ 是域，设 $\mathfrak{m} \subsetneq I$。  
取 $a \in I \setminus \mathfrak{m}$，则 $\bar{a} \neq \bar{0}$ 在 $R/\mathfrak{m}$ 中可逆。  
因此存在 $b$ 使得 $\bar{a}\bar{b} = \bar{1}$，即 $ab - 1 \in \mathfrak{m} \subset I$。  
所以 $1 = ab - (ab - 1) \in I$，即 $I = R$。

### 4.2 极大理想的存在性

**定理（Krull）：** 任意非零含幺环都有极大理想。

**证明：**

使用**Zorn引理**。考虑集合：
$$\mathcal{S} = \{I \subseteq R : I \text{ 是真理想}\}$$

以包含关系为偏序。

**验证条件：**
1. $\mathcal{S} \neq \emptyset$（因为 $(0) \in \mathcal{S}$）
2. 任意链有上界：设 $\{I_\alpha\}$ 是链，则 $\bigcup_\alpha I_\alpha$ 是理想且是真理想（不含1）

由Zorn引理，$\mathcal{S}$ 有极大元，即极大理想。

### 4.3 极大理想与素理想

**命题：** 极大理想都是素理想。

**证明：**

设 $\mathfrak{m}$ 是极大理想。则 $R/\mathfrak{m}$ 是域。  
域是整环，因此由素理想的等价刻画，$\mathfrak{m}$ 是素理想。

**注：** 逆命题不成立。例如 $\mathbb{Z}$ 中的 $(0)$ 是素理想但不是极大理想。

### 4.4 Jacobson根

**定义：** 环 $R$ 的**Jacobson根** $J(R)$ 定义为所有极大理想的交：
$$J(R) = \bigcap_{\mathfrak{m} \text{ 极大}} \mathfrak{m}$$

**刻画：** $x \in J(R)$ 当且仅当 $1 - xy$ 对任意 $y \in R$ 都是单位。

---

## 5. 与FormalMath对应

### 5.1 概念映射

| Stacks Project概念 | FormalMath对应内容 | 文件路径 |
|-------------------|-------------------|----------|
| 极大理想 | MaximalIdeal | `concept/交换代数/理想理论.md` |
| 域 | Field / IsField | `concept/抽象代数/域.md` |
| Jacobson根 | JacobsonRadical | `concept/交换代数/根理想.md` |
| 局部化 | Localization.AtPrime | `concept/交换代数/局部化.md` |
| Zariski拓扑 | ZariskiTopology | `concept/代数几何/素谱.md` |

### 5.2 知识体系位置

```
FormalMath知识体系
├── 抽象代数基础
│   └── 环论
│       ├── 理想
│       ├── 素理想 [Tag 00E1]
│       └── 极大理想 ←── Tag 00E2
│
├── 交换代数
│   ├── 理想理论
│   │   ├── 素理想分解
│   │   └── 维数理论
│   │
│   └── 局部化
│       └── 局部环 ←── 在极大理想处局部化
│
└── 代数几何
    └── 素谱
        ├── 闭点 ←── 极大理想
        └── 一般点 ←── 非极大素理想
```

### 5.3 学习路径建议

```
学习路径：
环的定义与例子
    ├── 子环与理想
    ├── 商环 ←── 理解 $R/\mathfrak{m}$
    ├── 素理想 ←── 对比学习
    └── 极大理想 ←── Tag 00E2
            ↓
    交换代数进阶
        ├── Jacobson根
        ├── 局部环
        └── Hilbert零点定理
```

---

## 6. 应用与重要性

### 6.1 理论重要性

**交换代数的柱石：**

极大理想是理解环结构的关键。它们对应于环的"点"，是连接代数与几何的桥梁。

**核心作用：**
1. **局部化**：在极大理想处局部化得到局部环
2. **几何点**：极大理想对应几何空间中的点
3. **Jacobson环**：Jacobson根刻画了环的"局部"性质

### 6.2 实际应用场景

#### 场景1：代数几何中的闭点

**几何解释：** 在代数闭域 $k$ 上，$k[x_1, \ldots, x_n]$ 的极大理想与 $\mathbb{A}^n_k$ 中的点一一对应。

**Hilbert零点定理：**

设 $k$ 是代数闭域，则 $k[x_1, \ldots, x_n]$ 的极大理想都具有形式：
$$\mathfrak{m}_a = (x_1 - a_1, \ldots, x_n - a_n)$$

其中 $a = (a_1, \ldots, a_n) \in k^n$。

**意义：** 代数闭域上的"点"可以用纯粹代数的方式描述。

#### 场景2：局部环

**定义：** 局部环是只有一个极大理想的环。

**构造：** 对任意素理想 $\mathfrak{p}$，局部化 $R_{\mathfrak{p}}$ 是局部环，其唯一极大理想为 $\mathfrak{p}R_{\mathfrak{p}}$。

**应用：**
- 研究概形的局部性质
- 层论中的茎（stalk）
- 相交重数的计算

#### 场景3：代数整数环

设 $\mathcal{O}_K$ 是数域 $K$ 的整数环。

**基本问题：** 素数 $p \in \mathbb{Z}$ 在 $\mathcal{O}_K$ 中如何分解？

$$(p) = \mathfrak{p}_1^{e_1} \cdots \mathfrak{g}_r^{e_r}$$

其中 $\mathfrak{p}_i$ 是 $\mathcal{O}_K$ 的极大理想（也是素理想）。

#### 场景4：Banach代数

在泛函分析中，交换Banach代数的极大理想空间对应于Gelfand谱。

**Gelfand变换：**
$$\hat{a}(\mathfrak{m}) = a \mod \mathfrak{m} \in \mathbb{C}$$

建立了代数与函数空间的联系。

### 6.3 现代发展

- **概形理论**：极大理想作为闭点的推广
- **非交换几何**：非交换环的"极大理想"
- **实代数几何**：实极大理想与实点

---

## 7. 与其他资源关联

### 7.1 Stacks Project内部关联

| 相关Tag | 关系类型 | 说明 |
|--------|---------|------|
| **Tag 00E1** (素理想) | 弱化版本 | 极大理想都是素理想 |
| **Tag 00E0** (极大理想存在性) | 理论基础 | Zorn引理的应用 |
| **Tag 00E8** (局部环) | 代数应用 | 极大理想处局部化 |
| **Tag 00FV** (Hilbert零点定理) | 几何应用 | 极大理想与点的对应 |
| **Tag 00DT** (Jacobson根) | 代数结构 | 所有极大理想的交 |
| **Tag 00DV** (中国剩余定理) | 代数应用 | 极大理想与商环分解 |

### 7.2 外部参考资源

**经典教材：**

1. **Atiyah-Macdonald, Introduction to Commutative Algebra**
   - Chapter 1: 极大理想与素理想
   - 第1章命题1.2：极大理想的存在性

2. **Matsumura, Commutative Ring Theory**
   - Chapter 1: 环与理想
   - 更系统的理论发展

3. **Dummit-Foote, Abstract Algebra**
   - Chapter 7.4: 极大理想
   - 包含大量例子和习题

4. **Eisenbud, Commutative Algebra**
   - Chapter 2: 根、局部化、初等分解
   - 几何视角的阐述

**在线资源：**
- [Stacks Project 第10章](https://stacks.math.columbia.edu/tag/00E2)
- [Wikipedia: Maximal Ideal](https://en.wikipedia.org/wiki/Maximal_ideal)
- [MathWorld: Maximal Ideal](https://mathworld.wolfram.com/MaximalIdeal.html)

---

## 8. Lean4形式化展望

### 8.1 形式化难度评估

| 方面 | 难度 | 说明 |
|------|------|------|
| 概念复杂度 | ★☆☆☆☆ | 基础概念，定义清晰 |
| 证明技术 | ★★☆☆☆ | 需要Zorn引理 |
| 依赖链条 | ★★☆☆☆ | 需要选择公理 |
| 预计工作量 | 小 | 需要1-2周 |

### 8.2 mathlib4现状

**当前已有基础：**
```
mathlib4
├── Algebra
│   ├── Ring ✅
│   ├── Ideal ✅
│   └── Field ✅
│
└── RingTheory
    ├── Ideal ✅
    ├── MaximalIdeal ✅  -- 已有完整定义
    └── JacobsonRadical ✅
```

**已有的相关定义：**

```lean
-- 极大理想的定义 (mathlib4)
structure Ideal.IsMaximal {R : Type*} [Semiring R] (I : Ideal R) : Prop where
  out : IsCoatom I
  -- IsCoatom 意味着 I ≠ ⊤ 且对任意 J, I < J 蕴含 J = ⊤

-- 等价刻画
theorem Ideal.IsMaximal.iff_quotient_isField {R : Type*} [CommRing R] {I : Ideal R} :
    I.IsMaximal ↔ IsField (R ⧸ I) := ...
```

### 8.3 形式化路线图

**阶段1：基本定义（已完成）**

```lean
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient

variable {R : Type*} [CommRing R]

-- 极大理想的定义
structure Ideal.IsMaximal (I : Ideal R) : Prop where
  ne_top : I ≠ ⊤
  eq_top_of_lt : ∀ J, I < J → J = ⊤
```

**阶段2：基本性质（已完成）**

```lean
-- 商环是域 ↔ 理想是极大理想
theorem Ideal.isMaximal_iff {I : Ideal R} :
    I.IsMaximal ↔ IsField (R ⧸ I) := ...

-- 极大理想是素理想
theorem Ideal.IsMaximal.isPrime {I : Ideal R} (h : I.IsMaximal) : I.IsPrime := ...

-- 极大理想的存在性 (需要Zorn引理)
theorem Ideal.exists_maximal (R : Type*) [Ring R] [Nontrivial R] :
    ∃ I : Ideal R, I.IsMaximal := ...
```

**阶段3：应用（部分完成）**

```lean
-- Jacobson根的定义
def JacobsonRadical (R : Type*) [CommRing R] : Ideal R :=
  sInf {I : Ideal R | I.IsMaximal}

-- 中国剩余定理
theorem chinese_remainder_theorem {I J : Ideal R} (h : I.IsMaximal) (h' : J.IsMaximal)
    (hcoprime : I ≠ J) :
    R ⧸ (I ⊓ J) ≃+* (R ⧸ I) × (R ⧸ J) := ...
```

### 8.4 教学示例

```lean
-- ℤ中的极大理想
example (p : ℕ) (hp : Nat.Prime p) :
    (Ideal.span {(p : ℤ)}).IsMaximal := by
  sorry

-- 域上多项式环的极大理想
example {k : Type*} [Field k] (a : k) :
    (Ideal.span {X - C a} : Ideal (Polynomial k)).IsMaximal := by
  sorry

-- 主理想整环中的非零素理想都是极大理想
theorem PID_prime_eq_maximal {R : Type*} [CommRing R] [IsPrincipalIdealRing R]
    [IsDomain R] {I : Ideal R} (hne : I ≠ ⊥) (hp : I.IsPrime) : I.IsMaximal := by
  sorry
```

---

## 附录

### A. 符号速查表

| 符号 | 含义 | LaTeX |
|------|------|-------|
| $\mathfrak{m}$ | 极大理想 | `\mathfrak{m}` |
| $R/\mathfrak{m}$ | 商环（域） | `R/\mathfrak{m}` |
| $J(R)$ | Jacobson根 | `J(R)` |
| $\text{mSpec}(R)$ | 极大谱 | `\text{mSpec}` |
| $\text{Spec}(R)$ | 素谱 | `\text{Spec}` |

### B. 极大理想的例子

| 环 | 极大理想 | 商环 |
|----|---------|------|
| $\mathbb{Z}$ | $(p)$，$p$ 为素数 | $\mathbb{F}_p$ |
| $k[x]$ | $(f(x))$，$f$ 不可约 | 有限扩张 |
| $k[x_1,\ldots,x_n]$（$k$ 代数闭） | $(x_1-a_1, \ldots, x_n-a_n)$ | $k$ |
| $C[0,1]$ | $M_a = \{f : f(a) = 0\}$ | $\mathbb{R}$ |
| $\mathbb{Z}[i]$ | $(1+i), (p)$（$p \equiv 3 \pmod{4}$） | 有限域 |

### C. 素理想 vs 极大理想

| 性质 | 素理想 | 极大理想 |
|------|--------|---------|
| $R/\mathfrak{p}$ 是整环 | ✓ | ✓ |
| $R/\mathfrak{p}$ 是域 | 不一定 | ✓ |
| 存在性 | 任意非零环 | 任意非零环 |
| 个数 | 可能无限 | 可能无限 |
| 包含关系 | 可能有真包含 | 极大元 |

---

*文档版本: 1.0*  
*创建日期: 2026年4月*  
*对应Stacks Project版本: 2024.02*
