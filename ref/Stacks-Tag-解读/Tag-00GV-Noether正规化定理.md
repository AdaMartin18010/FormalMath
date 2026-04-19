---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 00GV 解读：Noether正规化定理

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 00GV |
| **章节** | Commutative Algebra, Section 10.115: Noether normalization |
| **类型** | 定理 (Theorem) |
| **重要性** | ⭐⭐⭐⭐⭐ (交换代数基石) |
| **Stacks Project链接** | https://stacks.math.columbia.edu/tag/00GV |

---

## 2. 定理原文与翻译

### 英文原文

**Theorem 10.115.4 (Noether normalization).** Let $k$ be a field. Let $S$ be a finite type $k$-algebra. Let $\mathfrak{p} \subset \mathfrak{q}$ be distinct primes of $S$. Then there exist $n \geq 0$ and an injective finite type ring map $k[y_1, \ldots, y_n] \to S$ such that

1. the induced map on spectra identifies $k[y_1, \ldots, y_n]$ with a subring of $S$,
2. the primes $\mathfrak{p}$ and $\mathfrak{q}$ lie over distinct primes $\mathfrak{p}'$ and $\mathfrak{q}'$ of $k[y_1, \ldots, y_n]$, and
3. $\mathfrak{p}' \subset \mathfrak{q}'$ and $\dim((k[y_1, \ldots, y_n])_{\mathfrak{q}'}/\mathfrak{p}'_{\mathfrak{q}'}) = \dim(S_{\mathfrak{q}}/\mathfrak{p}_{\mathfrak{q}})$.

In particular, if $S$ is a domain, then $n = \dim(S)$.

### 中文翻译

**定理 10.115.4 (Noether正规化).** 设 $k$ 是域，$S$ 是有限生成 $k$-代数，$\mathfrak{p} \subset \mathfrak{q}$ 是 $S$ 的两个不同素理想。则存在 $n \geq 0$ 和单射型有限环映射 $k[y_1, \ldots, y_n] \to S$ 使得：

1. 谱上的诱导映射将 $k[y_1, \ldots, y_n]$ 等同于 $S$ 的子环；
2. 素理想 $\mathfrak{p}$ 和 $\mathfrak{q}$ 位于 $k[y_1, \ldots, y_n]$ 的不同素理想 $\mathfrak{p}'$ 和 $\mathfrak{q}'$ 之上；
3. $\mathfrak{p}' \subset \mathfrak{q}'$ 且 $\dim((k[y_1, \ldots, y_n])_{\mathfrak{q}'}/\mathfrak{p}'_{\mathfrak{q}'}) = \dim(S_{\mathfrak{q}}/\mathfrak{p}_{\mathfrak{q}})$。

特别地，若 $S$ 是整环，则 $n = \dim(S)$。

---

## 3. 概念依赖图

```
Tag 00GV: Noether正规化定理
│
├── 前置概念
│   ├── 有限生成代数
│   │   └── k[x_1,...,x_m]/I 形式
│   ├── 整扩张
│   │   └── 每个元素满足首一多项式
│   ├── 整相关与有限性
│   │   └── S是有限k[y_1,...,y_n]-模
│   ├── 维数理论 (Tag 00KD)
│   │   └── Krull维数
│   └── 域上的代数
│
├── 核心定理
│   └── Noether正规化
│       ├── 存在多项式子环
│       ├── 整扩张关系
│       └── 维数保持
│
├── 证明技术
│   ├── 变量替换技巧
│   ├── 单项式序与首项
│   ├── 归纳法
│   └── 投射技巧
│
├── 变体与推广
│   ├── 经典版本（域上）
│   ├── 几何解释
│   ├── 相对版本（环上）
│   └── 分次版本
│
└── 相关Tags
    ├── Tag 00KD: Krull维数
    ├── Tag 00GJ: 整扩张的维数
    ├── Tag 02JP: 概形的有限态射
    └── Tag 0C2L: Noether正规化的应用
```

---

## 4. 详细证明

### 4.1 定理的直观理解

**核心思想**：任何仿射代数簇都可以被"有限地"投射到仿射空间上。

**几何解释**：设 $X = \text{Spec}(S)$ 是 $k$ 上的有限型概形，则存在有限满射：

$$\pi: X \twoheadrightarrow \mathbb{A}^n_k$$

其中 $n = \dim(X)$。这意味着 $X$ 在 $\mathbb{A}^n$ 上是"有限覆叠"。

### 4.2 经典版本证明

**定理 (经典Noether正规化)**：设 $k$ 是无限域，$S = k[x_1, \ldots, x_m]/I$ 是有限生成 $k$-代数，则存在 $n$ 个 $k$-线性组合：

$$y_i = \sum_{j=1}^m a_{ij} x_j \quad (a_{ij} \in k)$$

使得 $k[y_1, \ldots, y_n] \subset S$ 是整扩张，且 $n = \dim(S)$（若 $S$ 整）。

**证明步骤**：

**步骤1: 化归到多项式环**

设 $S = k[x_1, \ldots, x_m]/I$，先考虑 $k[x_1, \ldots, x_m]$ 的情形。

**步骤2: 首项技巧**

取 $I$ 的生成元 $f_1, \ldots, f_r$。对每个 $f_i$，做变量替换使得 $f_i$ 对每个新变量都是首一的。

**步骤3: 归纳构造**

对 $f \in I$ 非零，设其总次数为 $d$。做线性变换：

$$x_i = y_i + x_m^{e_i} \quad (i < m)$$

选取适当的 $e_i$ 使得 $f$ 作为 $x_m$ 的多项式是首一的。

**步骤4: 维数计算**

由整扩张的维数不变性，$\dim(S) = \dim(k[y_1, \ldots, y_n]) = n$。

### 4.3 一般版本证明

对于给定素理想链 $\mathfrak{p} \subset \mathfrak{q}$ 的情形：

1. 先对 $S/\mathfrak{p}$ 应用经典版本，得到 $k[y_1, \ldots, y_n] \subset S/\mathfrak{p}$
2. 提升到 $S$，确保 $\mathfrak{p}$ 位于 $\mathfrak{p}'$ 上
3. 调整变量使得 $\mathfrak{q}$ 位于 $\mathfrak{q}'$ 上且维数匹配

### 4.4 有限域的处理

当 $k$ 有限时，线性变换不足以保证首一性，需要使用：

**Nagata技巧**：变量替换形如
$$x_i = y_i + x_m^{e_i}$$

其中指数 $e_i$ 选择为足够大且满足特定增长条件。

---

## 5. 与FormalMath的对应关系

| FormalMath概念 | 对应内容 | 文档位置 |
|----------------|----------|----------|
| 有限生成代数 | Finitely generated algebra | `concept/交换代数/有限生成代数.md` |
| 整扩张 | Integral extension | `concept/交换代数/整扩张.md` |
| Krull维数 | Tag 00KD | `concept/交换代数/Krull维数.md` |
| 有限态射 | Finite morphism | `concept/代数几何/有限态射.md` |
| 仿射概形 | Affine scheme | `concept/代数几何/仿射概形.md` |

### 学习路径

```
FormalMath: 交换代数核心
├── 前置
│   ├── 有限生成代数
│   ├── 整扩张理论
│   └── 维数理论 (Tag 00KD)
├── 当前 ← Tag 00GV
│   └── Noether正规化定理
└── 后续
    ├── Hilbert零点定理
    ├── 维数理论深化
    ├── 有限态射
    └── 代数几何中的应用
```

---

## 6. 应用与重要性

### 6.1 核心应用

| 应用 | 说明 |
|------|------|
| Hilbert零点定理 | 证明弱形式的关键步骤 |
| 维数计算 | $\dim(S) = n$ 的系统性计算 |
| 有限性定理 | 证明各种有限性结果 |
| 正规化引理 | 局部环论中的应用 |
| 模空间理论 | 参数空间的有理性问题 |

### 6.2 Hilbert零点定理的证明

**弱零点定理**：设 $k$ 代数闭，$I \subset k[x_1, \ldots, x_n]$ 是真理想，则 $V(I) \neq \emptyset$。

**证明概要**：
1. 假设 $I$ 极大，则 $S = k[x_1, \ldots, x_n]/I$ 是域
2. 由Noether正规化，$k[y_1, \ldots, y_m] \subset S$ 整，$S$ 域 ⟹ $k[y_1, \ldots, y_m]$ 域
3. 故 $m = 0$，$S/k$ 是有限扩张
4. $k$ 代数闭 ⟹ $S = k$
5. 设 $a_i = x_i \mod I$，则 $(a_1, \ldots, a_n) \in V(I)$

### 6.3 代数几何中的应用

**有限映射的存在性**：任何仿射簇 $X$ 都有到 $\mathbb{A}^n$（$n = \dim X$）的有限满射。

**几何意义**：
- $X$ 是 $\mathbb{A}^n$ 的"分歧覆叠"
- 可用于研究 $X$ 的拓扑性质
- 提供了将一般问题化归到多项式环的通用方法

### 6.4 推广与变体

| 变体 | 内容 |
|------|------|
| 相对版本 | 对 $R \to S$ 有限型，存在 $R[y_1, \ldots, y_n] \subset S$ 拟有限 |
| 分次版本 | 分次代数的齐次正规化 |
| 混合特征 | 在 $p$ 进情形下的版本 |
| 解析版本 | 解析几何中的类似结果 |

---

## 7. 与其他资源的关联

### 7.1 教科书对应

| 教科书 | 章节 | 内容 |
|--------|------|------|
| Atiyah-Macdonald | Chapter 5 | Noether's normalization lemma |
| Matsumura | Chapter 5 | The normalization theorem |
| Eisenbud | Chapter 13 | Noether normalization |
| Liu Qing | 2.1 | Noether normalization |
| Stacks Project | Tag 00GV | Noether normalization |

### 7.2 nLab条目

- [Noether normalization lemma](https://ncatlab.org/nlab/show/Noether+normalization+lemma)
- [integral extension](https://ncatlab.org/nlab/show/integral+extension)
- [finite morphism](https://ncatlab.org/nlab/show/finite+morphism)

### 7.3 Wikipedia条目

- [Noether normalization lemma](https://en.wikipedia.org/wiki/Noether_normalization_lemma)
- [Hilbert's Nullstellensatz](https://en.wikipedia.org/wiki/Hilbert%27s_Nullstellensatz)

### 7.4 相关Stacks Tags

| Tag | 内容 | 关系 |
|-----|------|------|
| 00KD | Krull维数 | 维数理论 |
| 00GJ | 整扩张的维数 | 性质 |
| 00GW | Noether正规化的证明 | 详细证明 |
| 02JP | 有限态射 | 几何解释 |
| 0C2L | 应用 | 后续 |

---

## 8. Lean4形式化展望

### 8.1 Mathlib4现状

Mathlib4中Noether正规化定理仍在开发中：

```lean
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.KrullDimension

-- 整扩张相关
#check Algebra.IsIntegral
#check RingHom.IsIntegral

-- 有限生成代数
#check Algebra.FiniteType

-- Noether正规化（待实现）
-- #check noetherNormalization
```

### 8.2 形式化路线图

| 组件 | 状态 | 说明 |
|------|------|------|
| 整扩张理论 | 完整 | 基础完整 |
| 有限生成代数 | 完整 | 定义完备 |
| 变量替换构造 | 待开发 | 核心构造 |
| 首一多项式技巧 | 待开发 | 关键步骤 |
| Noether正规化 | 待开发 | Tag 00GV目标 |
| Hilbert零点定理 | 待开发 | 应用 |

### 8.3 形式化代码框架

```lean
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.KrullDimension
import Mathlib.RingTheory.FiniteType

namespace RingTheory

variable {k S : Type*} [Field k] [CommRing S] [Algebra k S]
  [Algebra.FiniteType k S]

-- Noether正规化定理（经典版本）
theorem noether_normalization [IsDomain S] :
    ∃ (n : ℕ) (y : Fin n → S),
      Algebra.IsIntegral (adjoin k (Set.range y)) S ∧
      Algebra.IsPolynomial (adjoin k (Set.range y)) := by
  -- 归纳于生成元个数
  sorry

-- 含素理想链的版本
theorem noether_normalization_with_primes {p q : Ideal S} [p.IsPrime] [q.IsPrime]
    (hpq : p < q) :
    ∃ (n : ℕ) (y : Fin n → S) (p' q' : Ideal (adjoin k (Set.range y)))
      [p'.IsPrime] [q'.IsPrime],
      p' < q' ∧
      Ideal.comap (algebraMap _ S) p = p' ∧
      Ideal.comap (algebraMap _ S) q = q' ∧
      krullDimension (Localization.AtPrime q' ⧸ 
        (Ideal.map (algebraMap _ _) p')) =
      krullDimension (Localization.AtPrime q ⧸ 
        (Ideal.map (algebraMap _ _) p)) := by
  sorry

-- 构造性证明（用于计算）
def noetherNormalizationConstructive {m : ℕ} {x : Fin m → S}
    (hx : Algebra.adjoin k (Set.range x) = ⊤) :
    {n : ℕ // ∃ (y : Fin n → S), Algebra.IsIntegral (adjoin k (Set.range y)) S} :=
  sorry

end RingTheory
```

### 8.4 几何视角的形式化

```lean
import Mathlib.AlgebraicGeometry.AffineScheme

namespace AlgebraicGeometry

variable {k : Type*} [Field k]

-- 有限态射的构造
def finiteMorphismToAffineSpace {X : Scheme} [IsAffine X]
    [IsFiniteType (structureMorphism X)] :
    ∃ (n : ℕ) (f : X ⟶ (AffineSpace k n)),
      IsFinite f ∧ Surjective f := by
  -- 使用Noether正规化
  sorry

-- 维数计算推论
theorem dimension_eq_transcendence_degree {X : Scheme} [IsAffine X]
    [IsIntegral X] [IsFiniteType (structureMorphism X)] :
    X.dimension = transcendenceDegree k (functionField X) := by
  -- 使用Noether正规化
  sorry

end AlgebraicGeometry
```

### 8.5 形式化策略

**建议实现步骤**：

1. **基础准备**：完善多项式环的变量替换理论
2. **首一化引理**：证明给定多项式可通过变量替换首一化
3. **归纳构造**：对生成元个数归纳，逐步构造正规化子环
4. **维数保持**：证明整扩张保持维数
5. **素理想版本**：处理给定素理想链的情形

**挑战**：
- 变量替换的形式化需要仔细处理
- 首一化需要有效的算法描述
- 维数保持需要完整的整扩张理论

---

## 参考引用

```bibtex
@misc{stacks-project,
  author       = {The Stacks Project Authors},
  title        = {Stacks Project},
  howpublished = {\url{https://stacks.math.columbia.edu}},
  year         = {2024},
  note         = {Tag 00GV}
}

@book{atiyah2018introduction,
  title     = {Introduction to Commutative Algebra},
  author    = {Atiyah, Michael Francis and Macdonald, Ian Grant},
  year      = {2018},
  publisher = {CRC Press}
}

@article{noether1926endlichkeit,
  title     = {Der Endlichkeitssatz der Invarianten endlicher linearer Gruppen der Charakteristik p},
  author    = {Noether, Emmy},
  journal   = {Nachrichten von der Gesellschaft der Wissenschaften zu Göttingen, Mathematisch-Physikalische Klasse},
  pages     = {28--35},
  year      = {1926}
}
```

---

*文档版本: 1.0 | 创建日期: 2026-04-09 | 最后更新: 2026-04-09*
