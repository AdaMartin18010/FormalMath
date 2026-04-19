---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 013O - Grothendieck谱序列

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 013O |
| **章节位置** | Chapter 12: Homological Algebra > Section 12.21: Spectral Sequences > Subsection: The Spectral Sequence of a Composition of Functors |
| **数学领域** | 同调代数 / 谱序列理论 |
| **文档类型** | 引理/构造 (Lemma/Construction) |
| **重要性** | ⭐⭐⭐⭐⭐ (同调代数核心工具) |
| **相关Tags** | 013N, 013P, 013Q, 013R (谱序列系列) |

---

## 2. 定理原文

### 英文原文 (Stacks Project)

> **Lemma 12.21.14 (Grothendieck spectral sequence).** Let $\mathcal{A}, \mathcal{B}, \mathcal{C}$ be abelian categories. Let $F : \mathcal{A} \to \mathcal{B}$ and $G : \mathcal{B} \to \mathcal{C}$ be left exact functors. Assume that:
>
> 1. $\mathcal{A}$, $\mathcal{B}$ have enough injectives,
> 2. $F$ transforms injectives into $G$-acyclic objects.
>
> Then for any object $X$ of $\mathcal{A}$ there exists a first quadrant cohomological spectral sequence $(E_r, d_r)_{r \geq 0}$ with
>
> $$E_2^{p,q} = R^pG(R^qF(X))$$
>
> converging to $R^{p+q}(G \circ F)(X)$.

### 中文翻译

> **引理 12.21.14 (Grothendieck谱序列).** 设 $\mathcal{A}, \mathcal{B}, \mathcal{C}$ 是Abel范畴。设 $F : \mathcal{A} \to \mathcal{B}$ 和 $G : \mathcal{B} \to \mathcal{C}$ 是左正合函子。假设：
>
> 1. $\mathcal{A}$、$\mathcal{B}$ 有足够内射对象，
> 2. $F$ 将内射对象变为 $G$-零调对象。
>
> 则对 $\mathcal{A}$ 中任意对象 $X$，存在第一象限的上同调谱序列 $(E_r, d_r)_{r \geq 0}$ 满足
>
> $$E_2^{p,q} = R^pG(R^qF(X))$$
>
> 收敛到 $R^{p+q}(G \circ F)(X)$。

---

## 3. 概念依赖图

```
Grothendieck谱序列 (013O)
│
├── 前置概念
│   ├── Abel范畴 (Abelian Category)
│   ├── 左正合函子 (Left Exact Functor)
│   ├── 内射分解 (Injective Resolution)
│   ├── 导出函子 (Derived Functor)
│   │   ├── R^pF - F的右导出
│   │   └── R^pG - G的右导出
│   ├── 足够内射对象 (Enough Injectives)
│   └── G-零调对象 (G-acyclic Objects)
│       └── R^pG(Y) = 0 对所有 p > 0
│
├── 核心构造
│   ├──  Cartan-Eilenberg分解
│   │   └── 双复形构造
│   ├── 全复形 (Total Complex)
│   ├── 谱序列的滤过构造
│   └── 两个谱序列的比较
│
├── E2页结构
│   └── E_2^{p,q} = R^pG(R^qF(X))
│       p → G的导出次数
│       q → F的导出次数
│
└── 收敛目标
    └── E_∞ ⟹ R^{p+q}(G∘F)(X)
        复合函子的导出
```

### 依赖关系详解

| 概念 | 说明 | 在FormalMath中的位置 |
|------|------|---------------------|
| Abel范畴 | 同调代数的工作环境 | `concept/范畴论/Abel范畴.md` |
| 左正合函子 | 保持核但不必保持余核 | `concept/同调代数/正合函子.md` |
| 足够内射 | 每个对象可嵌入内射对象 | `concept/同调代数/内射对象.md` |
| 零调对象 | 对该函子无高阶导出 | `concept/同调代数/零调对象.md` |
| 谱序列 | 双复形的自然谱序列 | `concept/同调代数/谱序列.md` |

---

## 4. 证明概要

### 核心构造：Cartan-Eilenberg分解

**Step 1: 取内射分解**

设 $X \in \text{Ob}(\mathcal{A})$，取内射分解：

$$0 \to X \to I^0 \to I^1 \to I^2 \to \cdots$$

**Step 2: 逐次取内射分解**

对每个 $F(I^q) \in \text{Ob}(\mathcal{B})$，取内射分解：

$$0 \to F(I^q) \to J^{q,0} \to J^{q,1} \to J^{q,2} \to \cdots$$

由于 $F(I^q)$ 是 $G$-零调的，这个分解可用于计算 $R^\bullet G$。

**Step 3: 构造双复形**

构造双复形 $J^{\bullet,\bullet}$：

- 垂直微分：$d_v: J^{q,p} \to J^{q+1,p}$（来自Step 2的映射）
- 水平微分：$d_h: J^{q,p} \to J^{q,p+1}$（提升 $F(I^q) \to F(I^{q+1})$）

**关键：** 由 horseshoe lemma，可使每行、每列都是正合的。

**Step 4: 全复形的谱序列**

考虑全复形 $\text{Tot}(J^{\bullet,\bullet})$，有两种滤过：

#### 滤过1（按列）：

$$'E_1^{p,q} = H^q_v(J^{p,\bullet}) = R^qF(X)^p \text{ 的分解}$$

$$'E_2^{p,q} = H^p_h(H^q_v(J^{\bullet,\bullet})) = R^pG(R^qF(X))$$

#### 滤过2（按行）：

$$''E_1^{p,q} = H^q_h(J^{\bullet,p})$$

由于 $J^{\bullet,p}$ 是 $F(I^\bullet)$ 的内射分解，且 $F(I^q)$ $G$-零调，可得：

$$''E_2^{p,q} = \begin{cases} R^{p+q}(G \circ F)(X) & q = 0 \\ 0 & q > 0 \end{cases}$$

**Step 5: 比较与收敛**

两个谱序列都收敛到 $H^{p+q}(\text{Tot}(J))$。第二个谱序列退化给出：

$$H^n(\text{Tot}(J)) = R^n(G \circ F)(X)$$

因此第一个谱序列：

$$'E_2^{p,q} = R^pG(R^qF(X)) \Rightarrow R^{p+q}(G \circ F)(X)$$

∎

### 谱序列的可视化

```
E_2页：
     q=3  •  •  •  •
     q=2  •  •  •  •
     q=1  •  •  •  •
     q=0  •  •  •  •
        p=0 p=1 p=2 p=3
        
微分：d_2: E_2^{p,q} → E_2^{p+2, q-1}
     (向右2，向下1)
     
收敛：对角线 p+q = n 贡献给 R^n(G∘F)(X)
```

---

## 5. 与FormalMath的对应关系

### FormalMath相关文档

| 文档路径 | 内容对应 | 完成状态 |
|----------|----------|----------|
| `concept/同调代数/谱序列.md` | 核心概念 | 🚧 部分完成 |
| `concept/同调代数/Grothendieck谱序列.md` | 本Tag直接对应 | 🚧 计划中 |
| `concept/同调代数/导出函子.md` | 理论基础 | 🚧 部分完成 |
| `concept/范畴论/Abel范畴.md` | 基础范畴 | ✅ 已完成 |
| `concept/同调代数/双复形.md` | 构造工具 | 🚧 部分完成 |

### 概念映射

```yaml
Stacks Project Tag: 013O
FormalMath概念:
  - path: "concept/同调代数/Grothendieck谱序列.md"
    sections:
      - "构造与存在性"
      - "收敛定理"
      - "应用实例"
    relation: "核心对应"
  
  - path: "concept/同调代数/导出函子.md"
    relation: "理论基础"
  
  - path: "concept/同调代数/谱序列.md"
    sections:
      - "第一象限谱序列"
      - "收敛性"
    relation: "技术工具"
```

---

## 6. 应用与重要性

### 经典应用实例

#### 1. Leray谱序列

设 $f: X \to Y$ 是拓扑空间的连续映射：

$$E_2^{p,q} = H^p(Y, R^q f_* \mathcal{F}) \Rightarrow H^{p+q}(X, \mathcal{F})$$

这是Grothendieck谱序列的直接应用，其中：
- $F = f_*$（正向像）
- $G = \Gamma(Y, -)$（整体截面）
- $G \circ F = \Gamma(X, -)$

#### 2. 局部-整体谱序列 (Local-to-Global)

对于层上同调：

$$E_2^{p,q} = H^p(X, \mathcal{H}^q(\mathcal{F})) \Rightarrow H^{p+q}(X, \mathcal{F})$$

其中 $\mathcal{H}^q(\mathcal{F})$ 是上同调层。

#### 3. Hochschild-Serre谱序列 (群上同调)

设 $H \triangleleft G$，$M$ 是 $G$-模：

$$E_2^{p,q} = H^p(G/H, H^q(H, M)) \Rightarrow H^{p+q}(G, M)$$

#### 4. 凝聚层的上同调

对于环层空间 $(X, \mathcal{O}_X)$：

$$E_2^{p,q} = H^p(X, \mathcal{E}xt^q(\mathcal{F}, \mathcal{G})) \Rightarrow \text{Ext}^{p+q}(\mathcal{F}, \mathcal{G})$$

### 重要性评估

| 方面 | 重要性说明 |
|------|-----------|
| 理论统一 | 统一了各种谱序列作为特例 |
| 计算工具 | 将复杂上同调分解为可计算步骤 |
| 深层结构 | 揭示函子复合的导出行为 |
| 教学价值 | 学习导出范畴/谱序列的必经之路 |

---

## 7. 与其他资源的关联

### nLab 对应条目

| nLab页面 | URL | 特色 |
|----------|-----|------|
| Grothendieck spectral sequence | https://ncatlab.org/nlab/show/Grothendieck+spectral+sequence | 高阶视角 |
| spectral sequence | https://ncatlab.org/nlab/show/spectral+sequence | 一般理论 |
| derived functor | https://ncatlab.org/nlab/show/derived+functor | 导出函子 |

**nLab特色：** 讨论Grothendieck谱序列与导出范畴的联系，以及更一般的"复合导出"问题。

### 经典教材

| 文献 | 章节 | 特色 |
|------|------|------|
| Cartan-Eilenberg | Chapter XVI | 原始来源 |
| Grothendieck's Tôhoku | §2.4 | 奠基论文 |
| Weibel's Homological Algebra | 5.8 | 现代标准参考 |
| Gelfand-Manin | III.7 | 导出范畴视角 |
| McCleary | Chapter 2 | 用户友好 |

### 历史背景

- **1956年:** Cartan和Eilenberg在《Homological Algebra》中系统阐述
- **1957年:** Grothendieck的Tôhoku论文推广到Abel范畴
- **影响：** 成为同调代数计算的基本工具

---

## 8. Lean4形式化展望

### 当前形式化状态

| 项目 | 状态 | 说明 |
|------|------|------|
| mathlib4 (Spectral Sequences) | 🚧 早期开发 | 基础定义存在 |
| mathlib4 (Derived Functors) | 🚧 进行中 | 同调代数框架 |
| **具体本Tag** | ❌ 未开始 | 依赖谱序列成熟 |

### mathlib4相关进展

- **同调代数：** 链复形、同调、长正合列已建立
- **谱序列：** 基础定义（page、微分、收敛）正在开发
- **导出函子：** 部分存在，需更多API

### 形式化挑战

| 挑战 | 难度 | 可能的解决方案 |
|------|------|--------------|
| 双复形理论 | ⭐⭐⭐ | 推广现有链复形框架 |
| 两个谱序列的比较 | ⭐⭐⭐⭐ | 需要良好的收敛理论 |
| Cartan-Eilenberg分解 | ⭐⭐⭐⭐ | horseshoe lemma的形式化 |
| 具体计算应用 | ⭐⭐⭐⭐⭐ | 需要大量例子验证 |

### 推荐形式化路线图

#### 阶段1：双复形理论 (优先级：高)
- [ ] 双复形的定义
- [ ] 全复形构造
- [ ] 两种滤过（行/列）

#### 阶段2：谱序列基础 (优先级：高)
- [ ] 谱序列的完整定义（page + 微分）
- [ ] 收敛理论
- [ ] 边缘同态

#### 阶段3：构造工具 (优先级：高)
- [ ] Cartan-Eilenberg分解
- [ ] 内射分解的提升
- [ ] horseshoe lemma

#### 阶段4：Grothendieck谱序列 (优先级：中)
- [ ] 定理的陈述
- [ ] 完整证明
- [ ] 收敛性验证

#### 阶段5：应用 (优先级：中)
- [ ] Leray谱序列
- [ ] Hochschild-Serre谱序列
- [ ] Ext/Ext谱序列

### Lean4代码框架建议

```lean4
-- Grothendieck谱序列的形式化框架
import Mathlib.Algebra.Homology.SpectralSequence
import Mathlib.CategoryTheory.Abelian.Derived

open CategoryTheory Homology

variable {A B C : Type*} [Category A] [Category B] [Category C]
variable [Abelian A] [Abelian B] [Abelian C]
variable (F : A ⥤ B) (G : B ⥤ C)
variable [F.Additive] [G.Additive] [F.PreservesLeftExact] [G.PreservesLeftExact]

-- 假设条件：足够内射、F保内射为G-零调
variable [EnoughInjectives A] [EnoughInjectives B]
variable (hF : ∀ I : Injective A, IsGAcyclic G (F.obj I))

-- Grothendieck谱序列定理
theorem grothendieck_spectral_sequence (X : A) :
    ∃ (E : SpectralSequence C),
      E.E2 p q ≅ (R^p G).obj ((R^q F).obj X) ∧
      E.ConvergesTo (R^(p+q) (G ⋙ F)).obj X := by
  -- 构造Cartan-Eilenberg分解
  -- 建立双复形
  -- 两种滤过的谱序列
  -- 比较和收敛
  sorry

-- 应用：Leray谱序列
theorem leray_spectral_sequence {X Y : Top} (f : X ⟶ Y) (F : Sheaf Ab X) :
    ∃ (E : SpectralSequence Ab),
      E.E2 p q ≅ H^p Y (R^q f_* F) ∧
      E.ConvergesTo H^(p+q) X F := by
  -- 作为Grothendieck谱序列的特例
  sorry
```

### 参考实现

- **Coq/HoTT:** 部分同调代数库存在
- **UniMath:** 有谱序列的某些方面
- **Isabelle:** Archive of Formal Proofs中有部分谱序列理论

---

## 参考链接

- **Stacks Project Tag 013O:** https://stacks.math.columbia.edu/tag/013O
- **Stacks Project Section 12.21:** https://stacks.math.columbia.edu/tag/013N
- **Weibel's Homological Algebra:** https://doi.org/10.1017/CBO9781139644136
- **nLab - Grothendieck Spectral Sequence:** https://ncatlab.org/nlab/show/Grothendieck+spectral+sequence

---

*文档创建日期：2026年4月*  
*FormalMath Stacks Project Tag解读系列*
