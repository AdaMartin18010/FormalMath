# Stacks Tag 01FQ - 谱序列收敛

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01FQ |
| **概念名称** | 谱序列收敛 (Convergence of Spectral Sequences) |
| **所属章节** | Chapter 12: Homological Algebra, Section 12.24 |
| **概念类型** | 定义与定理 (Definition & Theorem) |
| ** Stacks原文** | Definition 12.24.5 / Lemma 12.24.6 |

---

## 2. 定理/定义原文

**收敛的定义：**

设 $(E_r, d_r)_{r \geq r_0}$ 是一个谱序列。称该谱序列**收敛**（converges）到分次对象 $H^*$，记作：
$$E_r^{p,q} \Rightarrow H^{p+q}$$

如果满足：

1. 对每个 $(p,q)$，存在 $r = r(p,q)$ 使得对所有 $r' \geq r$，$E_{r'}^{p,q} = E_\infty^{p,q}$
2. 每个 $H^n$ 有过滤 $F^\bullet H^n$ 使得：
$$E_\infty^{p,q} \cong \text{Gr}_F^p H^{p+q} = F^p H^{p+q} / F^{p+1} H^{p+q}$$

**英文原文：**
> Let $(E_r, d_r)_{r \geq r_0}$ be a spectral sequence. We say the spectral sequence *converges* to $H^*$, denoted $E_r^{p,q} \Rightarrow H^{p+q}$, if:
> 1. For each $(p,q)$ there exists $r = r(p,q)$ such that $d_r^{p,q} = 0$ and $d_r^{p-r, q+r-1} = 0$.
> 2. Each $H^n$ has a filtration such that the associated graded pieces are isomorphic to $E_\infty^{p,q}$.

---

## 3. 概念依赖图

```
Tag 01FQ: 谱序列收敛
│
├── 前置概念
│   ├── 谱序列定义 (Spectral Sequence) [Tag 010H]
│   ├── 谱序列的微分 (Differential) [Tag 010I]
│   ├── $E_\infty$页 [Tag 010J]
│   ├── 过滤对象 (Filtered Object) [Tag 012N]
│   └── 分次对象 (Graded Object) [Tag 012M]
│
├── 收敛类型
│   ├── 弱收敛 (Weak Convergence)
│   ├── 收敛 (Convergence)
│   ├── 有界收敛 (Bounded Convergence)
│   └── 正则收敛 (Regular Convergence)
│
├── 收敛判定
│   ├── 第一象限谱序列的有界性
│   ├── 退出页面的稳定性
│   └── 过滤的完备性
│
└── 后续应用
    ├── Leray谱序列 [Tag 01FP]
    ├── Grothendieck谱序列
    ├── 超上同调谱序列 [Tag 01FQ]
    └── Adams谱序列
```

---

## 4. 证明概要（收敛判定）

### 4.1 第一象限谱序列

**定义：** 第一象限谱序列满足 $E_r^{p,q} = 0$ 当 $p < 0$ 或 $q < 0$。

**定理：** 第一象限谱序列自动收敛。

**证明要点：**

**步骤1：** 观察微分的移动

微分 $d_r: E_r^{p,q} \to E_r^{p+r, q-r+1}$ 满足：
- 当 $r > p$ 时，起点 $E_r^{p,q}$ 可能非零，但 $E_r^{p-r, q+r-1} = 0$（因 $p-r < 0$）
- 当 $r > q+1$ 时，终点 $E_r^{p+r, q-r+1} = 0$（因 $q-r+1 < 0$）

**步骤2：** 稳定性分析

对每个固定的 $(p,q)$，当 $r > \max(p, q+1)$ 时：
- $d_r^{p,q} = 0$（靶为零）
- $d_r^{p-r, q+r-1} = 0$（源为零）

因此 $E_r^{p,q} = E_{r+1}^{p,q} = \cdots = E_\infty^{p,q}$。

### 4.2 构造目标上同调

**定理：** 设谱序列由过滤复形 $(F^p C^\bullet)_{p \in \mathbb{Z}}$ 构造，则：
$$E_\infty^{p,q} \cong F^p H^{p+q}(C) / F^{p+1} H^{p+q}(C)$$

**证明概要：**

**步骤1：** 定义过滤上的同调

$$F^p H^n(C) = \text{im}(H^n(F^p C) \to H^n(C))$$

**步骤2：** 计算 $E_\infty$

由构造，$E_r^{p,q}$ 的极限给出：
$$E_\infty^{p,q} = \frac{Z_\infty^{p,q}}{B_\infty^{p,q}}$$

其中 $Z_\infty$ 是永远循环的元素，$B_\infty$ 是永远边缘的元素。

**步骤3：** 建立同构

通过仔细分析，可以证明：
$$E_\infty^{p,q} \cong \frac{\ker(H^{p+q}(C) \to H^{p+q}(C/F^p C))}{\ker(H^{p+q}(C) \to H^{p+q}(C/F^{p+1} C))}$$

这正是 $F^p H^{p+q} / F^{p+1} H^{p+q}$。

### 4.3 边界情况

**边缘退化：** 若 $d_r = 0$ 对所有 $r \geq r_0$，则谱序列在 $E_{r_0}$ 处退化：
$$E_{r_0}^{p,q} = E_\infty^{p,q} = \text{Gr}^p H^{p+q}$$

**例：** 若复形只有两行非零，谱序列在 $E_2$ 处退化，给出长正合序列。

---

## 5. 与FormalMath对应

### 5.1 概念映射

| Stacks Project概念 | FormalMath对应内容 | 文件路径 |
|-------------------|-------------------|----------|
| 谱序列 | SpectralSequence | `concept/同调代数/谱序列.md` |
| 收敛 | Convergence | `concept/同调代数/谱序列收敛.md` |
| 过滤 | Filtration | `concept/同调代数/过滤.md` |
| 分次对象 | GradedObject | `concept/同调代数/分次对象.md` |
| $E_\infty$页 | EInfty | `concept/同调代数/谱序列.md` |

### 5.2 知识体系位置

```
FormalMath知识体系
├── 同调代数
│   ├── 谱序列理论
│   │   ├── 谱序列定义 [Tag 010H]
│   │   ├── 微分与页 [Tag 010I]
│   │   ├── 谱序列收敛 ←── Tag 01FQ
│   │   └── 应用实例
│   │
│   └── 过滤理论
│       ├── 过滤对象
│       └── 分次对象
│
└── 代数几何
    └── 层上同调
        └── Leray谱序列 ←── 应用
```

### 5.3 学习路径建议

```
学习路径：
复形与上同调
    ↓
谱序列基础
    ├── 定义与基本性质 [Tag 010H]
    ├── 微分的构造 [Tag 010I]
    └── 谱序列收敛 ←── Tag 01FQ
            ↓
    应用
        ├── Leray谱序列 [Tag 01FP]
        ├── Grothendieck谱序列
        └── Adams谱序列
```

---

## 6. 应用与重要性

### 6.1 理论重要性

**谱序列的核心问题：**

谱序列的价值在于其**收敛性**——它将复杂的计算分解为一系列"页面"，每页都比前一页"更接近"最终答案。

**核心作用：**
1. **计算策略**：从 $E_1$ 或 $E_2$ 出发，逐步逼近 $E_\infty$
2. **信息分解**：将目标上同调分解为更易计算的片段
3. **边缘同态**：谱序列提供自然映射（边缘同态）

### 6.2 实际应用场景

#### 场景1：Leray谱序列

设 $f: X \to Y$ 是连续映射，则：
$$E_2^{p,q} = H^p(Y, R^qf_*\mathcal{F}) \Rightarrow H^{p+q}(X, \mathcal{F})$$

**收敛性分析：**
- 若 $Y$ 是有限维的，这是第一象限谱序列，自动收敛
- 若纤维上同调有界，谱序列有强收敛性

#### 场景2：Grothendieck谱序列

设 $F: \mathcal{A} \to \mathcal{B}$ 和 $G: \mathcal{B} \to \mathcal{C}$ 是左正合函子，$F$ 将内射映为 $G$-零调对象，则：
$$E_2^{p,q} = R^pG(R^qF(A)) \Rightarrow R^{p+q}(G \circ F)(A)$$

**这是Tag 01F5（导出函子复合公式）的谱序列版本。**

#### 场景3：双复形谱序列

设 $C^{\bullet, \bullet}$ 是第一象限双复形，有两种谱序列：
- $'E_2^{p,q} = H^p_H H^q_V(C)$
- $''E_2^{p,q} = H^q_V H^p_H(C)$

两者都收敛到 $H^{p+q}(\text{Tot}(C))$。

**应用：** 层上同调的Čech计算。

### 6.3 边缘同态与五项正合列

从谱序列可提取**边缘同态**（Edge Homomorphisms）：

对于第一象限谱序列：
- **低次边缘**：$E_2^{n,0} \to H^n$（$E_2^{n,0}$ 到目标的映射）
- **高次边缘**：$H^n \to E_2^{0,n}$（目标到 $E_2^{0,n}$ 的映射）

**五项正合列：**

当只有前两行非零时，谱序列退化为：
$$0 \to E_2^{1,0} \to H^1 \to E_2^{0,1} \to E_2^{2,0} \to H^2$$

### 6.4 现代发展

- **收敛的精细分析**：条件收敛、强收敛
- **多谱序列**：多个指标的谱序列
- **同伦谱序列**：稳定同伦论中的谱序列

---

## 7. 与其他资源关联

### 7.1 Stacks Project内部关联

| 相关Tag | 关系类型 | 说明 |
|--------|---------|------|
| **Tag 010H** (谱序列定义) | 基础定义 | 收敛性的前提 |
| **Tag 010I** (谱序列微分) | 技术基础 | 微分的性质决定收敛 |
| **Tag 01FP** (Leray谱序列) | 主要应用 | 具体谱序列的收敛 |
| **Tag 01F5** (导出函子复合) | 理论基础 | 谱序列版本的理论基础 |
| **Tag 012N** (过滤) | 技术基础 | 收敛的目标结构 |
| **Tag 010J** ($E_\infty$页) | 技术概念 | 极限页的定义 |

### 7.2 外部参考资源

**经典教材：**

1. **McCleary, A User's Guide to Spectral Sequences**
   - 最全面、最实用的谱序列参考
   - 详细讨论各种收敛类型

2. **Weibel, An Introduction to Homological Algebra**
   - Chapter 5: 谱序列
   - 包含收敛的详细证明

3. **Bott-Tu, Differential Forms in Algebraic Topology**
   - Chapter III: 谱序列与纤维丛
   - 几何视角的阐述

4. **Spanier, Algebraic Topology**
   - Chapter 9: 谱序列
   - 拓扑学视角

**在线资源：**
- [Stacks Project 第12章](https://stacks.math.columbia.edu/tag/01FQ)
- [nLab: spectral sequence](https://ncatlab.org/nlab/show/spectral+sequence)

---

## 8. Lean4形式化展望

### 8.1 形式化难度评估

| 方面 | 难度 | 说明 |
|------|------|------|
| 概念复杂度 | ★★★★★ | 涉及过滤、极限、分级结构 |
| 证明技术 | ★★★★★ | 复杂的代数拓扑技术 |
| 依赖链条 | ★★★★★ | 需要完整的同调代数基础 |
| 预计工作量 | 很大 | 需要6-12个月 |

### 8.2 mathlib4现状

**当前已有基础：**
```
mathlib4
├── Algebra
│   └── Homology ✅
│
└── Order
    └── Filter ✅ -- 过滤的一般理论
```

**需要的补充：**
1. 谱序列的一般框架
2. 过滤复形的谱序列
3. 收敛性的形式化
4. 具体谱序列（Leray等）

### 8.3 形式化路线图

**阶段1：谱序列基础 (3个月)**

```lean
-- 谱序列的定义
structure SpectralSequence (C : Type*) [Category C] [Abelian C] where
  page (r : ℕ) : ℤ → ℤ → C
  differential (r : ℕ) : ∀ p q, page r p q ⟶ page r (p + r) (q - r + 1)
  condition : ∀ r p q, differential r p q ≫ differential r (p + r) (q - r + 1) = 0
  iso (r : ℕ) : page (r + 1) ≅ homology (differential r)
```

**阶段2：收敛性定义 (2个月)**

```lean
-- 谱序列收敛的定义
structure Convergence (E : SpectralSequence C) (H : ℤ → C) where
  filtration : ∀ n, Filtration (H n)
  iso : ∀ p q, ∃ r₀, ∀ r ≥ r₀,
    E.page r p q ≅ filtration.grade p (H (p + q))
```

**阶段3：第一象限谱序列 (2个月)**

```lean
-- 第一象限谱序列
def IsFirstQuadrant (E : SpectralSequence C) : Prop :=
  ∀ p q, p < 0 ∨ q < 0 → E.page 0 p q = 0

-- 第一象限谱序列的收敛性
theorem first_quadrant_convergence (E : SpectralSequence C)
    [h : IsFirstQuadrant E] : -- 自动收敛
  sorry
```

### 8.4 技术挑战

| 挑战 | 解决方案 |
|------|---------|
| 谱序列的索引复杂性 | 使用精细的类型系统 |
| 过滤的形式化 | 参考mathlib4的Filter结构 |
| 极限的构造 | 使用范畴论极限 |
| 收敛的判定 | 分类处理不同类型 |

---

## 附录

### A. 符号速查表

| 符号 | 含义 | LaTeX |
|------|------|-------|
| $E_r^{p,q}$ | 第$r$页，$(p,q)$位置 | `E_r^{p,q}` |
| $E_\infty^{p,q}$ | 极限页 | `E_\infty^{p,q}` |
| $\Rightarrow$ | 收敛 | `\Rightarrow` |
| $\text{Gr}^p H^n$ | 分次对象 | `\text{Gr}^p` |
| $F^p H^n$ | 过滤 | `F^p` |

### B. 收敛类型表

| 类型 | 条件 | 性质 |
|------|------|------|
| 弱收敛 | $E_\infty \cong \text{Gr} H$ | 最基本的收敛 |
| 收敛 | 同上 + 稳定性条件 | 标准收敛 |
| 有界收敛 | 谱序列有界 + 收敛 | 强收敛 |
| 正则收敛 | 退出页面条件 | 最强的收敛 |

---

*文档版本: 1.0*  
*创建日期: 2026年4月*  
*对应Stacks Project版本: 2024.02*
