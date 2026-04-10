# Stacks Tag 013U - 投影分解

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 013U |
| **概念名称** | 投影分解 (Projective Resolutions) |
| **所属章节** | Chapter 13: Derived Categories, Section 13.19 |
| **概念类型** | 定义与构造 (Definition & Construction) |
| ** Stacks原文** | Definition 13.19.1 / Lemma 13.19.2 |

---

## 2. 定理/定义原文

**定义陈述：**

设 $\mathcal{A}$ 是一个阿贝尔范畴，$A \in \text{Ob}(\mathcal{A})$ 是一个对象。

**投影分解**是指一个正合序列：
$$\cdots \to P_2 \to P_1 \to P_0 \to A \to 0$$

其中每个 $P_n$ 都是投影对象。

等价地，这是一个拟同构：
$$P_\bullet \to A[0]$$

其中 $P_\bullet$ 是有界上复形（或链复形），且每个 $P_n$ 投影。

**存在性定理：**

若阿贝尔范畴 $\mathcal{A}$ 有足够投影对象，则每个对象都有投影分解。

**英文原文：**
> Let $\mathcal{A}$ be an abelian category. Let $A \in \text{Ob}(\mathcal{A})$. A *projective resolution of $A$* is a complex $P_\bullet$ together with a map $P_0 \to A$ such that:
> 1. We have $P_n = 0$ for $n < 0$.
> 2. Each $P_n$ is a projective object of $\mathcal{A}$.
> 3. The map $P_0 \to A$ induces an isomorphism $H_0(P_\bullet) \to A$ and for $n \neq 0$ we have $H_n(P_\bullet) = 0$.

---

## 3. 概念依赖图

```
Tag 013U: 投影分解
│
├── 前置概念
│   ├── 阿贝尔范畴 (Abelian Category) [Tag 009B]
│   ├── 链复形 (Chain Complex) [Tag 010H]
│   ├── 投影对象 (Projective Object) [Tag 013N]
│   ├── 足够投影 (Enough Projectives) [Tag 013P]
│   ├── 拟同构 (Quasi-Isomorphism) [Tag 010U]
│   └── 同调/同伦 (Homology/Homotopy) [Tag 010N]
│
├── 构造方法
│   ├── 逐次构造：利用投影覆盖
│   ├── 函子性：态射的提升
│   └── 同伦唯一性：在同伦意义下唯一
│
├── 与内射分解的关系
│   ├── 对偶概念：投影 vs 内射
│   ├── 左右导出函子：投影用于左导出
│   └── 范畴对偶：A^op 中互换
│
└── 后续应用
    ├── 左导出函子 [Tag 013W]
    ├── Tor函子 [Tag 00DV]
    ├── 群同调 [Tag 00DW]
    └── Lie代数同调 [Tag 00DX]
```

---

## 4. 证明概要（存在性与唯一性）

### 4.1 存在性证明

**定理：** 若阿贝尔范畴 $\mathcal{A}$ 有足够投影对象，则每个对象 $A \in \mathcal{A}$ 都有投影分解。

**构造性证明：**

**步骤1：** 构造 $P_0$

由于 $\mathcal{A}$ 有足够投影，存在满射 $P_0 \twoheadrightarrow A$，其中 $P_0$ 是投影对象。

令 $K_1 = \ker(P_0 \to A)$ 为核。

**步骤2：** 归纳构造 $P_n$

假设已构造到 $P_{n-1}$，得到核 $K_n = \ker(P_{n-1} \to P_{n-2})$。

由于有足够投影，存在满射 $P_n \twoheadrightarrow K_n$，其中 $P_n$ 投影。

定义微分 $d_n: P_n \to P_{n-1}$ 为复合：
$$P_n \twoheadrightarrow K_n \hookrightarrow P_{n-1}$$

**步骤3：** 验证正合性

由构造，$\text{im}(d_n) = K_n = \ker(d_{n-1})$，因此序列正合。

### 4.2 同伦唯一性

**定理：** 设 $P_\bullet$ 和 $Q_\bullet$ 都是 $A$ 的投影分解，则存在同伦等价：
$$P_\bullet \simeq Q_\bullet$$

**与内射分解的区别：**

- **内射分解**：从对象出发，逐步嵌入内射对象
- **投影分解**：从对象出发，逐步用投影对象覆盖

两者通过对偶范畴联系：$A$ 在 $\mathcal{A}$ 中的投影分解 = $A$ 在 $\mathcal{A}^{op}$ 中的内射分解。

### 4.3 函子性

**定理：** 设 $\varphi: A \to B$ 是态射，$P_\bullet$ 和 $Q_\bullet$ 分别是 $A$ 和 $B$ 的投影分解，则存在链复形态射：
$$\tilde{\varphi}: P_\bullet \to Q_\bullet$$

在链复形同伦意义下唯一。

---

## 5. 与FormalMath对应

### 5.1 概念映射

| Stacks Project概念 | FormalMath对应内容 | 文件路径 |
|-------------------|-------------------|----------|
| 投影对象 | Projective | `concept/范畴论/投影对象.md` |
| 足够投影 | EnoughProjectives | `concept/同调代数/阿贝尔范畴.md` |
| 投影分解 | ProjectiveResolution | `concept/同调代数/分解.md` |
| 左导出函子 | LeftDerivedFunctor | `concept/同调代数/导出函子.md` |
| Tor函子 | Tor | `concept/同调代数/导出函子.md` |

### 5.2 知识体系位置

```
FormalMath知识体系
├── 范畴论基础
│   └── 阿贝尔范畴
│       ├── 投影对象 ←── 核心概念
│       └── 足够投影 ←── 存在性条件
│
├── 同调代数
│   ├── 复形理论
│   │   └── 链复形
│   │
│   ├── 分解理论
│   │   ├── 投影分解 ←── Tag 013U (链复形)
│   │   └── 内射分解 ←── Tag 013T (上链复形)
│   │
│   └── 导出函子
│       ├── 左导出函子 ←── 投影分解的应用
│       └── 右导出函子 ←── 内射分解的应用
```

### 5.3 学习路径建议

```
学习路径：
阿贝尔范畴
    ├── 正合序列
    ├── 投影对象 ←── 关键前置
    └── 足够投影 ←── 存在性保证
            ↓
链复形与分解
    ├── 链复形的定义
    ├── 同调代数基础
    └── 投影分解 ←── Tag 013U
            ↓
左导出函子
    └── Tor函子等
```

---

## 6. 应用与重要性

### 6.1 理论重要性

**内射分解的对偶：**

投影分解与内射分解形成完美对偶。它们分别用于定义**左导出函子**和**右导出函子**。

**核心作用：**
1. **左导出函子**：$L_nF(A) = H_n(F(P_\bullet))$
2. **Tor函子**：用投影分解计算张量积的导出
3. **群同调**：$H_n(G, M)$ 的计算

### 6.2 实际应用场景

#### 场景1：Tor函子

设 $R$ 是环，$M$ 是右 $R$-模，$N$ 是左 $R$-模。

**定义：** $\text{Tor}^R_n(M, N) = L_n(M \otimes_R -)(N)$

**计算：** 取 $N$ 的投影分解 $P_\bullet \to N$，则：
$$\text{Tor}^R_n(M, N) = H_n(M \otimes_R P_\bullet)$$

**例：** 若 $N$ 是平坦模，则 $\text{Tor}^R_n(M, N) = 0$ 对 $n > 0$。

#### 场景2：群同调

设 $G$ 是群，$M$ 是 $G$-模。

**定义：** $H_n(G, M) = L_n(-_G)(M)$（取 $G$-余不变量）

**计算：** 通过投影分解，等价于标准复形（bar resolution）的计算。

**低维解释：**
- $H_0(G, M) = M_G = M / \langle gm - m \rangle$
- $H_1(G, M) = G^{ab} \otimes M$（当 $M$ 平凡作用）

#### 场景3：Hilbert合冲定理

设 $k$ 是域，$S = k[x_1, \ldots, x_n]$。

**定理：** 任意有限生成 $S$-模 $M$ 有长度不超过 $n$ 的投影分解。

**意义：** 多项式环的**整体维数**为 $n$。

### 6.3 具体例子

**例1：自由分解**

自由模是最强的投影对象。自由分解是最"好"的投影分解。

**例2：$\mathbb{Z}$-模的分解**

对有限生成阿贝尔群 $A$，有标准分解：
$$0 \to F_1 \to F_0 \to A \to 0$$

其中 $F_0, F_1$ 是自由阿贝尔群。

**例3：Koszul复形**

在正则序列情形下，Koszul复形给出了自然的投影分解。

### 6.4 现代发展

- **K-投影复形**：推广到无界复形
- **导出范畴的等价**：投影复形实现 $D^-(\mathcal{A})$
- **A-无穷代数**：投影分解的高阶结构

---

## 7. 与其他资源关联

### 7.1 Stacks Project内部关联

| 相关Tag | 关系类型 | 说明 |
|--------|---------|------|
| **Tag 013N** (投影对象) | 核心概念 | 分解的基本单元 |
| **Tag 013P** (足够投影) | 存在性条件 | 保证分解存在 |
| **Tag 013T** (内射分解) | 对偶概念 | 对偶范畴中的对应 |
| **Tag 013W** (左导出函子) | 主要应用 | 导出函子的定义基础 |
| **Tag 00DV** (Tor函子) | 核心应用 | Tor的标准计算 |
| **Tag 00DW** (群同调) | 应用 | 群同调的标准计算 |

### 7.2 外部参考资源

**经典教材：**

1. **Weibel, An Introduction to Homological Algebra**
   - Chapter 2: 导出函子与分解
   - 投影分解的标准参考

2. **Brown, Cohomology of Groups**
   - Chapter I: 群同调的定义与计算
   - 投影分解的具体应用

3. **Cartan-Eilenberg, Homological Algebra**
   - Chapter V: 导出函子
   - 经典教材

4. **Eisenbud, Commutative Algebra**
   - Chapter 19: 自由分解与合冲定理
   - 交换代数视角

---

## 8. Lean4形式化展望

### 8.1 形式化难度评估

| 方面 | 难度 | 说明 |
|------|------|------|
| 概念复杂度 | ★★★★☆ | 与内射分解类似 |
| 证明技术 | ★★★★☆ | 对偶于内射分解 |
| 依赖链条 | ★★★★★ | 需要完整的同调代数基础 |
| 预计工作量 | 大 | 需要4-6个月 |

### 8.2 mathlib4现状

**当前已有基础：**
```
mathlib4
├── Algebra
│   └── Homology ✅
│
└── CategoryTheory
    ├── Abelian ✅
    └── Projective 📝 计划中
```

### 8.3 形式化路线图

**阶段1：投影对象理论 (2个月)**

```lean
-- 投影对象的定义
class Projective (X : C) : Prop where
  factors : ∀ (Y Z : C) [Epi (f : Y ⟶ Z)] (g : X ⟶ Z),
    ∃ h : X ⟶ Y, h ≫ f = g

-- 足够投影
def HasEnoughProjectives (C : Type*) [Category C] [Abelian C] : Prop :=
  ∀ X : C, ∃ P : C, Projective P ∧ Nonempty (Epi (P ⟶ X))
```

**阶段2：投影分解 (2个月)**

```lean
-- 投影分解的结构
structure ProjectiveResolution (X : C) where
  c : ChainComplex C ℕ
  π : c.X 0 ⟶ X
  projective : ∀ n, Projective (c.X n)
  exact : ∀ n, (c.d n).Exact
  epi : Epi π

-- 存在性定理
theorem exists_projective_resolution [HasEnoughProjectives C] (X : C) :
    Nonempty (ProjectiveResolution X) := by
  sorry
```

**阶段3：Tor函子的定义 (2个月)**

```lean
-- Tor函子的定义
noncomputable def Tor (n : ℕ) (M : Module R) (N : Module R) : Type _ :=
  let P := some (exists_projective_resolution N)
  homology (M ⊗ P.c.X n) (M ⊗ P.c.d n) (M ⊗ P.c.d (n+1))
```

### 8.4 与内射分解的代码对偶

```lean
-- 投影分解 vs 内射分解
structure ProjectiveResolution (X : C)  -- 链复形
structure InjectiveResolution (X : C)   -- 上链复形

-- 函子性
def ProjectiveResolution.map  -- 左导出
def InjectiveResolution.map   -- 右导出
```

---

## 附录

### A. 符号速查表

| 符号 | 含义 | LaTeX |
|------|------|-------|
| $P_\bullet$ | 投影链复形 | `P_\bullet` |
| $A[0]$ | 集中在0度的复形 | `A[0]` |
| $\simeq$ | 同伦等价 | `\simeq` |
| $L_nF$ | 第$n$左导出函子 | `L_nF` |
| $\text{Tor}_n$ | Tor函子 | `\text{Tor}_n` |

### B. 投影分解 vs 内射分解

| 特性 | 投影分解 | 内射分解 |
|------|---------|---------|
| 方向 | 从左到右（链复形） | 从左到右（上链复形） |
| 对象 | 投影对象 | 内射对象 |
| 构造 | 投影覆盖 | 内射嵌入 |
| 应用 | 左导出函子 | 右导出函子 |
| 典型函子 | $\otimes$（张量积） | $\text{Hom}$（同态） |
| 例子 | Tor函子 | Ext函子 |

---

*文档版本: 1.0*  
*创建日期: 2026年4月*  
*对应Stacks Project版本: 2024.02*
