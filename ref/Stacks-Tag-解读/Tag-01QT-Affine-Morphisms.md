# Stacks Project Tag 01QT - 仿射态射（Affine Morphisms）

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01QT |
| **章节** | Chapter 29: Morphisms of Schemes, Section 29.11 |
| **类型** | 定义 (Definition) + 引理 (Lemma) |
| **重要性** | ★★★★★ (核心概念) |
| **位置** | Schemes, Definition 29.11.1 |

## 2. 定理/定义原文

### 英文原文

**Definition 29.11.1.** A morphism of schemes $f : X \to S$ is called **affine** if the inverse image of every affine open of $S$ is an affine open of $X$.

**Lemma 29.11.3.** Let $f : X \to S$ be a morphism of schemes. The following are equivalent:

1. The morphism $f$ is affine.
2. There exists an affine open covering $S = \bigcup W_j$ such that each $f^{-1}(W_j)$ is affine.
3. There exists a quasi-coherent sheaf of $\mathcal{O}_S$-algebras $\mathcal{A}$ and an isomorphism $X \cong \underline{\mathop{\mathrm{Spec}}}_S(\mathcal{A})$ of schemes over $S$.

Moreover, in this case $X = \underline{\mathop{\mathrm{Spec}}}_S(f_*\mathcal{O}_X)$.

### 中文翻译

**定义 29.11.1.** 概形态射 $f : X \to S$ 称为**仿射的**，如果 $S$ 的每个仿射开集的逆像都是 $X$ 的仿射开集。

**引理 29.11.3.** 设 $f : X \to S$ 是概形态射。以下条件等价：

1. 态射 $f$ 是仿射的。
2. 存在仿射开覆盖 $S = \bigcup W_j$ 使得每个 $f^{-1}(W_j)$ 都是仿射的。
3. 存在拟凝聚 $\mathcal{O}_S$-代数层 $\mathcal{A}$ 以及 $X \cong \underline{\mathop{\mathrm{Spec}}}_S(\mathcal{A})$ 作为 $S$-概形的同构。

此外，在这种情况下 $X = \underline{\mathop{\mathrm{Spec}}}_S(f_*\mathcal{O}_X)$。

## 3. 概念依赖图

```
                    仿射态射 (Affine Morphism)
                           |
          +----------------+----------------+
          |                |                |
    定义条件           等价刻画          全局描述
    (Defining         (Equivalent       (Global
     Condition)       Characterization) Description)
          |                |                |
   仿射开集的          局部仿射性        相对Spec
   逆像仿射           (Lemma 29.11.3)   构造
          |                |                |
          +----------------+----------------+
                           |
                核心性质与应用
                           |
       +-------------------+-------------------+
       |                   |                   |
   分离且拟紧          基变换封闭性         与闭浸入关系
   (Separated +       (Base Change)      (Closed Immersion)
    Quasi-compact)
```

**前置概念：**
- 概形的基本理论
- 仿射概形（Affine Schemes）
- 拟凝聚层（Quasi-coherent Sheaves）
- 相对Spec构造（Relative Spec）

**依赖此概念：**
- 闭浸入（Closed Immersions）
- 有限态射（Finite Morphisms）
- 拟仿射态射（Quasi-affine Morphisms）
- 向量丛的构造

## 4. 证明概要

### 4.1 等价性证明

**$(1) \Rightarrow (2)$：** 显然，取 $S$ 的任意仿射开覆盖即可。

**$(2) \Rightarrow (3)$：** 关键构造步骤：

1. 设 $S = \bigcup_{j \in J} W_j$ 是仿射开覆盖，$W_j = \mathop{\mathrm{Spec}}(R_j)$

2. 令 $U_j = f^{-1}(W_j) = \mathop{\mathrm{Spec}}(A_j)$，则 $A_j$ 是 $R_j$-代数

3. 构造层 $\mathcal{A} = f_*\mathcal{O}_X$，验证其为拟凝聚 $\mathcal{O}_S$-代数层

4. 证明 $X \cong \underline{\mathop{\mathrm{Spec}}}_S(\mathcal{A})$

**$(3) \Rightarrow (1)$：** 

设 $X = \underline{\mathop{\mathrm{Spec}}}_S(\mathcal{A})$。对于仿射开集 $W = \mathop{\mathrm{Spec}}(R) \subset S$，有：

$$f^{-1}(W) = \mathop{\mathrm{Spec}}(\mathcal{A}(W))$$

这是仿射的。

### 4.2 关键性质证明

**引理 29.11.2：** 仿射态射是分离且拟紧的。

**证明概要：**
- 拟紧性：由定义直接得到
- 分离性：使用判别准则，两个点 $x_1, x_2 \in X$ 映射到同一点 $s \in S$，则它们在某个仿射开集 $f^{-1}(W)$ 中，而仿射概形是分离的。

## 5. 与FormalMath的对应关系

| FormalMath概念 | Stacks Project对应 | Lean4/mathlib4 |
|----------------|-------------------|----------------|
| `Scheme` | 概形 $X, S$ | `AlgebraicGeometry.Scheme` |
| `AffineScheme` | 仿射概形 | `IsAffine` |
| `Morphism` | 态射 $f : X \to S$ | `Scheme.Hom` |
| `AffineMorphism` | 仿射态射 | `IsAffineHom` |
| `QuasiCoherentSheaf` | 拟凝聚层 $\mathcal{A}$ | `QuasiCoherentSheaf` |
| `SpecFunctor` | 相对Spec | `SpecFunctor` |

**mathlib4对应代码：**
```lean
-- 仿射态射的定义
class IsAffineHom {X Y : Scheme} (f : X ⟶ Y) : Prop where
  -- 仿射开集的逆像是仿射的
  isAffine_preimage : ∀ U : Y.Opens, IsAffine U → IsAffine (f ⁻¹ᵁ U)

-- 等价刻画：全局仿射性
theorem isAffineHom_iff_spec : 
    IsAffineHom f ↔ ∃ (A : Algebra 𝒪_Y), X ≅ Spec (.of 𝒪_Y A) := by
  -- ...
```

## 6. 应用与重要性

### 6.1 核心应用

**1. 闭浸入的刻画**

闭浸入是仿射态射的特例（Lemma 29.11.10）。这给出了闭子概形的几何描述。

**2. 有限态射**

有限态射是仿射态射，且对应的代数层是凝聚的（coherent）。

**3. 向量丛的构造**

给定向量丛 $\mathcal{E}$ 在 $S$ 上，可以构造仿射态射：

$$\mathbb{V}(\mathcal{E}) = \underline{\mathop{\mathrm{Spec}}}_S(\mathop{\mathrm{Sym}}^*(\mathcal{E}^\vee)) \to S$$

### 6.2 重要例子

| 例子 | 描述 | 是否仿射 |
|------|------|---------|
| $\mathbb{A}^n_S \to S$ | 仿射空间 | ✓ |
| $\mathbb{P}^n_S \to S$ | 射影空间 | ✗ |
| 闭浸入 $Z \hookrightarrow X$ | 闭子概形 | ✓ |
| 开浸入 $U \hookrightarrow X$ | 开子概形 | 一般否 |
| $\mathbb{A}^2 \setminus \{0\} \to \mathbb{A}^2$ |  punctured平面 | ✗ |

### 6.3 几何意义

仿射态射的本质：**局部上，源概形是靶概形的"仿射簇族"**

对于点 $s \in S$，纤维 $X_s$ 是仿射概形，其坐标环是 $(f_*\mathcal{O}_X)_s \otimes_{\mathcal{O}_{S,s}} k(s)$。

## 7. 与其他资源的关联

| 资源 | 章节 | 关联内容 |
|------|------|---------|
| Hartshorne | II.5 | 仿射态射与分离性 |
| Hartshorne | II.7 | 射影态射的对比 |
| Vakil | 18.1 | 仿射态射的定义与性质 |
| EGA II | §1 | 详细的技术处理 |
| Liu | 3.1 | 态射的基本类型 |

**Stacks Project交叉引用：**
- Tag 01S5: 仿射态射的详细性质
- Tag 01W0: 固有态射
- Tag 01T6: 分离态射
- Tag 01QT: 有限型态射

## 8. Lean4形式化展望

### 8.1 当前状态

mathlib4中的形式化进展：

```lean
-- 已完成
class IsAffineHom (f : X ⟶ Y) : Prop

-- 等价刻画
theorem isAffineHom_iff_isAffine_preimage {f : X ⟶ Y} :
    IsAffineHom f ↔ ∀ U, IsAffine U → IsAffine (f ⁻¹ᵁ U)

-- 基本性质
theorem isAffineHom_comp {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsAffineHom f] [IsAffineHom g] : IsAffineHom (f ≫ g)

instance isAffineHom_baseChange {f : X ⟶ Y} [IsAffineHom f]
    {Z : Scheme} (g : Z ⟶ Y) : IsAffineHom (pullback.snd f g)
```

### 8.2 待完成工作

```lean
-- 待形式化：全局Spec刻画
theorem isAffineHom_iff_Spec {f : X ⟶ Y} :
    IsAffineHom f ↔ ∃ (𝒜 : AlgebraSheaf 𝒪_Y),
      X ≅ Spec (𝒜) := sorry

-- 待形式化：与闭浸入的关系
theorem isClosedImmersion_isAffineHom {f : X ⟶ Y}
    (hf : IsClosedImmersion f) : IsAffineHom f := sorry

-- 待形式化：向量丛构造
def AffineBundle (𝒜 : AlgebraSheaf 𝒪_Y) : Scheme :=
  Spec 𝒜
```

### 8.3 形式化路线图

```
阶段1: 基础定义 ✓
  └── IsAffineHom类型类

阶段2: 局部刻画 ✓
  └── 仿射开集的条件

阶段3: 全局刻画 (进行中)
  └── 相对Spec构造
  └── 代数层对应

阶段4: 应用 (计划中)
  └── 向量丛
  └── 仿射化
  └── Chow引理
```

---

**文档版本：** Round 36  
**创建日期：** 2026-04-09
