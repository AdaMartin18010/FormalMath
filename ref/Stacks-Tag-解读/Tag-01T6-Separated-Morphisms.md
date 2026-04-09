# Stacks Project Tag 01T6 - 分离态射（Separated Morphisms）

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01T6 |
| **章节** | Chapter 26: Schemes, Section 26.21: Separation axioms |
| **类型** | 定义 (Definition) |
| **重要性** | ★★★★★ (核心概念) |
| **位置** | Schemes, Definition 26.21.3 |

## 2. 定理/定义原文

### 英文原文

**Definition 26.21.3.** Let $f : X \to S$ be a morphism of schemes.

1. We say $f$ is **separated** if the diagonal morphism $\Delta_{X/S}$ is a closed immersion.

2. We say $f$ is **quasi-separated** if the diagonal morphism $\Delta_{X/S}$ is a quasi-compact morphism.

3. We say a scheme $Y$ is **separated** if the morphism $Y \to \mathop{\mathrm{Spec}}(\mathbf{Z})$ is separated.

4. We say a scheme $Y$ is **quasi-separated** if the morphism $Y \to \mathop{\mathrm{Spec}}(\mathbf{Z})$ is quasi-separated.

### 中文翻译

**定义 26.21.3.** 设 $f : X \to S$ 是概形态射。

1. 称 $f$ 是**分离的**（separated），如果对角态射 $\Delta_{X/S}$ 是闭浸入。

2. 称 $f$ 是**拟分离的**（quasi-separated），如果对角态射 $\Delta_{X/S}$ 是拟紧态射。

3. 称概形 $Y$ 是**分离的**，如果态射 $Y \to \mathop{\mathrm{Spec}}(\mathbf{Z})$ 是分离的。

4. 称概形 $Y$ 是**拟分离的**，如果态射 $Y \to \mathop{\mathrm{Spec}}(\mathbf{Z})$ 是拟分离的。

## 3. 概念依赖图

```
                    分离态射 (Separated Morphism)
                           |
          +----------------+----------------+
          |                |                |
    对角态射           闭浸入          拟紧态射
    (Diagonal          (Closed         (Quasi-compact)
     Morphism)         Immersion)
          |                |                |
          +----------------+----------------+
                           |
                分离性 ⇔ 对角像闭
                           |
       +-------------------+-------------------+
       |                   |                   |
   代数判别法           valuative           纤维积刻画
   (Algebraic          criterion           (Fiber product)
    Criterion)
```

**前置概念：**

- 纤维积（Fiber Products）
- 对角态射（Diagonal Morphism）
- 闭浸入（Closed Immersions）
- 拟紧态射（Quasi-compact Morphisms）

**依赖此概念：**

- 固有态射（Proper Morphisms）
- 射影态射（Projective Morphisms）
- 拟射影态射（Quasi-projective Morphisms）
- 分离概形的所有基本性质

## 4. 证明概要

### 4.1 对角态射是浸入

**Lemma 26.21.2.** 设 $X$ 是 $S$ 上的概形。对角态射 $\Delta_{X/S}$ 是浸入。

**证明概要：**

1. 取 $V \subset X$ 仿射开，映射到 $U \subset S$ 仿射开

2. 则 $V \times_U V$ 是 $X \times_S X$ 的仿射开

3. 考虑开子概形 $W = \bigcup V \times_U V$ 的并

4. 证明 $\Delta_{X/S}^{-1}(V \times_U V) = V$

5. 验证 $\Delta_{V/U}$ 是闭浸入（仿射情形已知）

### 4.2 代数判别法

**Lemma 26.21.7.** 设 $f : X \to S$ 是概形态射。以下条件等价：

1. $f$ 是分离的
2. 对于映射到 $S$ 中公共仿射开集的一对仿射开集 $(U, V)$，有：
   - $U \cap V$ 是仿射的
   - 环映射 $\mathcal{O}_X(U) \otimes_{\mathbf{Z}} \mathcal{O}_X(V) \to \mathcal{O}_X(U \cap V)$ 是满射

**代数意义：** 分离性等价于仿射开集的交可以用它们的坐标环"显式描述"。

### 4.3 典型例子

**分离的：**

- 仿射概形（$\mathop{\mathrm{Spec}}(A) \to \mathop{\mathrm{Spec}}(\mathbf{Z})$）
- 射影空间 $\mathbb{P}^n_S \to S$
- 所有闭子概形

**非分离的：**

- 仿射直线的双原点：$\mathbb{A}^1$ with doubled origin
- 两条仿射直线在无穷远处粘合

## 5. 与FormalMath的对应关系

| FormalMath概念 | Stacks Project对应 | Lean4/mathlib4 |
|----------------|-------------------|----------------|
| `Scheme` | 概形 $X, S$ | `AlgebraicGeometry.Scheme` |
| `DiagonalMorphism` | $\Delta_{X/S}$ | `diagonal` |
| `ClosedImmersion` | 闭浸入 | `IsClosedImmersion` |
| `Separated` | 分离态射 | `IsSeparated` |
| `QuasiSeparated` | 拟分离态射 | `IsQuasiSeparated` |

**mathlib4对应：**

```lean
-- 分离态射定义
class IsSeparated {X Y : Scheme} (f : X ⟶ Y) : Prop where
  diagonal_closedImmersion : IsClosedImmersion (diagonal f)

-- 拟分离态射
class IsQuasiSeparated {X Y : Scheme} (f : X ⟶ Y) : Prop where
  diagonal_quasiCompact : QuasiCompact (diagonal f)

-- 仿射态射是分离的
instance {X Y : Scheme} (f : X ⟶ Y) [IsAffineHom f] : IsSeparated f := by
  -- 证明：仿射态射的对角是仿射的，从而是闭浸入
  sorry
```

## 6. 应用与重要性

### 6.1 为什么需要分离性？

**直观意义：**

分离性确保概形的"点"行为良好。在非分离概形中，一个点可以"分叉"成多个点。

**几何解释：**

对于域 $k$ 上的概形 $X$，分离性等价于：$X \times_k X$ 中的对角点对应于 $X$ 中的点，没有"额外"的极限点。

### 6.2 核心性质

| 性质 | 说明 | 重要性 |
|------|------|--------|
| 局部性质 | 分离性是局部于靶的 | 可局部验证 |
| 稳定性 | 在基变换和复合下保持 | 构造新例子 |
| 纤维积 | 分离概形的纤维积仍分离 | 范畴性质 |
| 值判别法 | valuative criterion | 证明工具 |

### 6.3 与Hausdorff空间的类比

| 拓扑空间 | 概形 |
|---------|------|
| Hausdorff ($T_2$) | 分离 |
| 对角 $\Delta_X \subset X \times X$ 闭 | 对角态射 $\Delta_{X/S}$ 是闭浸入 |
| 点可以由不交开集分离 | 类似的几何直观 |

**关键区别：** 概形的Zariski拓扑几乎从不Hausdorff，但分离性是其代数对应。

### 6.4 应用实例

**1. 模空间的存在性**

许多模函子（如曲线模空间）只在分离概形上有好的表示。

**2. 相交理论**

分离性确保纤维积构造给出正确的几何对象。

**3. 凝聚层的性质**

在分离概形上，凝聚层的上同调理论工作良好。

## 7. 与其他资源的关联

| 资源 | 章节 | 关联内容 |
|------|------|---------|
| Hartshorne | II.4 | 分离态射的定义与基本性质 |
| Hartshorne | II.7 | 射影态射是分离的 |
| Vakil | 11.1 | 分离性的直观解释 |
| EGA I | §5 | 完整的技术处理 |
| Liu | 3.3 | 中国留数定理的分离性应用 |

**Stacks Project交叉引用：**

- Tag 01KH: 分离公理（详细引理）
- Tag 01W0: 固有态射（分离是条件之一）
- Tag 01T8: valuative criterion
- Tag 04YV: 代数空间的分离性

## 8. Lean4形式化展望

### 8.1 当前状态

mathlib4中分离态射的形式化：

```lean
-- 已完成定义
class IsSeparated (f : X ⟶ Y) : Prop

-- 基本性质
theorem isSeparated_iff_diagonal_closedImmersion {f : X ⟶ Y} :
    IsSeparated f ↔ IsClosedImmersion (diagonal f)

-- 复合保持分离性
theorem IsSeparated.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsSeparated f] [IsSeparated g] : IsSeparated (f ≫ g)
```

### 8.2 待形式化内容

```lean
-- 代数判别法
theorem isSeparated_iff_affine_intersections {f : X ⟶ Y} :
    IsSeparated f ↔ ∀ (U V : X.Opens) [IsAffine U] [IsAffine V]
      (h : U.ι ≫ f = V.ι ≫ f),
      IsAffine (U ⊓ V) ∧ Function.Surjective ... := sorry

-- valuative criterion
theorem valuativeCriterion_separated {f : X ⟶ Y} :
    IsSeparated f ↔ ∀ R : ValuationRing, ... := sorry
```

### 8.3 形式化路线图

```
阶段1: 基础定义 ✓
  └── IsSeparated类型类
  └── IsQuasiSeparated类型类

阶段2: 基本性质 ✓
  └── 复合封闭性
  └── 基变换封闭性

阶段3: 判别法 (进行中)
  └── 仿射交集判别
  └── valuative criterion

阶段4: 应用 (计划中)
  └── 射影态射的分离性
  └── 固有态射理论
```

---

**文档版本：** Round 36
**创建日期：** 2026-04-09
