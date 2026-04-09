# Stacks Project Tag 01R0 - 有限型态射（Finite Type Morphisms）

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01R0 |
| **章节** | Chapter 29: Morphisms of Schemes, Section 29.15 |
| **类型** | 定义 (Definition) + 引理 (Lemma) |
| **重要性** | ★★★★★ (核心概念) |
| **位置** | Morphisms of Schemes, Definition 29.15.1 |

## 2. 定理/定义原文

### 英文原文

**Definition 29.15.1.** Let $f : X \to S$ be a morphism of schemes.

1. We say that $f$ is **locally of finite type** if for every affine opens $U \subset X$, $V \subset S$ with $f(U) \subset V$ the ring map $\mathcal{O}_S(V) \to \mathcal{O}_X(U)$ is of finite type.

2. We say that $f$ is **of finite type** if it is locally of finite type and quasi-compact.

### 中文翻译

**定义 29.15.1.** 设 $f : X \to S$ 是概形态射。

1. 称 $f$ 是**局部有限型**的（locally of finite type），如果对每对仿射开集 $U \subset X$, $V \subset S$ 满足 $f(U) \subset V$，环映射 $\mathcal{O}_S(V) \to \mathcal{O}_X(U)$ 是有限型的。

2. 称 $f$ 是**有限型**的（of finite type），如果它既是局部有限型的又是拟紧的。

## 3. 概念依赖图

```
                    有限型态射 (Finite Type)
                           |
          +----------------+----------------+
          |                |                |
    局部有限型        拟紧性           环映射有限型
    (Locally of     (Quasi-          (Finite Type
     Finite Type)    Compact)         Ring Map)
          |                |                |
          +----------------+----------------+
                           |
                组合条件：有限型 = 局部有限型 + 拟紧
                           |
       +-------------------+-------------------+
       |                   |                   |
   有限态射           射影态射          固有态射
   (Finite)         (Projective)      (Proper)
       |                   |                   |
   有限+整           有限型+分离       有限型+分离
                       +整体构造      +泛闭
```

**前置概念：**
- 环映射的有限型（Finite Type Ring Maps）
- 拟紧态射（Quasi-compact Morphisms）
- 局部性质（Local Properties）

**依赖此概念：**
- 固有态射（Proper Morphisms）
- 射影态射（Projective Morphisms）
- 有限呈现态射（Finite Presentation）
- Jacobson概形

## 4. 证明概要

### 4.1 有限型的判别准则

**引理 29.15.2:** 设 $f : X \to S$ 是概形态射。以下条件等价：

1. $f$ 是局部有限型的
2. 对每个仿射开 $V \subset S$，$f^{-1}(V)$ 可以被仿射开 $\{U_i\}$ 覆盖，使得每个 $\mathcal{O}_S(V) \to \mathcal{O}_X(U_i)$ 是有限型的
3. 存在仿射开覆盖 $S = \bigcup V_j$，使得每个 $f^{-1}(V_j)$ 可以被仿射开 $\{U_{ji}\}$ 覆盖，使得每个 $\mathcal{O}_S(V_j) \to \mathcal{O}_X(U_{ji})$ 是有限型的

**证明思路：** 
- (1)⇒(2)⇒(3) 显然
- (3)⇒(1) 需要验证对任意仿射开对，环映射有限型。利用有限型环映射的局部性质：若 $R \to A$ 在 $D(f_i)$ 上有限型且 $\{f_i\}$ 生成单位理想，则 $R \to A$ 有限型。

### 4.2 与有限态射的关系

**引理 29.15.5:** 闭浸入是有限型的。

**证明：** 闭浸入对应商环映射 $R \to R/I$，显然是有限型的（生成元就是1的像）。

**引理 29.15.6:** 有限型态射的纤维是有限型概形（在剩余域上）。

这反映了"有限型"的几何意义：纤维是"有限维"的。

### 4.3 稳定性性质

**引理 29.15.3:** 局部有限型的复合是局部有限型的。

**证明：** 若 $R \to S$ 和 $S \to T$ 都是有限型，则 $T$ 可由有限个 $S$-元素生成，每个 $S$ 元素又由有限个 $R$-元素生成。因此 $T$ 由有限个 $R$-元素生成。

**引理 29.15.4:** 有限型在基变换下保持。

## 5. 与FormalMath的对应关系

| FormalMath概念 | Stacks Project对应 | Lean4/mathlib4 |
|----------------|-------------------|----------------|
| `RingHom.FiniteType` | 有限型环映射 | `RingHom.FiniteType` ✓ |
| `QuasiCompact` | 拟紧态射 | `QuasiCompact` ✓ |
| `LocallyOfFiniteType` | 局部有限型 | `LocallyOfFiniteType` ✓ |
| `FiniteType` | 有限型态射 | `FiniteType` ✓ |
| `Scheme` | 概形 | `Scheme` ✓ |

**mathlib4对应代码：**
```lean
-- 环映射有限型
class RingHom.FiniteType {R S : Type*} [CommRing R] [CommRing S] 
    (f : R →+* S) : Prop where
  -- S可由R上的有限个元素生成
  exists_finset : ∃ s : Finset S, 
    Subalgebra.toSubmodule (Algebra.adjoin R (s : Set S)) = ⊤

-- 局部有限型态射
class LocallyOfFiniteType {X Y : Scheme} (f : X ⟶ Y) : Prop where
  -- 局部上由环映射有限型刻画
  finiteType_affine : ∀ (U : X.Opens) (V : Y.Opens) [IsAffine U] [IsAffine V]
    (h : U.ι ≫ f = V.ι), RingHom.FiniteType ...

-- 有限型态射
class FiniteType {X Y : Scheme} (f : X ⟶ Y) : Prop where
  locallyOfFiniteType : LocallyOfFiniteType f
  quasiCompact : QuasiCompact f
```

## 6. 应用与重要性

### 6.1 为什么有限型重要？

**有限型的几何意义：**

- **有限维性：** 纤维是域上的有限型概形 = "有限维代数簇"
- **有限描述：** 可用有限个多项式方程描述
- **可计算性：** 有限数据可编码在计算机中

### 6.2 与有限态射的对比

| 性质 | 有限态射 | 有限型态射 |
|------|---------|-----------|
| 环论对应 | 模有限 | 代数有限型 |
| 纤维 | 零维（有限点） | 有限维 |
| 例子 | 正规化、Frobenius | 仿射空间、射影空间 |
| 闭性 | 固有的 | 需要额外假设 |

### 6.3 Jacobson概形

**定义：** 概形 $X$ 是Jacobson的，如果每个闭点都可以由其闭包确定。

**定理：** 若 $X$ 在域 $k$ 上是有限型的，则 $X$ 是Jacobson的。

这是有限型概形的重要性质，在代数几何的许多构造中都有用。

### 6.4 Noether正规化

**定理（Noether正规化）：** 设 $k$ 是域，$A$ 是有限型 $k$-代数。则存在 $d \geq 0$ 和单射：

$$k[x_1, \ldots, x_d] \hookrightarrow A$$

使得 $A$ 在 $k[x_1, \ldots, x_d]$ 上有限。

这给出了有限型代数的"标准形式"。

### 6.5 应用实例

**例1：维数理论**

有限型概形有良好定义的维数，且维数函数有良好的性质。

**例2：希尔伯特概形**

Hilbert概形参数化射影空间中的闭子概形，这些子概形自动是有限型的。

**例3：模空间**

大多数自然的模函子（如曲线模空间）产生的概形是有限型的。

## 7. 与其他资源的关联

| 资源 | 章节 | 关联内容 |
|------|------|---------|
| Hartshorne | II.3 | 有限型态射的定义与例子 |
| Hartshorne | II.4 | 分离性+有限型 = 固有性的一部分 |
| Hartshorne | I.4 | Noether正规化 |
| Vakil | 8.1 | 有限型的直观解释 |
| Matsumura | Ch.4 | 有限型环扩张 |

**Stacks Project交叉引用：**
- Tag 00F4: 环映射有限型
- Tag 01T6: 分离态射
- Tag 01W7: 固有态射
- Tag 01T8: valuative criterion
- Tag 02V0: 平坦模

## 8. Lean4形式化展望

### 8.1 当前状态

mathlib4中有限型态射已有较好的形式化：

```lean
-- 已完成
class RingHom.FiniteType {R S : Type*} [CommRing R] [CommRing S] 
    (f : R →+* S) : Prop

class LocallyOfFiniteType {X Y : Scheme} (f : X ⟶ Y) : Prop

class FiniteType {X Y : Scheme} (f : X ⟶ Y) : Prop

-- 基本性质
theorem FiniteType.comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [FiniteType f] [FiniteType g] : FiniteType (f ≫ g)

instance FiniteType.baseChange {X Y : Scheme} (f : X ⟶ Y) [FiniteType f]
    {Z : Scheme} (g : Z ⟶ Y) : FiniteType (pullback.snd f g)
```

### 8.2 待形式化内容

```lean
-- Jacobson性质
theorem isJacobson_of_finiteType_over_field {X : Scheme} [IsFiniteType X]
    (h : ∃ k : Field, X ≅ Spec (Algebra k)) : IsJacobson X := sorry

-- Noether正规化
theorem noetherNormalization {k : Type*} [Field k] {A : Type*} [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ (d : ℕ) (f : MvPolynomial (Fin d) k →+* A),
    Function.Injective f ∧ RingHom.Finite (algebraMap ... ) := sorry

-- 维数理论
theorem dimension_finiteType_field {X : Scheme} [IsFiniteType X]
    (h : ∃ k : Field, X ≅ Spec (Algebra k)) :
    ∃ d : ℕ, dimension X = d := sorry
```

### 8.3 形式化路线图

```
阶段1: 基础定义 ✓
  └── RingHom.FiniteType
  └── LocallyOfFiniteType
  └── FiniteType

阶段2: 基本性质 ✓
  └── 复合封闭性
  └── 基变换封闭性
  └── 局部性质

阶段3: 高级性质 (进行中)
  └── Jacobson性质
  └── Noether正规化
  └── 维数理论

阶段4: 应用 (计划中)
  └── Hilbert概形
  └── 模空间理论
  └── 相交理论
```

---

**文档版本：** Round 36  
**创建日期：** 2026-04-09
