---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 013P - 正合函子（Exact Functors）

> **来源**: [Stacks Project](https://stacks.math.columbia.edu/tag/013P)  
> **创建日期**: 2026-04-10  
> **Round**: 37

---

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 013P |
| **英文名称** | Exact Functors |
| **中文名称** | 正合函子 |
| **数学分支** | 同调代数 / 范畴论 |
| **所属章节** | Derived Categories |
| **难度等级** | 中等 |

**前置知识要求**：阿贝尔范畴、短正合列、函子、导出函子

---

## 2. 定理/定义原文

### 英文原文 (Stacks Project)

**Definition 013P.** Let $F : \mathcal{A} \to \mathcal{B}$ be a functor between abelian categories.

1. We say $F$ is **exact** if it transforms any short exact sequence in $\mathcal{A}$ into a short exact sequence in $\mathcal{B}$.

2. We say $F$ is **left exact** if it transforms any short exact sequence $0 \to A \to B \to C \to 0$ in $\mathcal{A}$ into an exact sequence $0 \to F(A) \to F(B) \to F(C)$ in $\mathcal{B}$.

3. We say $F$ is **right exact** if it transforms any short exact sequence $0 \to A \to B \to C \to 0$ in $\mathcal{A}$ into an exact sequence $F(A) \to F(B) \to F(C) \to 0$ in $\mathcal{B}$.

### 中文翻译

**定义 013P.** 设 $F : \mathcal{A} \to \mathcal{B}$ 为阿贝尔范畴之间的函子。

1. 称 $F$ 是 **正合的** (exact)，如果它将 $\mathcal{A}$ 中的任意短正合列转化为 $\mathcal{B}$ 中的短正合列。

2. 称 $F$ 是 **左正合的** (left exact)，如果它将 $\mathcal{A}$ 中的任意短正合列 $0 \to A \to B \to C \to 0$ 转化为 $\mathcal{B}$ 中的正合列 $0 \to F(A) \to F(B) \to F(C)$。

3. 称 $F$ 是 **右正合的** (right exact)，如果它将 $\mathcal{A}$ 中的任意短正合列 $0 \to A \to B \to C \to 0$ 转化为 $\mathcal{B}$ 中的正合列 $F(A) \to F(B) \to F(C) \to 0$。

---

## 3. 概念依赖图

```
                    ┌─────────────────────┐
                    │    阿贝尔范畴       │
                    │    𝒜, ℬ            │
                    └─────────┬───────────┘
                              │
              ┌───────────────┼───────────────┐
              ▼               ▼               ▼
       ┌────────────┐  ┌────────────┐  ┌────────────┐
       │  函子 F    │  │ 短正合列   │  │  正合性   │
       │  𝒜 → ℬ    │  │ 0→A→B→C→0 │  │  分类     │
       └─────┬──────┘  └─────┬──────┘  └─────┬──────┘
             │               │               │
             └───────────────┼───────────────┘
                             ▼
                    ┌─────────────────┐
                    │   正合性类型    │
                    │  ┌───────────┐  │
                    │  │ 左正合    │  │
                    │  │ 右正合    │  │
                    │  │ 正合      │  │
                    │  └───────────┘  │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
       ┌────────────┐ ┌────────────┐ ┌────────────┐
       │ 典型例子   │  │ 典型例子   │  │ 典型例子   │
       │ Hom(X,-)  │  │ Hom(-,X)  │  │  X ⊗ -    │
       │  左正合   │  │  左正合   │  │  右正合   │
       └────────────┘ └────────────┘ └────────────┘
```

**依赖概念说明**：
- **阿贝尔范畴 (Abelian Category)**：具有核、余核、像的加法范畴
- **短正合列 (Short Exact Sequence)**：$0 \to A \xrightarrow{f} B \xrightarrow{g} C \to 0$，其中 $\ker g = \text{im } f$
- **左正合 (Left Exact)**：保持核但不一定保持余核
- **右正合 (Right Exact)**：保持余核但不一定保持核

---

## 4. 证明概要

### 核心命题

正合函子保持所有有限极限和有限余极限。

### 证明步骤

**Step 1: 正合函子与有限极限**

**命题**：函子 $F$ 正合当且仅当它保持有限极限和有限余极限。

**证明**：
- ($\Rightarrow$)：短正合列 $0 \to A \to B \to C \to 0$ 等价于 $A = \ker(B \to C)$ 且 $C = \text{coker}(A \to B)$
- 正合函子保持核和余核
- 有限极限/余极限可由核/余核构造

**Step 2: 左正合函子的刻画**

**命题**：$F$ 左正合 $\Leftrightarrow$ $F$ 保持有限极限。

**证明**：
- 核是拉回（有限极限）
- 左正合 $\Rightarrow$ 保持核 $\Rightarrow$ 保持有限极限
- 反之，保持核保证左正合性

**Step 3: 右正合函子的刻画**

**命题**：$F$ 右正合 $\Leftrightarrow$ $F$ 保持有限余极限。

**证明**：类似于Step 2，使用余核和推出。

**Step 4: 典型例子的验证**

- **$\text{Hom}(X, -)$ 左正合**：
  $$0 \to A \to B \to C \text{ 正合} \Rightarrow 0 \to \text{Hom}(X, A) \to \text{Hom}(X, B) \to \text{Hom}(X, C) \text{ 正合}$$
  
- **$X \otimes -$ 右正合**：张量积的右正合性是模范畴的基本性质

---

## 5. 与FormalMath对应关系

| Stacks Project | FormalMath对应内容 |
|----------------|-------------------|
| 正合函子 | `docs/category-theory/exact-functors.md` |
| 阿贝尔范畴 | `docs/category-theory/abelian-categories.md` |
| 导出函子 | `docs/homological-algebra/derived-functors.md` |
| 短正合列 | `docs/homological-algebra/exact-sequences.md` |

**推荐学习路径**：
1. 理解阿贝尔范畴的结构（核、余核）
2. 学习短正合列的定义与性质
3. 掌握正合函子的等价刻画
4. 学习导出函子理论（Ext、Tor）
5. 了解正合函子在三角范畴中的对应

---

## 6. 应用与重要性

### 实际应用

1. **导出函子理论**
   - 非正合函子的左/右导出：$L^i F$、$R^i F$
   - Ext函子：$\text{Ext}^i(X, Y) = R^i\text{Hom}(X, -)(Y)$
   - Tor函子：$\text{Tor}_i(X, Y) = L^i(X \otimes -)(Y)$

2. **层上同调**
   - 整体截面函子 $\Gamma(X, -)$ 左正合
   - 上同调函子 $H^i(X, -) = R^i\Gamma(X, -)$

3. **局部化理论**
   - 正合函子与局部化的相容性
   - Serre商范畴

### 重要性

- **同调代数基础**：导出函子理论的出发点
- **计算工具**：通过正合性传递代数信息
- **分类理论**：Morita等价中的关键角色

---

## 7. 与其他资源关联

### 参考资源

| 资源类型 | 推荐内容 | 关联度 |
|----------|----------|--------|
| **教材** | Weibel《同调代数导论》第1-2章 | ⭐⭐⭐⭐⭐ |
| **教材** | Rotman《同调代数导论》函子章节 | ⭐⭐⭐⭐ |
| **教材** | Kashiwara-Shapira《Categories and Sheaves》 | ⭐⭐⭐⭐⭐ |
| **讲义** | Vakil《代数几何基础》23章 | ⭐⭐⭐⭐ |

### 相关Tags

- **Tag 0105**：阿贝尔范畴
- **Tag 010H**：短正合列
- **Tag 0132**：导出函子
- **Tag 010L**：极限与余极限

---

## 8. Lean4形式化展望

### 当前形式化状态

mathlib4中正合函子已有基础形式化：

```lean4
-- mathlib4中的正合函子
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

open CategoryTheory CategoryTheory.Limits

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

-- 正合函子的定义
class ExactFunctor (F : C ⥤ D) : Prop where
  /-- 保持短正合列 -/
  preserves_short_exact : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    ShortExact f g → ShortExact (F.map f) (F.map g)

-- 左正合函子
class LeftExactFunctor (F : C ⥤ D) : Prop where
  /-- 保持核 -/
  preserves_kernels : ∀ {X Y : C} (f : X ⟶ Y),
    PreservesLimit (parallelPair f 0) F

-- 右正合函子  
class RightExactFunctor (F : C ⥤ D) : Prop where
  /-- 保持余核 -/
  preserves_cokernels : ∀ {X Y : C} (f : X ⟶ Y),
    PreservesColimit (parallelPair f 0) F

-- 等价刻画
theorem exact_iff_preserves_finite_limits_and_colimits (F : C ⥤ D) :
    ExactFunctor F ↔ 
    (PreservesFiniteLimits F ∧ PreservesFiniteColimits F) := by
  -- 正合函子等价于保持有限极限和余极限
  sorry
```

### 形式化挑战

1. **有限极限的保持**：需要处理有限图表的极限
2. **正合性判据**：各种等价刻画的证明
3. **导出函子的构造**：从非正合函子构造导出函子

### 推荐形式化路径

```
Phase 1: 基本定义
  └── 正合/左正合/右正合函子
  └── 保持核/余核的性质
  
Phase 2: 等价刻画
  └── 正合 ↔ 保持有限极限和余极限
  └── 左正合 ↔ 保持有限极限
  
Phase 3: 典型例子
  └── Hom函子
  └── 张量积函子
  └── 层截面函子
  
Phase 4: 导出函子
  └── 左导出函子 L^i F
  └── 右导出函子 R^i F
```

---

## 版本历史

| 版本 | 日期 | 修改内容 |
|------|------|----------|
| v1.0 | 2026-04-10 | 初始版本创建 |

---

> **声明**：本文档基于Stacks Project开源数学资源创建，遵循Creative Commons Attribution-ShareAlike 4.0 International License。
