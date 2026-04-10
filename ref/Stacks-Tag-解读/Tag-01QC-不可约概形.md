# Stacks Project Tag 01QC - 不可约概形（Irreducible Schemes）

> **来源**: [Stacks Project](https://stacks.math.columbia.edu/tag/01QC)  
> **创建日期**: 2026-04-10  
> **Round**: 37

---

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01QC |
| **英文名称** | Irreducible Schemes |
| **中文名称** | 不可约概形 |
| **数学分支** | 代数几何 |
| **所属章节** | Schemes |
| **难度等级** | 初级 |

**前置知识要求**：概形基础、拓扑不可约性、整概形

---

## 2. 定理/定义原文

### 英文原文 (Stacks Project)

**Definition 01QC.** A scheme $X$ is **irreducible** if its underlying topological space is irreducible. Equivalently, $X$ is irreducible if it is nonempty and every nonempty open subscheme is dense in $X$.

Recall that a topological space $X$ is **irreducible** if $X$ is not the union of two proper closed subsets.

### 中文翻译

**定义 01QC.** 概形 $X$ 称为 **不可约的**，如果其底拓扑空间是不可约的。等价地，$X$ 不可约当且仅当它非空且每个非空开子概形在 $X$ 中稠密。

回顾：拓扑空间 $X$ **不可约** 是指 $X$ 不是两个真闭子集的并。

---

## 3. 概念依赖图

```
                    ┌─────────────────────┐
                    │       概形 X        │
                    └─────────┬───────────┘
                              │
              ┌───────────────┼───────────────┐
              ▼               ▼               ▼
       ┌────────────┐  ┌────────────┐  ┌────────────┐
       │  底空间    │  │  开稠密子集│  │  真闭子集  │
       │    |X|    │  │    U ⊆ X   │  │   Z ⊊ X   │
       └─────┬──────┘  └─────┬──────┘  └─────┬──────┘
             │               │               │
             └───────────────┼───────────────┘
                             ▼
                    ┌─────────────────┐
                    │   不可约概形     │
                    │  定义等价性     │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
       ┌────────────┐ ┌────────────┐ ┌────────────┐
       │  整概形    │  │ 唯一泛点   │  │ 函数域     │
       │Integral    │  │ Generic    │  │ Fraction   │
       │ Scheme     │  │ Point      │  │ Field      │
       └────────────┘ └────────────┘ └────────────┘
```

**依赖概念说明**：
- **不可约空间**：不能写成两个真闭子集的并：$X \neq Z_1 \cup Z_2$，$Z_1, Z_2 \subsetneq X$
- **稠密子集**：$\overline{U} = X$
- **整概形**：既约且不可约的概形
- **泛点**：不可约闭子集的唯一一般点

---

## 4. 证明概要

### 核心命题

不可约概形的等价刻画及其与整概形的关系。

### 证明步骤

**Step 1: 不可约性的等价条件**

**命题**：以下条件等价：
1. $X$ 不可约
2. 任意两个非空开子集相交
3. 每个非空开子集稠密
4. 不存在真闭覆盖

**证明**：
- (1 $\Leftrightarrow$ 4)：由定义
- (2 $\Leftrightarrow$ 3)：$U$ 稠密 $\Leftrightarrow$ $U$ 与任意非空开集相交
- (1 $\Leftrightarrow$ 2)：若 $X = Z_1 \cup Z_2$，则 $(X \setminus Z_1) \cap (X \setminus Z_2) = \emptyset$

**Step 2: 泛点的存在性**

**命题**：不可约概形有唯一的泛点。

**证明**：设 $\xi$ 为对应于 $\mathcal{O}_{X,\eta}$ 的素理想的点，其中 $\eta$ 是底空间的泛点。

不可约闭子集与素理想一一对应，故不可约空间有唯一的一般点。

**Step 3: 整概形的刻画**

**命题**：概形 $X$ 是整概形当且仅当：
- $X$ 不可约且既约
- $\Leftrightarrow$ $X$ 连通且对任意开集 $U$，$\mathcal{O}_X(U)$ 是整环

**证明**：
- 既约：无幂零局部环
- 不可约 $\Leftrightarrow$ 局部环有唯一极小素理想
- 结合 $\Rightarrow$ 局部环是整环 $\Rightarrow$ 截面是整环

**Step 4: 函数域**

**命题**：整概形 $X$ 有良定义的函数域 $K(X) = \mathcal{O}_{X,\xi}$，其中 $\xi$ 是泛点。

**证明**：$\mathcal{O}_{X,\xi}$ 是局部整环，其分式域即为函数域。对任意仿射开集 $U = \text{Spec}(A)$，$K(X) = \text{Frac}(A)$。

---

## 5. 与FormalMath对应关系

| Stacks Project | FormalMath对应内容 |
|----------------|-------------------|
| 不可约概形 | `docs/algebraic-geometry/irreducible-schemes.md` |
| 整概形 | `docs/algebraic-geometry/integral-schemes.md` |
| 函数域 | `docs/algebraic-geometry/function-fields.md` |
| 泛点 | `docs/algebraic-geometry/generic-points.md` |

**推荐学习路径**：
1. 学习拓扑空间的不可约性
2. 理解概形的既约性
3. 掌握不可约与整概形的关系
4. 学习泛点的概念
5. 了解函数域的构造

---

## 6. 应用与重要性

### 实际应用

1. **代数簇的结构**
   - 代数簇分解为不可约分支
   - 不可约分支对应于素理想的极小元

2. **有理函数**
   - 整概形上的有理函数域
   - 双有理几何的基础

3. **除子理论**
   - Weil除子在余维1的不可约子簇上定义
   - Cartier除子与线丛

4. **平展拓扑**
   - 不可约性是平展拓扑的性质
   - 几何不可约性

### 重要性

- **基本几何性质**：不可约性是概形的核心性质
- **分解定理**：任意概形可分解为不可约分支
- **函数域理论**：整概形的函数域是有理函数的基础
- **维数理论**：不可约分支的维数定义

---

## 7. 与其他资源关联

### 参考资源

| 资源类型 | 推荐内容 | 关联度 |
|----------|----------|--------|
| **教材** | Hartshorne《代数几何》习题3.1-3.2 | ⭐⭐⭐⭐⭐ |
| **教材** | Liu《Algebraic Geometry》2.4节 | ⭐⭐⭐⭐ |
| **讲义** | Vakil《代数几何基础》4.6节 | ⭐⭐⭐⭐⭐ |
| **讲义** | Görtz-Wedhorn《Algebraic Geometry I》3.2节 | ⭐⭐⭐⭐ |

### 相关Tags

- **Tag 01Q9**：连通概形
- **Tag 004U**：不可约拓扑空间
- **Tag 01R1**：既约概形
- **Tag 01RG**：整概形

---

## 8. Lean4形式化展望

### 当前形式化状态

mathlib4中不可约概形的形式化：

```lean4
-- 概念性代码框架
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Irreducible

open AlgebraicGeometry TopologicalSpace

variable {X : Scheme}

-- 不可约概形的定义
def IsIrreducibleScheme (X : Scheme) : Prop :=
  IrreducibleSpace X.toTopCat

-- 等价刻画：任意两个非空开集相交
theorem isIrreducibleScheme_iff (X : Scheme) :
    IsIrreducibleScheme X ↔ 
    (Nonempty X.carrier ∧ 
     ∀ (U V : X.Opens), 
       U ≠ ⊥ → V ≠ ⊥ → U ∩ V ≠ ⊥) := by
  -- 使用拓扑不可约性的等价刻画
  sorry

-- 整概形的定义
def IsIntegralScheme (X : Scheme) : Prop :=
  IsIrreducibleScheme X ∧ IsReduced X

-- 泛点
def genericPoint (X : Scheme) [IsIrreducibleScheme X] : X.carrier :=
  -- 底空间的一般点
  (IrreducibleSpace.genericPoint X.toTopCat).1

-- 函数域
def functionField (X : Scheme) [IsIntegralScheme X] : Type _ :=
  X.presheaf.stalk (genericPoint X)
```

### 形式化挑战

1. **既约概形**：幂零理想的整体化
2. **整环层**：截面环的整性条件
3. **函数域的独立性**：不依赖于仿射覆盖的选择

### 推荐形式化路径

```
Phase 1: 基础定义
  └── 不可约概形
  └── 等价条件的形式化
  
Phase 2: 整概形
  └── 既约概形的定义
  └── 整概形的刻画
  
Phase 3: 泛点与函数域
  └── 一般点的存在性
  └── 函数域的构造
  
Phase 4: 分解定理
  └── 不可约分支
  └── 分解的唯一性
```

---

## 版本历史

| 版本 | 日期 | 修改内容 |
|------|------|----------|
| v1.0 | 2026-04-10 | 初始版本创建 |

---

> **声明**：本文档基于Stacks Project开源数学资源创建，遵循Creative Commons Attribution-ShareAlike 4.0 International License。
