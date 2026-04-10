# Stacks Project Tag 01Q9 - 连通概形（Connected Schemes）

> **来源**: [Stacks Project](https://stacks.math.columbia.edu/tag/01Q9)  
> **创建日期**: 2026-04-10  
> **Round**: 37

---

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01Q9 |
| **英文名称** | Connected Schemes |
| **中文名称** | 连通概形 |
| **数学分支** | 代数几何 |
| **所属章节** | Schemes |
| **难度等级** | 初级 |

**前置知识要求**：概形基础、拓扑连通性、层论

---

## 2. 定理/定义原文

### 英文原文 (Stacks Project)

**Definition 01Q9.** A scheme $X$ is **connected** if its underlying topological space is connected. Equivalently, $X$ is connected if it is nonempty and not the disjoint union of two nonempty open subschemes.

### 中文翻译

**定义 01Q9.** 概形 $X$ 称为 **连通的**，如果其底拓扑空间是连通的。等价地，$X$ 连通当且仅当它非空且不是两个非空开子概形的不交并。

---

## 3. 概念依赖图

```
                    ┌─────────────────────┐
                    │       概形 X        │
                    │  (局部环化空间)      │
                    └─────────┬───────────┘
                              │
              ┌───────────────┼───────────────┐
              ▼               ▼               ▼
       ┌────────────┐  ┌────────────┐  ┌────────────┐
       │  底空间    │  │  结构层    │  │  开子概形  │
       │    |X|    │  │    𝒪_X    │  │   U ⊆ X   │
       └─────┬──────┘  └─────┬──────┘  └─────┬──────┘
             │               │               │
             └───────────────┼───────────────┘
                             ▼
                    ┌─────────────────┐
                    │   连通概形       │
                    │  定义等价性     │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
       ┌────────────┐ ┌────────────┐ ┌────────────┐
       │ 整体截面   │  │ 连通分支   │  │ 几何连通   │
       │ Γ(X,𝒪_X)  │  │ 分解唯一性 │  │ 基域扩张   │
       │ 可能非域   │  │            │  │            │
       └────────────┘ └────────────┘ └────────────┘
```

**依赖概念说明**：
- **底拓扑空间**：概形作为局部环化空间的拓扑部分
- **开子概形**：$(U, \mathcal{O}_X|_U)$，其中 $U$ 为开子集
- **不交并**：$X = U \sqcup V$，$U \cap V = \emptyset$，$U, V$ 开
- **连通性**：不能分解为两个非空不交开集的并

---

## 4. 证明概要

### 核心命题

概形连通的等价刻画。

### 证明步骤

**Step 1: 定义等价性**

**证明**：
- 概形 $X$ 连通 $\Leftrightarrow$ 底空间 $|X|$ 连通
- $|X|$ 连通 $\Leftrightarrow$ $|X|$ 不能写成两个非空不交开集的并
- $|X| = U \cup V$（不交并）$\Leftrightarrow$ $X = (U, \mathcal{O}_X|_U) \sqcup (V, \mathcal{O}_X|_V)$（开子概形的不交并）

**Step 2: 整体截面的性质**

**命题**：若 $X$ 连通，则 $\Gamma(X, \mathcal{O}_X)$ 没有非平凡幂等元。

**证明**：设 $e \in \Gamma(X, \mathcal{O}_X)$ 满足 $e^2 = e$。定义：

$$U = \{x \in X \mid e_x = 1 \in \mathcal{O}_{X,x}\}$$
$$V = \{x \in X \mid e_x = 0 \in \mathcal{O}_{X,x}\}$$

则 $U, V$ 为开集，$U \cap V = \emptyset$，$X = U \cup V$。由连通性，$U = \emptyset$ 或 $V = \emptyset$，故 $e = 0$ 或 $e = 1$。

**Step 3: 连通分支的分解**

**命题**：任意概形可唯一分解为连通分支的不交并。

**证明**：底空间的连通分支给出概形的分解：

$$X = \bigsqcup_{i \in I} X_i$$

其中每个 $X_i$ 是极大连通开子概形（连通分支）。

---

## 5. 与FormalMath对应关系

| Stacks Project | FormalMath对应内容 |
|----------------|-------------------|
| 连通概形 | `docs/algebraic-geometry/schemes.md` 连通性 |
| 底拓扑空间 | `concept/topology.md` 拓扑基础 |
| 开子概形 | `docs/algebraic-geometry/open-subschemes.md` |
| 整体截面 | `docs/sheaf-theory/global-sections.md` |

**推荐学习路径**：
1. 复习拓扑空间的连通性
2. 学习概形的定义与结构
3. 理解底空间与概形的关系
4. 掌握连通性的等价刻画
5. 了解连通分支与几何连通性

---

## 6. 应用与重要性

### 实际应用

1. **代数簇的结构**
   - 连通分支对应于代数簇的不可约分支的并
   - 研究簇的整体性质

2. **线丛的分类**
   - 连通概形上的线丛由Picard群分类
   - $Pic(X) = H^1(X, \mathcal{O}_X^\times)$

3. **平展覆盖**
   - 连通概形的平展基本群
   - Galois理论与概形覆叠

4. **几何点**
   - 几何连通：基域扩张后仍连通
   - 代数闭域上的连通性研究

### 重要性

- **基本拓扑性质**：连通性是概形的最基本不变量之一
- **分类问题**：连通分支分解是研究概形的第一步
- **函子性**：连通性在概形态射下的表现

---

## 7. 与其他资源关联

### 参考资源

| 资源类型 | 推荐内容 | 关联度 |
|----------|----------|--------|
| **教材** | Hartshorne《代数几何》第二章 | ⭐⭐⭐⭐⭐ |
| **教材** | Liu《Algebraic Geometry》3.2节 | ⭐⭐⭐⭐ |
| **讲义** | Vakil《代数几何基础》4.6节 | ⭐⭐⭐⭐⭐ |
| **讲义** | Görtz-Wedhorn《Algebraic Geometry I》 | ⭐⭐⭐⭐ |

### 相关Tags

- **Tag 01QC**：不可约概形
- **Tag 004U**：不可约拓扑空间
- **Tag 01R1**：约化概形
- **Tag 0362**：几何连通概形

---

## 8. Lean4形式化展望

### 当前形式化状态

mathlib4中概形的连通性在代数几何库中发展：

```lean4
-- 概念性代码框架
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Connected

open AlgebraicGeometry TopologicalSpace CategoryTheory

variable {X : Scheme}

-- 连通概形的定义
def IsConnectedScheme (X : Scheme) : Prop :=
  ConnectedSpace X.toTopCat

-- 等价刻画：非空且非不交并
theorem isConnectedScheme_iff (X : Scheme) :
    IsConnectedScheme X ↔ 
    (Nonempty X.carrier ∧ 
     ∀ (U V : X.Opens), 
       U ∪ V = ⊤ → U ∩ V = ⊥ → U = ⊥ ∨ V = ⊥) := by
  -- 使用拓扑连通性的等价刻画
  sorry

-- 连通分支
def connectedComponent (x : X.carrier) : Set X.carrier :=
  connectedComponentIn ⊤ x

-- 整体截面无幂等元
theorem idempotent_constant_of_connected (X : Scheme)
    [IsConnectedScheme X] (e : Γ(X, ⊤)) (he : e^2 = e) :
    e = 0 ∨ e = 1 := by
  -- 使用幂等元的开分解
  sorry
```

### 形式化挑战

1. **概形范畴的构造**：完整的Scheme类型定义
2. **底空间的函子性**：从概形到拓扑空间的映射
3. **几何连通的定义**：基域扩张后的连通性

### 推荐形式化路径

```
Phase 1: 基础定义
  └── 概形的连通性
  └── 等价条件的形式化
  
Phase 2: 连通分支
  └── 连通分支的分解
  └── 分支的唯一性
  
Phase 3: 整体截面
  └── 幂等元的性质
  └── 连通性与截面环
  
Phase 4: 几何性质
  └── 几何连通概形
  └── 基域扩张的影响
```

---

## 版本历史

| 版本 | 日期 | 修改内容 |
|------|------|----------|
| v1.0 | 2026-04-10 | 初始版本创建 |

---

> **声明**：本文档基于Stacks Project开源数学资源创建，遵循Creative Commons Attribution-ShareAlike 4.0 International License。
