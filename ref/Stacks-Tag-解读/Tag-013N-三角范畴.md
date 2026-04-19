---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 013N - 三角范畴（Triangulated Categories）

> **来源**: [Stacks Project](https://stacks.math.columbia.edu/tag/013N)  
> **创建日期**: 2026-04-10  
> **Round**: 37

---

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 013N |
| **英文名称** | Triangulated Categories |
| **中文名称** | 三角范畴 |
| **数学分支** | 同调代数 / 代数几何 |
| **所属章节** | Derived Categories |
| **难度等级** | 高级 |

**前置知识要求**：加法范畴、复形、同伦、平移函子

---

## 2. 定理/定义原文

### 英文原文 (Stacks Project)

**Definition 013N.** A **triangulated category** is an additive category $\mathcal{D}$ endowed with:

1. An additive automorphism $[1] : \mathcal{D} \to \mathcal{D}$ called the **shift functor** or **translation functor**.

2. A class of **distinguished triangles** (or **exact triangles**), often denoted $X \to Y \to Z \to X[1]$.

These data are subject to the following axioms:

- **TR1**: 
  - (a) Any morphism $f: X \to Y$ can be extended to a distinguished triangle $X \xrightarrow{f} Y \to Z \to X[1]$.
  - (b) The triangle $X \xrightarrow{\text{id}} X \to 0 \to X[1]$ is distinguished.
  - (c) Any triangle isomorphic to a distinguished triangle is distinguished.

- **TR2**: A triangle $X \to Y \to Z \to X[1]$ is distinguished if and only if $Y \to Z \to X[1] \to Y[1]$ is distinguished.

- **TR3**: Given a commutative diagram with distinguished triangles as rows, there exists a morphism $Z \to Z'$ making the diagram commute.

- **TR4** (Octahedral axiom): [Technical condition]

### 中文翻译

**定义 013N.** **三角范畴** 是配备以下结构的加法范畴 $\mathcal{D}$：

1. 加法自同构 $[1] : \mathcal{D} \to \mathcal{D}$，称为 **平移函子** 或 **位移函子**。

2. 一类 **特异三角形**（或 **正合三角形**），常记为 $X \to Y \to Z \to X[1]$。

这些数据满足以下公理：

- **TR1**:
  - (a) 任意态射 $f: X \to Y$ 可扩张为特异三角形 $X \xrightarrow{f} Y \to Z \to X[1]$。
  - (b) 三角形 $X \xrightarrow{\text{id}} X \to 0 \to X[1]$ 是特异的。
  - (c) 任何与特异三角形同构的三角形也是特异的。

- **TR2**: 三角形 $X \to Y \to Z \to X[1]$ 是特异的当且仅当 $Y \to Z \to X[1] \to Y[1]$ 是特异的。

- **TR3**: 给定以特异三角形为行的交换图，存在态射 $Z \to Z'$ 使图交换。

- **TR4** (八面体公理): [技术性条件]

---

## 3. 概念依赖图

```
                    ┌─────────────────────┐
                    │     加法范畴        │
                    │    (Additive)       │
                    └─────────┬───────────┘
                              │
              ┌───────────────┼───────────────┐
              ▼               ▼               ▼
       ┌────────────┐  ┌────────────┐  ┌────────────┐
       │  平移函子  │  │ 特异三角形 │  │  态射锥    │
       │    [1]    │  │  X→Y→Z→X[1]│  │   Cone(f) │
       └─────┬──────┘  └─────┬──────┘  └─────┬──────┘
             │               │               │
             └───────────────┼───────────────┘
                             ▼
                    ┌─────────────────┐
                    │     TR公理      │
                    │  ┌───────────┐  │
                    │  │ TR1-TR4   │  │
                    │  │ 八面体    │  │
                    │  └───────────┘  │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
       ┌────────────┐ ┌────────────┐ ┌────────────┐
       │ 同伦范畴   │  │ 导出范畴   │  │ 稳定同伦  │
       │  K(𝒜)     │  │   D(𝒜)    │  │  范畴     │
       └────────────┘ └────────────┘ └────────────┘
```

**依赖概念说明**：
- **加法范畴 (Additive Category)**：具有零对象、有限双积、阿贝尔群结构的态射集
- **平移函子 (Shift Functor)**：$[n]: \mathcal{D} \to \mathcal{D}$，$n \in \mathbb{Z}$
- **特异三角形 (Distinguished Triangle)**：推广短正合列的概念
- **八面体公理 (Octahedral Axiom)**：保证平移的相容性，TR4

---

## 4. 证明概要

### 核心命题

同伦范畴 $K(\mathcal{A})$ 和导出范畴 $D(\mathcal{A})$ 构成三角范畴。

### 证明步骤

**Step 1: 平移函子的构造**

对于复形 $X^\bullet$，定义平移：

$$(X[1])^n = X^{n+1}, \quad d_{X[1]}^n = -d_X^{n+1}$$

验证这是范畴自同构。

**Step 2: 映射锥构造**

对于态射 $f: X^\bullet \to Y^\bullet$，定义映射锥：

$$C(f)^n = X^{n+1} \oplus Y^n$$

$$d_{C(f)}^n = \begin{pmatrix} -d_X^{n+1} & 0 \\ f^{n+1} & d_Y^n \end{pmatrix}$$

**Step 3: 特异三角形的定义**

三角形 $X^\bullet \xrightarrow{f} Y^\bullet \to C(f) \to X^\bullet[1]$ 是特异的，其中：
- $Y^\bullet \to C(f)$ 是包含
- $C(f) \to X^\bullet[1]$ 是投影

**Step 4: TR公理的验证**

- **TR1**: 由映射锥的存在性保证
- **TR2**: 通过映射锥的性质验证旋转等价性
- **TR3**: 利用同伦提升性质
- **TR4**: 八面体公理由复形的双复形结构保证

**Step 5: 同伦范畴的三角结构**

在同伦范畴 $K(\mathcal{A})$ 中，同伦等价的态射被等同，保持三角结构。

---

## 5. 与FormalMath对应关系

| Stacks Project | FormalMath对应内容 |
|----------------|-------------------|
| 三角范畴 | `docs/category-theory/triangulated-categories.md` |
| 同伦范畴 | `docs/homological-algebra/homotopy-category.md` |
| 导出范畴 | `docs/category-theory/derived-categories.md` |
| 平移函子 | `docs/homological-algebra/chain-complex.md` 平移 |

**推荐学习路径**：
1. 掌握加法范畴的基础（双积、零对象）
2. 学习复形与同伦等价
3. 理解映射锥的构造
4. 掌握TR公理的几何意义
5. 学习导出范畴的三角结构

---

## 6. 应用与重要性

### 实际应用

1. **导出范畴理论**
   - D^b(X) 是研究概形的核心工具
   - Fourier-Mukai变换

2. **表示论**
   - 稳定模范畴的三角结构
   - 倾斜理论

3. **代数拓扑**
   - 稳定同伦范畴
   - 谱序列的构造

4. **代数几何**
   - Verdier对偶
   - 反常层理论

### 重要性

- **同调代数的现代化**：三角范畴是同调代数的自然框架
- **导出函子的统一**：Ext、Tor等函子在三角范畴中统一处理
- **几何与代数的桥梁**：连接代数几何与同伦论

---

## 7. 与其他资源关联

### 参考资源

| 资源类型 | 推荐内容 | 关联度 |
|----------|----------|--------|
| **教材** | Neeman《Triangulated Categories》 | ⭐⭐⭐⭐⭐ |
| **教材** | Gelfand-Manin《Methods of Homological Algebra》 | ⭐⭐⭐⭐⭐ |
| **讲义** | Huybrechts《Fourier-Mukai Transforms》第1章 | ⭐⭐⭐⭐ |
| **论文** | Verdier《Des catégories dérivées》 | ⭐⭐⭐⭐⭐ |

### 相关Tags

- **Tag 013P**：正合函子
- **Tag 013S**：同伦范畴
- **Tag 05QK**：导出范畴
- **Tag 0145**：t-结构

---

## 8. Lean4形式化展望

### 当前形式化状态

三角范畴的形式化在mathlib4中是高级目标：

```lean4
-- 概念性代码框架
import Mathlib.CategoryTheory.Triangulated.Basic
import Mathlib.CategoryTheory.Shift.Basic

open CategoryTheory Limits

-- 三角范畴的公理化定义
class TriangulatedCategory (C : Type u) [Category.{v} C]
    [HasZeroObject C] [HasShift C ℤ] where
  /-- 特异三角形类 -/
  distinguishedTriangles : Set (Triangle C)
  
  /-- TR1: 每个态射可扩张为特异三角形 -/
  mem_distinguishedTriangles_of_morphism {X Y : C} (f : X ⟶ Y) :
    ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦1⟧),
      Triangle.mk f g h ∈ distinguishedTriangles
  
  /-- TR1(b): 恒等三角形特异 -/
  mem_distinguishedTriangles_id (X : C) :
    Triangle.mk (𝟙 X) (0 : X ⟶ 0) (0 : (0 : C) ⟶ X⟦1⟧) ∈ distinguishedTriangles
  
  /-- TR2: 旋转等价 -/
  rotate_distinguishedTriangles (T : Triangle C) :
    T ∈ distinguishedTriangles ↔ T.rotate ∈ distinguishedTriangles
  
  /-- TR3: 态射提升 -/
  complete_distinguishedTriangles (T₁ T₂ : Triangle C)
    (hT₁ : T₁ ∈ distinguishedTriangles) (hT₂ : T₂ ∈ distinguishedTriangles)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ (c : T₁.obj₃ ⟶ T₂.obj₃), T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ 
      T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃
  
  /-- TR4: 八面体公理 -/
  octahedron_axiom : ...
```

### 形式化挑战

1. **八面体公理的表述**：需要精确的形式化八面体图
2. **平移函子的协调性**：$[m] \circ [n] \cong [m+n]$ 的自然同构
3. **导出范畴的构造**：从阿贝尔范畴构造三角范畴

### 推荐形式化路径

```
Phase 1: 平移函子
  └── 定义HasShift类型类
  └── 验证函子性质
  
Phase 2: 三角形结构
  └── 定义Triangle结构
  └── 实现特异三角形类
  
Phase 3: TR公理
  └── TR1-TR3的形式化
  └── TR4八面体公理
  
Phase 4: 实例构造
  └── 同伦范畴K(𝒜)
  └── 导出范畴D(𝒜)
```

---

## 版本历史

| 版本 | 日期 | 修改内容 |
|------|------|----------|
| v1.0 | 2026-04-10 | 初始版本创建 |

---

> **声明**：本文档基于Stacks Project开源数学资源创建，遵循Creative Commons Attribution-ShareAlike 4.0 International License。
