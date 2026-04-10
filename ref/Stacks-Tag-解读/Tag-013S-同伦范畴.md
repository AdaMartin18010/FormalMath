# Stacks Project Tag 013S - 同伦范畴（Homotopy Category）

> **来源**: [Stacks Project](https://stacks.math.columbia.edu/tag/013S)  
> **创建日期**: 2026-04-10  
> **Round**: 37

---

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 013S |
| **英文名称** | The Homotopy Category |
| **中文名称** | 同伦范畴 |
| **数学分支** | 同调代数 / 代数拓扑 |
| **所属章节** | Derived Categories |
| **难度等级** | 中等 |

**前置知识要求**：链复形、链映射、链同伦、阿贝尔范畴

---

## 2. 定理/定义原文

### 英文原文 (Stacks Project)

**Definition 013S.** Let $\mathcal{A}$ be an additive category. The **homotopy category** $K(\mathcal{A})$ is defined as follows:

1. The objects of $K(\mathcal{A})$ are complexes in $\mathcal{A}$.

2. The morphisms in $K(\mathcal{A})$ are homotopy classes of morphisms of complexes, i.e.,
   
   $$\text{Hom}_{K(\mathcal{A})}(X^\bullet, Y^\bullet) = \text{Hom}_{\text{Comp}(\mathcal{A})}(X^\bullet, Y^\bullet) / \sim$$
   
   where $f \sim g$ if there exists a homotopy $h$ between $f$ and $g$.

If $\mathcal{A}$ is abelian, then $K(\mathcal{A})$ is a triangulated category with the distinguished triangles being those isomorphic to triangles of the form $X^\bullet \to Y^\bullet \to C(f) \to X^\bullet[1]$.

### 中文翻译

**定义 013S.** 设 $\mathcal{A}$ 为加法范畴。**同伦范畴** $K(\mathcal{A})$ 定义如下：

1. $K(\mathcal{A})$ 的对象为 $\mathcal{A}$ 中的复形。

2. $K(\mathcal{A})$ 中的态射为复形态射的同伦类，即：
   
   $$\text{Hom}_{K(\mathcal{A})}(X^\bullet, Y^\bullet) = \text{Hom}_{\text{Comp}(\mathcal{A})}(X^\bullet, Y^\bullet) / \sim$$
   
   其中 $f \sim g$ 如果存在 $f$ 和 $g$ 之间的同伦 $h$。

若 $\mathcal{A}$ 是阿贝尔范畴，则 $K(\mathcal{A})$ 是以特异三角形为那些同构于 $X^\bullet \to Y^\bullet \to C(f) \to X^\bullet[1]$ 形式的三角形的三角范畴。

---

## 3. 概念依赖图

```
                    ┌─────────────────────┐
                    │    加法范畴 𝒜       │
                    └─────────┬───────────┘
                              │
              ┌───────────────┼───────────────┐
              ▼               ▼               ▼
       ┌────────────┐  ┌────────────┐  ┌────────────┐
       │   复形     │  │  链映射    │  │  链同伦    │
       │  X^•, Y^• │  │  f, g      │  │  h: f ≃ g │
       └─────┬──────┘  └─────┬──────┘  └─────┬──────┘
             │               │               │
             └───────────────┼───────────────┘
                             ▼
                    ┌─────────────────┐
                    │  复形范畴 Comp(𝒜)│
                    │  态射 = 链映射   │
                    └────────┬────────┘
                             │  商去同伦
                             ▼
                    ┌─────────────────┐
                    │   同伦范畴 K(𝒜)  │
                    │ 态射 = 同伦类    │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
       ┌────────────┐ ┌────────────┐ ┌────────────┐
       │ 拟同构     │  │ 导出范畴   │  │ 三角结构   │
       │ Quasi-iso │  │   D(𝒜)    │  │  [1]平移  │
       └────────────┘ └────────────┘ └────────────┘
```

**依赖概念说明**：
- **复形 (Complex)**：微分平方为零的链对象序列
- **链映射 (Chain Map)**：与微分交换的态射序列
- **链同伦 (Chain Homotopy)**：$h: f \simeq g$ 满足 $f - g = dh + hd$
- **映射锥 (Mapping Cone)**：$C(f)^n = X^{n+1} \oplus Y^n$

---

## 4. 证明概要

### 核心命题

同伦范畴 $K(\mathcal{A})$ 是三角范畴，且当 $\mathcal{A}$ 阿贝尔时具有自然的三角结构。

### 证明步骤

**Step 1: 同伦范畴的良定义性**

验证链同伦是等价关系：
- **自反性**：$f \sim f$（零同伦）
- **对称性**：$f \sim g \Rightarrow g \sim f$（取负同伦）
- **传递性**：$f \sim g, g \sim h \Rightarrow f \sim h$（同伦相加）

**Step 2: 范畴结构的验证**

- **合成良定义**：若 $f \sim f'$，$g \sim g'$，则 $g \circ f \sim g' \circ f'$
- **恒等态射**：恒等链映射的同伦类
- **结合律**：继承自复形范畴

**Step 3: 平移函子**

定义 $[1]: K(\mathcal{A}) \to K(\mathcal{A})$：
- 对象：$(X[1])^n = X^{n+1}$，$d_{X[1]}^n = -d_X^{n+1}$
- 态射：$(f[1])^n = f^{n+1}$

验证这是自同构（逆为 $[-1]$）。

**Step 4: 特异三角形的定义**

对于链映射 $f: X^\bullet \to Y^\bullet$，定义映射锥复形：

$$C(f)^n = X^{n+1} \oplus Y^n, \quad d^n = \begin{pmatrix} -d_X^{n+1} & 0 \\ f^{n+1} & d_Y^n \end{pmatrix}$$

三角形 $X^\bullet \xrightarrow{f} Y^\bullet \to C(f) \to X^\bullet[1]$ 是特异的。

**Step 5: TR公理的验证**

- **TR1**：映射锥给出态射的扩张
- **TR2**：映射锥的旋转对应
- **TR3**：同伦提升引理
- **TR4**：八面体公理由复形的双锥构造

---

## 5. 与FormalMath对应关系

| Stacks Project | FormalMath对应内容 |
|----------------|-------------------|
| 同伦范畴 | `docs/homological-algebra/homotopy-category.md` |
| 链复形 | `docs/homological-algebra/chain-complex.md` |
| 链同伦 | `docs/algebraic-topology/homotopy.md` |
| 导出范畴 | `docs/category-theory/derived-categories.md` |

**推荐学习路径**：
1. 学习复形的定义与基本操作
2. 理解链映射和链同伦的概念
3. 掌握映射锥的构造与性质
4. 学习同伦范畴的商构造
5. 理解到导出范畴的局部化

---

## 6. 应用与重要性

### 实际应用

1. **导出范畴的构造**
   - $D(\mathcal{A}) = K(\mathcal{A})[\{\text{拟同构}\}^{-1}]$
   - 同伦范畴是导出范畴的中间步骤

2. **同调不变量**
   - 同伦等价的复形具有同构的同调
   - 同伦范畴捕获了"本质"的同调信息

3. **代数拓扑**
   - 奇异链复形的同伦范畴
   - 与拓扑同伦范畴的联系

4. **代数几何**
   - 完全交的上同调计算
   - Fourier-Mukai变换的定义域

### 重要性

- **同调代数的语言**：现代同调代数的标准框架
- **导出函子**：左/右导出函子的自然定义域
- **拓扑直觉**：代数拓扑中的同伦概念在代数中的对应

---

## 7. 与其他资源关联

### 参考资源

| 资源类型 | 推荐内容 | 关联度 |
|----------|----------|--------|
| **教材** | Weibel《同调代数导论》第1章 | ⭐⭐⭐⭐⭐ |
| **教材** | Gelfand-Manin《Methods of Homological Algebra》 | ⭐⭐⭐⭐⭐ |
| **讲义** | Huybrechts《Fourier-Mukai》第2章 | ⭐⭐⭐⭐ |
| **视频** | MIT 18.915 (同调代数) | ⭐⭐⭐⭐ |

### 相关Tags

- **Tag 013N**：三角范畴
- **Tag 013P**：正合函子
- **Tag 05QK**：导出范畴
- **Tag 013W**：拟同构

---

## 8. Lean4形式化展望

### 当前形式化状态

mathlib4中同伦范畴的形式化已启动：

```lean4
-- 概念性代码框架
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.CategoryTheory.Triangulated.Basic

open CategoryTheory HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

-- 同伦范畴的定义
abbrev HomotopyCategory (C : Type u) [Category.{v} C] [Preadditive C]
    (c : ComplexShape ι) :=
  (HomologicalComplex C c) ⋙ (homotopyEquivalences C c)

-- 或更直接的定义
def HomotopyCategory' (C : Type u) [Category.{v} C] [Preadditive C]
    (c : ComplexShape ι) :=
  CategoryTheory.Quotient 
    (HomologicalComplex C c) 
    (HomotopyRel C c)

-- 三角结构
instance [Abelian C] : TriangulatedCategory (HomotopyCategory C c) where
  shift := ...
  distinguishedTriangles := 
    {T | ∃ (X Y : HomologicalComplex C c) (f : X ⟶ Y),
      T ≅ distinguishedTriangle f}
  -- TR公理的验证
```

### 形式化挑战

1. **商范畴的构造**：需要形式化同伦关系的商
2. **三角结构的验证**：TR公理的完整验证
3. **局部化函子**：到导出范畴的局部化构造

### 推荐形式化路径

```
Phase 1: 同伦关系
  └── 定义链同伦
  └── 验证等价关系
  
Phase 2: 商范畴
  └── 构造同伦范畴
  └── 验证范畴公理
  
Phase 3: 三角结构
  └── 定义平移函子
  └── 定义特异三角形
  └── 验证TR公理
  
Phase 4: 导出范畴
  └── 局部化构造
  └── 拟同构的逆向
```

---

## 版本历史

| 版本 | 日期 | 修改内容 |
|------|------|----------|
| v1.0 | 2026-04-10 | 初始版本创建 |

---

> **声明**：本文档基于Stacks Project开源数学资源创建，遵循Creative Commons Attribution-ShareAlike 4.0 International License。
