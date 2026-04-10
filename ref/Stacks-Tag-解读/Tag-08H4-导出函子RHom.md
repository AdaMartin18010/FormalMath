# Stacks Project Tag 08H4 - 导出函子RHom

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 08H4 |
| **定义名称** | 导出函子 RHom (Derived Functor RHom) |
| **所属章节** | Section 15.73 - RHom (More on Algebra) |
| **数学领域** | 同调代数、导出范畴、代数几何 |
| **Stacks Project链接** | https://stacks.math.columbia.edu/tag/08H4 |

## 2. 定理/定义原文

**定义 (Tag 08H4):**

设 $(\mathcal{C}, \mathcal{O})$ 是环化空间，$K^\bullet, L^\bullet$ 是 $\mathcal{O}$-模的复形。定义**导出Hom函子**：

$$R\text{Hom}_{\mathcal{O}}(K^\bullet, L^\bullet) := \text{Hom}_{D(\mathcal{O})}(K^\bullet, L^\bullet)$$

更具体地，若 $L^\bullet \to I^\bullet$ 是K-内射消解，则：

$$R\text{Hom}_{\mathcal{O}}(K^\bullet, L^\bullet) \cong \text{Hom}_{K(\mathcal{O})}(K^\bullet, I^\bullet)$$

**上同调实现:**

对 $n \in \mathbb{Z}$，定义**Ext函子**：

$$\text{Ext}^n_{\mathcal{O}}(K^\bullet, L^\bullet) := H^n(R\text{Hom}_{\mathcal{O}}(K^\bullet, L^\bullet))$$

**计算方式:**
- 若 $K^\bullet$ 由投射对象组成且上有界，则：
$$\text{Ext}^n(K^\bullet, L^\bullet) = H^n(\text{Hom}^\bullet(K^\bullet, L^\bullet))$$
- 若 $L^\bullet$ 是K-内射的，则：
$$\text{Ext}^n(K^\bullet, L^\bullet) = H^n(\text{Hom}_{K(\mathcal{O})}(K^\bullet, L^\bullet[n]))$$

## 3. 概念依赖图

```
导出函子 RHom (Tag 08H4)
│
├── 核心前置概念
│   ├── 环化空间 (Tag 006N)
│   ├── 导出范畴 D(𝒪) (Tag 08FR)
│   ├── K-内射复形 (Tag 013Z)
│   ├── 同伦范畴 K(𝒪) (Tag 0113)
│   └── Hom复形 Hom^∙ (Tag 0A98)
│
├── 经典Ext理论
│   ├── Ext函子 Ext^n (Tag 00DV)
│   ├── 投射消解 (Tag 00E1)
│   ├── 内射消解 (Tag 013X)
│   └── Yoneda Ext (Tag 0A5A)
│
├── 导出函子技术
│   ├── 右导出函子 RF (Tag 05R1)
│   ├── 导出张量积 ⊗^L (Tag 08HP)
│   └── 伴随对 (Tag 003L)
│
└── 后继应用
    ├── Grothendieck对偶
    ├── 完美复形 (Tag 08FT)
    └── 导出Morita理论
```

## 4. 证明概要

**存在性与良定性证明:**

**Step 1: K-内射消解的存在性**
- 假设：环化空间有足够多内射对象
- 由Tag 013Y，任意复形 $L^\bullet$ 有K-内射消解 $L^\bullet \to I^\bullet$

**Step 2: 同伦范畴计算**
- 对于固定的 $K^\bullet$，函子 $\text{Hom}_{K(\mathcal{O})}(K^\bullet, -)$ 是左正合的
- 取右导出函子即得 $R\text{Hom}$

**Step 3: 导出范畴解释**
- 利用导出范畴的泛性质
- $R\text{Hom}_{\mathcal{O}}(K^\bullet, -)$ 是 $\text{Hom}_{D(\mathcal{O})}(K^\bullet, -)$ 的导出

**Step 4: 双变函子延拓**
- $R\text{Hom}$ 对两个变量都有定义
- 若 $K^\bullet$ 由投射（或平坦）对象组成，可用Hom复形计算

**重要性质证明:**

**谱序列:**
- 若 $K^\bullet$ 上有界，有谱序列：
$$E_2^{p,q} = \text{Ext}^p(K^{-q}, L^\bullet) \Rightarrow \text{Ext}^{p+q}(K^\bullet, L^\bullet)$$

**局部化性质:**
- 对开集 $U \subseteq X$，$(R\text{Hom}_X(K, L))|_U \cong R\text{Hom}_U(K|_U, L|_U)$

## 5. 与FormalMath对应

| Stacks Project概念 | FormalMath对应内容 | 文档路径 |
|-------------------|-------------------|----------|
| 导出Hom RHom | 同调代数/RHom | `concept/homological_algebra/rhom.md` |
| Ext函子 | 同调代数/Ext | `concept/homological_algebra/ext_functor.md` |
| K-内射复形 | 同调代数/K-内射复形 | `concept/homological_algebra/kinjective.md` |
| 导出范畴 | 范畴论/导出范畴 | `concept/category_theory/derived_category.md` |

**当前对齐状态:**
- ⚠️ **概念对齐** - 核心概念在文档中有描述，完整形式化待补充

**建议补充内容:**
```markdown
## RHom详解

### 定义
设 $(X, \mathcal{O})$ 环化空间，$K^\bullet, L^\bullet$ 复形：
$$R\text{Hom}_{\mathcal{O}}(K^\bullet, L^\bullet) := \text{Hom}_{D(\mathcal{O})}(K^\bullet, L^\bullet)$$

### 计算
取 $L^\bullet \to I^\bullet$ 为K-内射消解：
$$R\text{Hom}_{\mathcal{O}}(K^\bullet, L^\bullet) = \text{Hom}_{K(\mathcal{O})}(K^\bullet, I^\bullet)$$

### Ext函子
$$\text{Ext}^n(K^\bullet, L^\bullet) = H^n(R\text{Hom}(K^\bullet, L^\bullet))$$

### 重要性质
1. **局部化:** $(R\text{Hom}_X(K,L))|_U \cong R\text{Hom}_U(K|_U,L|_U)$
2. **与导出张量积的伴随:** $R\text{Hom}(K \otimes^L L, M) \cong R\text{Hom}(K, R\text{Hom}(L, M))$
3. **与上同调的交换:** 在一定条件下与 $Rf_*$ 交换

### 应用
- Grothendieck对偶
- 完美复形的判别
- 导出Morita等价
```

## 6. 应用与重要性

**核心应用场景:**

### 1. Grothendieck对偶
- $R\text{Hom}$ 是Grothendieck对偶理论的核心函子
- 对偶化复形 $K_X$ 满足 $R\text{Hom}(F, K_X) \cong R\text{Hom}(Rf_*F, \mathcal{O}_Y)$

### 2. 完美复形 (Tag 08FT)
- 复形 $K^\bullet$ 是**完美的**若局部拟同构于有界投射复形
- 判别准则: $K^\bullet$ 完美当且仅当 $R\text{Hom}(K^\bullet, -)$ 与直和交换

### 3. 层上同调的内部Hom
- 对 $\mathcal{O}$-模层，$R\text{Hom}$ 推广了内部Hom
- 用于构造对偶层、相对对偶理论

### 4. 导出Morita理论
- 两个环的导出范畴等价当且仅当存在特定的 $R\text{Hom}$ 关系
- 倾斜理论的核心工具

### 5. 相交理论
- 计算Ext群判断子概形的相交性质
- Serre的相交重数公式

**重要性评级:** ⭐⭐⭐⭐⭐ (5/5)

RHom是导出同调代数的核心函子，是现代代数几何、表示论、数学物理的基石。

## 7. 与其他资源关联

### Stacks Project内部关联
| 相关Tag | 关联描述 |
|---------|----------|
| Tag 013Z | K-内射复形（计算基础） |
| Tag 08HP | 导出张量积（伴随对） |
| Tag 08FT | 完美复形（判别应用） |
| Tag 08FR | 导出范畴 |
| Tag 0A98 | Hom复形 |

### 外部资源

**经典文献:**
1. **Hartshorne, R.** "Residues and Duality"
   - 第II章: 导出Hom的系统阐述

2. **Verdier, J.-L.** "Des catégories dérivées..."
   - 导出范畴的奠基论文

**现代教材:**
1. **Gelfand & Manin** "Methods of Homological Algebra"
   - 第3章: 导出函子

2. **Kashiwara & Schapira** "Sheaves on Manifolds"
   - 第2章: 环化空间上的同调代数

3. **Huybrechts, D.** "Fourier-Mukai Transforms"
   - 第3章: 导出范畴技术

### 相关理论
- **Serre duality**: 代数几何对偶
- **Poincaré duality**: 拓扑对偶
- **Tilting theory**: 表示论中的倾斜理论

## 8. Lean4形式化展望

### 形式化难度评估: ⭐⭐⭐⭐⭐ (5/5)

**主要挑战:**
1. **导出层范畴** - 需要环化空间上的导出范畴
2. **K-内射消解** - 层论中的存在性证明
3. **双变函子** - 同时对两个变量的导出
4. **与RΓ的交换** - 整体截面与RHom的关系

**Lean4实现路线:**

```lean4
-- 概念框架（设想）
import Mathlib

-- 环化空间上的导出Hom
section RHom

variable {X : Type*} [TopologicalSpace X] (𝒪 : SheafOfRings X)

-- RHom作为导出范畴的Hom
noncomputable
def RHom {K L : CochainComplex (Sheaf.Ab 𝒪)} :
    DerivedCategory (Sheaf.Ab 𝒪) :=
  DerivedCategory.hom K L

-- 通过K-内射消解计算
def RHom_KInjective (K : CochainComplex (Sheaf.Ab 𝒪))
    (L : CochainComplex (Sheaf.Ab 𝒪))
    (hL : KInjective L) :
    CochainComplex Ab :=
  HomComplex K L

-- Ext函子
def Ext (n : ℤ) {K L : CochainComplex (Sheaf.Ab 𝒪)} : Ab :=
  (RHom K L).homology n

end RHom

-- 应用：Grothendieck对偶的陈述
theorem grothendieck_duality {X Y : Scheme} (f : X ⟶ Y) [Proper f]
    (K : DerivedCategory (QCohSheaf X)) :
    RHom (Rf_* K) (ω_Y) ≅ Rf_* (RHom K (ω_X)) := by
  sorry
  -- 需要完整的对偶理论
```

**Mathlib现状:**
- `DerivedCategory` 在发展中
- 层论的同调代数基础存在
- K-内射层消解尚未形式化
- RHom需要新的框架

**形式化优先级:** MEDIUM
- 是高级同调代数的核心
- 依赖大量前置理论
- 建议在其他导出函子完成后推进

---

**文档编制日期:** 2026年4月  
**作者:** FormalMath项目团队  
**版本:** 1.0
