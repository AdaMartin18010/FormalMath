# Stacks Project Tag 0G2B - 导出形变函子

## 1. 基本概念与定义

### 1.1 从经典到导出

**经典形变函子：** $F: \text{Art}_k \to \text{Set}$

**问题：**

- 只能看到"连通分支"的信息
- 丢失同伦/高阶信息
- 提升性质不充分

**导出形变函子：** $\mathbf{F}: \text{dgArt}_k \to \text{Spaces}$

**优势：**

- 取值于空间（或谱），保留同伦信息
- 自然给出(∞-)群oid结构
- 完整描述所有阶的形变

### 1.2 形式定义

**定义（导出形变函子）：** 设 $k$ 为域，$\text{dgArt}_k$ 为微分分次Artin $k$-代数范畴。

**导出形变问题**是函子：$$\mathbf{F}: \text{dgArt}_k \to \mathcal{S}$$

满足：

1. $\mathbf{F}(k) \simeq *$（单点）
2. 同伦下降条件
3. 切复形的存在性

---

## 2. 数学背景与动机

### 2.1 导出形变的必要性

**例子：概形的自同构**

经典形变理论只能看到 $H^0(X, T_X)$（自同构的李代数）。

导出理论可以看到完整的自同构**群**（带其拓扑）。

**例子：高阶阻碍**

经典：一阶形变存在，二阶可能受阻

导出：所有阻碍自动编码在空间的同伦群中

### 2.2 历史发展

**Illusie (1970s):** cotangent complex与形变

**Hinich (1990s):** dg coalgebra与形变

**Getzler (2000s):** Lie代数与形变函子

**Lurie (2010s):** 导出形变理论的公理化

**Pridham:** 统一各种导出形变理论

---

## 3. 形式化性质与定理

### 3.1 Lurie的对应定理

**定理（Lurie）：** 特征0时，有等价：

$$\{\text{形式导出模问题}\} \cong \{\text{pro-可解dg Lie代数}\}$$

**对应细节：**

- 形变函子 $\mathbf{F}$ ↔ dg Lie代数 $g$
- 切空间 $T\mathbf{F} \cong g[1]$
- 形变空间 $\mathbf{F}(R) \cong MC(g \otimes m_R)$

### 3.2 切复形与阻碍

**定义：** 导出形变函子 $\mathbf{F}$ 的**切复形**是：$$T\mathbf{F} = \mathbf{F}(k[\epsilon]/\epsilon^2) \in \text{Sp}$$

**定理：** 对于Artin代数 $R$ 的扩张 $0 \to I \to \tilde{R} \to R \to 0$：

存在阻碍理论：$$ob \in \pi_{-1}(T\mathbf{F} \otimes I)$$

### 3.3 与Hochschild上同调的联系

**定理：** 代数 $A$ 的导出形变函子由 $C^*(A; A)[1]$（Hochschild上链复形）控制。

**推论：**

- 一阶形变：$HH^2(A)$
- 二阶阻碍：$HH^3(A)$
- 高阶数据：完整的Hochschild复形

---

## 4. Stacks Project 中的位置

### 4.1 章节定位

- **主要章节：** Formal Deformation Theory
- **前置Tags：**
  - Tag 0G2A (形变理论现代发展)
  - Tag 0A5Q (导出范畴)
  - Tag 0D5B (Hochschild上同调)

### 4.2 依赖关系

```
Tag 0G2B (导出形变函子)
├── Tag 0G2A (形变理论)
├── Tag 0A5Q (导出范畴)
├── Tag 0A5R (稳定∞-范畴)
└── Tag 0D5B (非交换上同调)
```

---

## 5. 应用与例子

### 5.1 具体计算

**例1：交换代数的形变**

对于 $A = k[x]/(x^2)$：

- $HH^2(A)$ 参数化一阶形变
- 导出形变函子看到所有阶的信息

**例2：概形的形变**

$X/k$ 光滑射影，导出形变函子由 $R\Gamma(X, \wedge^* T_X)$ 控制。

**例3：复结构的形变**

Kodaira-Spencer理论增强为导出形式：切复形包含所有多切空间。

### 5.2 在数学中的应用

**(1) 形变量子化**

Kontsevich的形变量子化是泊松流形的特定形变问题。

**(2) 导出交截**

两个子概形相交的导出形变给出Tor的高阶信息。

**(3) 稳定同伦理论**

Goerss-Hopkins理论：环谱的形变由André-Quillen上同调控制。

---

## 6. 与其他概念的联系

### 6.1 概念网络

```
导出形变函子 (0G2B)
│
├── dg Lie代数 ──→ 特征0理论
├── L-∞代数 ──→ 更一般
├── Hochschild复形 ──→ 代数形变
├── cotangent复形 ──→ 几何形变
├── André-Quillen上同调 ──→ 交换形变
└── 谱序列 ──→ 阻碍理论
```

### 6.2 形变理论的谱系

```
经典（Schlessinger）
    ↓
增强（Goldman-Millson）
    ↓
导出（Lurie）
    ↓
谱值（Goerss-Hopkins）
    ↓
最一般（∞-范畴）
```

---

## 7. 学习资源与参考文献

### 7.1 Stacks Project原文

- **URL:** https://stacks.math.columbia.edu/tag/0G2B
- **章节：** Formal Deformation Theory

### 7.2 核心文献

1. **Lurie, J.** "Derived Algebraic Geometry X: Formal Moduli Problems"
   - 导出形变理论的公理化

2. **Pridham, J.P.** "Unifying derived deformation theories"
   - 统一框架

3. **Manetti, M.** "Differential graded Lie algebras and formal deformation theory"
   - dg Lie代数方法

### 7.3 应用文献

- **Kontsevich, M.** "Deformation quantization of Poisson manifolds"
- **Goerss & Hopkins** "Moduli spaces of commutative ring spectra"

---

## 8. 形式化实现笔记

### 8.1 Lean 4实现

```lean
-- 微分分次Artin代数
structure DGArtinAlgebra (k : Type) [Field k] extends
    DifferentialGradedAlgebra k where
  [finiteDimensional : FiniteDimensional k carrier]
  [localRing : IsLocalRing (carrier 0)]
  [artinian : IsArtinian (carrier 0)]

-- 导出形变函子
def DerivedDeformationFunctor (k : Type) [Field k] (X : Scheme k) :
    Functor (DGArtinAlgebra k)ᵒᵖ (InfinityCategory Type) where
  obj A := {X' : DGScheme A // X' ⊗ A k ≅ X}
  map f := sorry

-- 切复形
def TangentComplex {k : Type} [Field k]
    (F : Functor (DGArtinAlgebra k)ᵒᵖ (InfinityCategory Type)) :
    Spectrum :=
  F.obj (KaehlerDGA k)
```

### 8.2 形式化挑战

1. **dg Artin代数：** 微分分次与有限性条件的结合
2. **空间值函子：** 需要∞-群oid或谱的形式化
3. **Maurer-Cartan方程：** 形变空间的显式描述

---

## 总结

Tag 0G2B (导出形变函子) 是现代形变理论的核心概念，将经典形变理论提升到导出/同伦层次。通过Lurie的对应定理，导出形变函子与dg Lie代数建立了精确联系，为代数几何、数学物理和代数拓扑中的形变问题提供了统一框架。

---

*文档生成时间：2026年4月*
*Stacks Project版本：最新*
*完成度：100个Tags冲刺第99个*
