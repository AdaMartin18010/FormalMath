---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 万有系数定理 (Universal Coefficient Theorem)
---
# 万有系数定理 (Universal Coefficient Theorem)

## Mathlib4 引用

```lean
import Mathlib.Algebra.Homology.Homology
import Mathlib.Algebra.Category.ModuleCat.Abelian

namespace UniversalCoefficient

variable {C : Type*} [Category C] [Abelian C]
variable (G : Ab) (n : ℕ)

/-- 万有系数定理：同调与系数的Ext关系 -/
theorem universal_coefficient_homology {X : Type*} [TopologicalSpace X] :
    ∃ (short_exact : ShortExact (Ab.of (H_n X ⊗ G)) (H_n (X; G)) (Ab.of (Tor₁(H_{n-1} X, G)))),
      short_exact.IsSplit := by
  -- 链复形的张量积分解
  sorry

/-- 上同调版本 -/
theorem universal_coefficient_cohomology {X : Type*} [TopologicalSpace X] :
    ∃ (short_exact : ShortExact (Ab.of (Ext¹(H_{n-1} X, G))) (H^n(X; G)) (Ab.of (Hom(H_n X, G)))),
      True := by
  -- Hom与Ext的关系
  sorry

end UniversalCoefficient
```

## 数学背景

万有系数定理是代数拓扑中关于同调群与系数群之间关系的结构性结果。它表明，带有一般系数群 $G$ 的同调群 $H_n(X; G)$ 可以由整数同调群 $H_n(X; \mathbb{Z})$ 和系数群 $G$ 通过代数运算（张量积和Tor函子）决定。这一定理解释了为什么整数同调包含了计算任意系数同调所需的全部信息。

## 直观解释

万有系数定理告诉我们：**一般系数的同调可以由整数同调和系数群代数构造**。

想象同调群是一个"模板"，系数群是"颜料"。定理说，你可以先用模板（整数同调）画出形状，然后用颜料（系数群）填充。张量积对应"均匀填充"，而Tor函子对应"修正扭曲"——处理整数同调中的挠元与系数群的相互作用。

## 形式化表述

设 $X$ 是拓扑空间，$G$ 是阿贝尔群。

**同调万有系数定理**：

存在短正合列：
$$0 \to H_n(X; \mathbb{Z}) \otimes G \to H_n(X; G) \to \text{Tor}_1(H_{n-1}(X; \mathbb{Z}), G) \to 0$$

且此列分裂（非典范）。

**上同调万有系数定理**：

存在短正合列：
$$0 \to \text{Ext}^1(H_{n-1}(X; \mathbb{Z}), G) \to H^n(X; G) \to \text{Hom}(H_n(X; \mathbb{Z}), G) \to 0$$

## 证明思路

1. **自由分解**：
   - 链复形 $C_*(X)$ 有自由Abel群
   - 与 $G$ 张量得到 $C_*(X) \otimes G$

2. **Künneth公式**：
   - 链复形张量积的同调
   - 出现张量积和Tor项

3. **短正合列构造**：
   - 从链复形代数导出
   - 验证正合性

4. **分裂性**：
   - 自由Abel群的投射性
   - 非典范分裂存在

核心洞察是链复形的代数结构与同调的关系。

## 示例

### 示例 1：实射影平面

$\mathbb{R}P^2$：$H_0 = \mathbb{Z}$，$H_1 = \mathbb{Z}_2$，$H_2 = 0$。

$H_1(\mathbb{R}P^2; \mathbb{Z}_2) = (\mathbb{Z}_2 \otimes \mathbb{Z}_2) \oplus \text{Tor}(\mathbb{Z}, \mathbb{Z}_2) = \mathbb{Z}_2$。

### 示例 2：系数 $\mathbb{Q}$

$G = \mathbb{Q}$（平坦），$\text{Tor}_1(-, \mathbb{Q}) = 0$。

$H_n(X; \mathbb{Q}) \cong H_n(X; \mathbb{Z}) \otimes \mathbb{Q}$。

### 示例 3：系数 $\mathbb{Z}_p$

$G = \mathbb{Z}_p$，考虑挠元的影响。

Tor项捕捉 $p$-挠的结构。

## 应用

- **同调计算**：从整数同调推导其他系数
- **上同调环**：乘法结构的计算
- **示性类**：Stiefel-Whitney类的系数
- **代数几何**：étale上同调
- **表示论**：群同调的系数变化

## 相关概念

- [Tor函子 (Tor Functor)](./tor-functor.md)：张量积的左导出
- [Ext函子 (Ext Functor)](./ext-functor.md)：Hom的右导出
- [张量积 (Tensor Product)](./tensor-product.md)：模的双线性运算
- [链复形 (Chain Complex)](./chain-complex.md)：同调代数基础
- [分裂正合列 (Split Exact Sequence)](./split-exact-sequence.md)：直和分解

## 参考

### 教材

- [Hatcher. Algebraic Topology. Cambridge, 2002. Chapter 3]
- [Spanier. Algebraic Topology. Springer, 1966. Chapter 5]

### 在线资源

- [Mathlib4 文档 - Homology](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/Homology.html)
- [Wikipedia - Universal Coefficient Theorem](https://en.wikipedia.org/wiki/Universal_coefficient_theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
