---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Tor函子

## Mathlib4 引用

```lean
import Mathlib.Algebra.Homology.Tor

namespace HomologicalAlgebra

/-- Tor函子的定义 -/
theorem tor_functor
    {R : Type*} [Ring R]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (n : ℕ) :
    Tor R n M N ≃ AddCommGroup.of
      (ModuleCat.of R M ⊗ ModuleCat.of R N)⟦n⟧ := by
  -- Tor是张量积的导出函子
  apply tor_iso_shifted_tensor

/-- Tor的平衡性 -/
theorem tor_balance
    {R : Type*} [Ring R]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (n : ℕ) :
    Tor R n M N ≅ Tor' R n M N := by
  -- Tor可以用投射分解或平坦分解计算
  apply tor_balance_iso

end HomologicalAlgebra
```

## 数学背景

Tor函子是张量积函子的左导出函子，与Ext函子对偶。名字来源于"torsion"（挠），因为对于Abel群，$\text{Tor}^\mathbb{Z}_1(M, N)$ 度量了两个群之间的"挠"相互作用。Tor函子在同调代数、代数拓扑（特别是Künneth公式）和交换代数中有重要应用。它是测量张量积"不保持正合性"的工具。

## 直观解释

Tor函子量化了张量积的"扭曲"行为。当两个模相乘时，如果它们都有"洞"（挠元素），这些洞可能相互作用产生新的结构。$\text{Tor}_1$ 捕捉这种一阶相互作用，更高阶的Tor则捕捉更复杂的交互。在几何上，这对应于积空间中的"意外"同调类——本不应存在但由于代数扭曲而产生的同调。

## 形式化表述

设 $R$ 是环，$M$ 是右 $R$-模，$N$ 是左 $R$-模。

**定义**：$\text{Tor}^R_n(M, N) = L_n(M \otimes_R -)(N)$

使用 $N$ 的投射分解 $P_\bullet \to N$：
$$\text{Tor}^R_n(M, N) = H_n(M \otimes_R P_\bullet)$$

**平衡性**：也可以用 $M$ 的投射分解计算，结果同构。

**基本性质**：

- $\text{Tor}^R_0(M, N) = M \otimes_R N$
- 若 $M$ 或 $N$ 平坦，则 $\text{Tor}^R_n(M, N) = 0$（$n \geq 1$）

## 证明思路

1. **选择投射分解**：$P_\bullet \to N$ 是投射分解
2. **张量作用**：构造复形 $M \otimes_R P_\bullet$
3. **计算同调**：取第 $n$ 阶同调群
4. **验证平衡性**：证明两种方式（左/右分解）等价

## 示例

### 示例 1：Abel群的Tor

**问题**：计算 $\text{Tor}^\mathbb{Z}_1(\mathbb{Z}/m\mathbb{Z}, \mathbb{Z}/n\mathbb{Z})$。

**解答**：

使用 $\mathbb{Z}/n\mathbb{Z}$ 的投射分解：
$$0 \to \mathbb{Z} \xrightarrow{\cdot n} \mathbb{Z} \to \mathbb{Z}/n\mathbb{Z} \to 0$$

张量 $\mathbb{Z}/m\mathbb{Z}$ 后计算同调：
$$\text{Tor}^\mathbb{Z}_1(\mathbb{Z}/m\mathbb{Z}, \mathbb{Z}/n\mathbb{Z}) \cong \mathbb{Z}/\gcd(m,n)\mathbb{Z}$$

这与Ext的结果相同（对Abel群的对偶性）。

### 示例 2：局部化与Tor

**问题**：设 $S$ 是交换环 $R$ 的乘闭子集，证明 $S^{-1}R$ 是平坦 $R$-模。

**解答**：

等价于证明 $\text{Tor}^R_1(S^{-1}R, M) = 0$ 对所有 $M$ 成立。

$S^{-1}R \otimes_R M \cong S^{-1}M$，且局部化是正合函子，因此 $S^{-1}R$ 平坦。

## 应用

- **Universal Coefficient Theorem**：同调系数的改变
- **Künneth公式**：积空间的同调计算
- **平坦性判别**：环模的平坦性测试
- **交换代数**：正则局部环的刻画
- **代数几何**：层张量积的性质

## 相关概念

- [Ext函子](./ext-functor.md)：Hom的导出函子
- [张量积](./tensor-product.md)：Tor的基础函子
- [平坦模](./flat-module.md)：Tor消失的模
- [投射模](./projective-module.md)：Tor消失的条件
- [导出函子](./derived-functor.md)：Tor的一般框架

## 参考

### 教材

- Weibel, C.A. An Introduction to Homological Algebra. Cambridge, 1994. Chapter 3
- Rotman, J.J. An Introduction to Homological Algebra. Springer, 2009. Chapter 10

### 论文

- Cartan, H. & Eilenberg, S. Homological Algebra. Princeton, 1956. Chapter 5

### 在线资源

- [Tor Functor Wikipedia](https://en.wikipedia.org/wiki/Tor_functor)
- [Stacks Project - Tor](https://stacks.math.columbia.edu/tag/00DW)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
