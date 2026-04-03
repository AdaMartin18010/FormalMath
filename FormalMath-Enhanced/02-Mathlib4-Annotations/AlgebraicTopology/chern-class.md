# Chern类理论

## Mathlib4 引用

```lean
import Mathlib.AlgebraicTopology.ChernClass

namespace AlgebraicTopology

/-- Chern类的定义 -/
theorem chern_class
    {B : Type*} [TopologicalSpace B]
    {E : TopologicalSpace} (π : E → B)
    [IsComplexVectorBundle E B π] :
    ∃ (c : ℕ → H^{2*}(B, ℤ)),
      c 0 = 1 ∧
      TotalChernClass E = ∏ (1 + c i) := by
  -- 全陈类分解为陈类
  sorry

/-- Whitney和公式 -/
theorem whitney_sum_formula
    {B : Type*} [TopologicalSpace B]
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (π_E : E → B) (π_F : F → B)
    [IsComplexVectorBundle E B π_E]
    [IsComplexVectorBundle F B π_F] :
    TotalChernClass (E ⊕ F) =
      TotalChernClass E * TotalChernClass F := by
  -- 直和丛的陈类相乘
  sorry

end AlgebraicTopology
```

## 数学背景

Chern类由Shiing-Shen Chern（陈省身）在1946年引入，是复向量丛的最重要的拓扑不变量。陈类将代数拓扑与复几何联系起来，是指标定理、Riemann-Roch定理和数学物理中弦理论的基础工具。陈类满足优美的函子性和乘法性质（Whitney和公式），使其成为计算的有力工具。Chern因这项工作获得了Wolf奖和Shaw奖。

## 直观解释

Chern类如同复向量丛的"曲率指纹"。想象一个复向量丛如同空间中的一族复向量空间——在每个点附近，我们可以尝试将其"展平"（找局部平凡化）。如果整体可以展平（平凡丛），所有陈类为零。陈类度量了这种"展平"的障碍程度，是拓扑扭曲的指标。$c_k$ 特别地度量了丛的"k维复杂性"。

## 形式化表述

设 $\pi: E \to B$ 是秩 $n$ 的复向量丛。

**全陈类**：$c(E) = 1 + c_1(E) + c_2(E) + \cdots + c_n(E)$，其中 $c_k(E) \in H^{2k}(B; \mathbb{Z})$。

**公理化刻画**：

1. **函子性**：$c(f^*E) = f^*c(E)$
2. **Whitney和**：$c(E \oplus F) = c(E) \cdot c(F)$
3. **归一化**：线丛 $L$ 的陈类 $c_1(L) = e(L_\mathbb{R})$（Euler类）

**曲率表示**：若 $\nabla$ 是联络，曲率 $F_\nabla$，则
$$c(E) = \det(I + \frac{i}{2\pi} F_\nabla)$$

## 证明思路

1. **分裂原理**：将一般丛分裂为线丛的直和
2. **分类空间**：用 $BU(n)$ 的上同调定义陈类
3. **公理验证**：验证函子性、Whitney和和归一化
4. **曲率表示**：用Chern-Weil理论构造
5. **乘积公式**：验证陈特征的性质

## 示例

### 示例 1：切丛的陈类

**问题**：计算 $\mathbb{CP}^n$ 切丛的陈类。

**解答**：

欧拉序列：$0 \to \mathcal{O} \to \mathcal{O}(1)^{\oplus (n+1)} \to T\mathbb{CP}^n \to 0$

由Whitney和公式：
$$c(T\mathbb{CP}^n) = (1 + H)^{n+1}$$
其中 $H = c_1(\mathcal{O}(1))$ 是超平面类。

### 示例 2：Gauss-Bonnet定理

**问题**：陈类与Euler示性数的关系。

**解答**：

对紧复流形 $M^{2n}$：
$$\int_M c_n(TM) = \chi(M)$$

这是经典Gauss-Bonnet定理的高维推广。

$n=1$ 时，$c_1(TM) = \chi(M) \cdot [\text{pt}]$。

## 应用

- **指标定理**：Atiyah-Singer定理的K-理论形式
- **Riemann-Roch定理**：代数几何中的核心结果
- **弦理论**：异常消去的条件
- **代数K-理论**：Bloch-Wigner函数
- **数学物理**：Yang-Mills理论

## 相关概念

- [Stiefel-Whitney类](./stiefel-whitney-class.md)：实丛的版本
- [Pontryagin类](./pontryagin-class.md)：实丛的复化
- [Euler类](./euler-class.md)：最高陈类的特例
- [陈特征](./chern-character.md)：K-理论的同构
- [Todd类](./todd-class.md)：Riemann-Roch定理中的修正

## 参考

### 教材

- Bott, R. & Tu, L.W. Differential Forms in Algebraic Topology. Springer, 1982.
- Milnor, J.W. & Stasheff, J.D. Characteristic Classes. Princeton, 1974.

### 论文

- Chern, S.S. Characteristic classes of Hermitian manifolds. Ann. of Math., 47: 85-121, 1946.
- Grothendieck, A. La théorie des classes de Chern. Bull. Soc. Math. France, 86: 137-154, 1958.

### 在线资源

- [Chern Class Wikipedia](https://en.wikipedia.org/wiki/Chern_class)
- [nLab - Chern Class](https://ncatlab.org/nlab/show/Chern+class)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
