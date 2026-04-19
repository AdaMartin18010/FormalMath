---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: 张量积性质 (Tensor Product Properties)
---
# 张量积性质 (Tensor Product Properties)

## Mathlib4 引用

```lean
import Mathlib.Algebra.Module.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

namespace TensorProduct

variable {R : Type*} [CommRing R]
variable {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [Module R M] [Module R N] [Module R P]

/-- 张量积的右正合性 -/
theorem right_exactness {f : M →ₗ[R] N} (hf : Function.Surjective f) :
    Function.Surjective (f.rTensor P : M ⊗[R] P →ₗ[R] N ⊗[R] P) := by
  intro z
  -- 利用张量积的泛性质
  apply TensorProduct.induction_on z
  · -- 零元情形
    use 0
    simp
  · -- 纯张量情形
    intro n p
    rcases hf n with ⟨m, hm⟩
    use m ⊗ₜ p
    simp [hm]
  · -- 加法封闭
    sorry

/-- 张量积的结合律 -/
theorem associativity :
    (M ⊗[R] N) ⊗[R] P ≅ₗ[R] M ⊗[R] (N ⊗[R] P) := by
  refine LinearEquiv.ofLinear
    (lift <| lift <| comp (curry <| lift <| lcurry <| mk R M (N ⊗[R] P)) (mk R N P))
    (lift <| comp (uncurry <| mk R (M ⊗[R] N) P) (mk R M N))
    ?_ ?_
  · -- 验证逆
    sorry
  · -- 验证逆
    sorry

/-- 张量积与直和的分配律 -/
theorem direct_sum_distrib {ι : Type*} [Fintype ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    (⨁ i, M i) ⊗[R] N ≅ₗ[R] ⨁ i, (M i ⊗[R] N) := by
  sorry

end TensorProduct
```

## 数学背景

张量积是数学中最基本的构造之一，最初由Hermann Grassmann在1844年（外代数）和Giuseppe Peano在1888年（双线性形式）引入。现代张量积理论由Bourbaki学派在1940年代系统化。它在表示论、微分几何、物理学（特别是广义相对论和量子力学）以及同调代数中都有核心应用，是连接代数与几何的桥梁。

## 直观解释

张量积是**将双线性运算转化为线性运算的通用构造**。

想象两个向量空间 $M$ 和 $N$，我们想构造一个空间来"存储"所有形如 $m \otimes n$ 的对象，满足双线性关系：$(m_1 + m_2) \otimes n = m_1 \otimes n + m_2 \otimes n$ 等。张量积 $M \otimes N$ 就是满足这些关系的"最一般"的空间。它可以看作是从 $M^* \times N^*$ 到基域的双线性映射的空间。

## 形式化表述

$M \otimes_R N$ 是满足以下泛性质的 $R$-模：

给定双线性映射 $\varphi: M \times N \to P$，存在唯一的线性映射 $\tilde{\varphi}: M \otimes N \to P$ 使得 $\tilde{\varphi}(m \otimes n) = \varphi(m, n)$。

**基本性质**：

1. **结合律**：$(M \otimes N) \otimes P \cong M \otimes (N \otimes P)$
2. **交换律**：$M \otimes N \cong N \otimes M$
3. **分配律**：$(\bigoplus_i M_i) \otimes N \cong \bigoplus_i (M_i \otimes N)$
4. **右正合性**：$M' \to M \to M'' \to 0$ 正合 $\Rightarrow$ $M' \otimes N \to M \otimes N \to M'' \otimes N \to 0$ 正合

## 证明思路

1. **泛性质刻画**：张量积由泛性质唯一确定（差同构）
2. **结合律**：构造两边到 $M \times N \times P$ 的三重线性映射空间的同构
3. **分配律**：利用直和的泛性质和有限性假设
4. **右正合性**：
   - 满射性：利用张量积由纯张量生成
   - 在 $M'' \otimes N$ 处的正合性：构造逆映射或利用同调代数

核心洞察是张量积作为表示双线性函子的伴随函子。

## 示例

### 示例 1：向量空间的张量积

设 $M = \mathbb{R}^2$，$N = \mathbb{R}^3$，则 $M \otimes N \cong \mathbb{R}^6$。

基：$\{e_1 \otimes f_1, e_1 \otimes f_2, e_1 \otimes f_3, e_2 \otimes f_1, e_2 \otimes f_2, e_2 \otimes f_3\}$

### 示例 2：基变换

设 $V$ 是 $\mathbb{Q}$ 上的向量空间，$\mathbb{Q}(\sqrt{2})$ 是二次扩张。

$V \otimes_\mathbb{Q} \mathbb{Q}(\sqrt{2})$ 将 $V$ "标量扩张"到更大的域。

### 示例 3：非自由模的张量积

$\mathbb{Z}_2 \otimes_\mathbb{Z} \mathbb{Z}_3 = 0$（因为 $a \otimes b = 3(a \otimes b) = a \otimes 3b = a \otimes 0 = 0$）

这说明张量积可以"坍缩"不同挠性的模。

## 应用

- **表示论**：表示的张量积构造
- **微分几何**：张量场、微分形式
- **代数几何**：层和向量丛的运算
- **物理学**：应力-能量张量、量子纠缠
- **同调代数**：Tor函子的定义

## 相关概念

- Tor函子 (Tor Functor)：张量积的左导出
- 平坦模 (Flat Module)：保持正合性的模
- Hom与张量积 (Hom-Tensor Adjunction)：伴随关系
- 对称代数 (Symmetric Algebra)：张量积的对称化
- 外代数 (Exterior Algebra)：反对称张量积

## 参考

### 教材

- [Atiyah & Macdonald. Introduction to Commutative Algebra. Addison-Wesley, 1969. Chapter 2]
- [Dummit & Foote. Abstract Algebra. Wiley, 3rd edition, 2004. Chapter 10]

### 历史文献

- [Bourbaki. Algèbre, Chapitre II. Hermann, 1947]

### 在线资源

- [Mathlib4 文档 - TensorProduct][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/TensorProduct/Basic.html](需更新)
- [Keith Conrad - Tensor Products][https://kconrad.math.uconn.edu/blurbs/linmultialg/tensorprod.pdf](需更新)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
