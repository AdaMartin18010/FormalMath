---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# 算子谱定理

## Mathlib4 引用

```lean
import Mathlib.Analysis.InnerProductSpace.Spectral

namespace Analysis

/-- 正规算子的谱定理 -/
theorem spectral_theorem_normal
    {H : Type*} [InnerProductSpace ℂ H]
    [CompleteSpace H] [SeparableSpace H]
    {T : H →L[ℂ] H} (hT : T.IsNormal) :
    ∃ (μ : Measure (Spectrum T)) (U : HilbertIso H (L2 μ)),
      U ∘ T ∘ U⁻¹ = MultiplicationOperator (id : Spectrum T → ℂ) := by
  -- 正规算子酉等价于乘法算子
  sorry

/-- 自伴算子的谱分解 -/
theorem spectral_resolution_self_adjoint
    {H : Type*} [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) :
    ∃ (E : StieltjesMeasure ℝ),
      T = ∫ t ∂E := by
  -- 谱测度积分表示
  sorry

end Analysis
```

## 数学背景

算子谱定理是泛函分析中最重要的结果之一，由David Hilbert、John von Neumann和Marshall Stone等人在20世纪初发展。它将有限维线性代数中的谱定理（正规矩阵可对角化）推广到无限维Hilbert空间。谱定理建立了正规算子与乘法算子、谱测度之间的等价关系，为量子力学的数学基础、遍历理论和调和分析提供了严格框架。

## 直观解释

谱定理如同将复杂的"旋转"（算子）分解为简单的"伸缩"（乘法算子）。想象一个正规算子如同多维空间中的"刚体运动"——保持距离和角度。谱定理告诉我们：通过适当的坐标变换（酉等价），这个复杂运动变成在每个坐标轴上的简单伸缩。特征值变成谱，特征向量变成谱测度，对角化变成乘法算子表示。

## 形式化表述

设 $H$ 是Hilbert空间，$T \in B(H)$ 是正规算子（$TT^* = T^*T$）。

**谱定理（乘法算子形式）**：存在测度空间 $(X, \mu)$ 和酉算子
$$U: H \to L^2(X, \mu)$$
使得 $UTU^* = M_\phi$（乘以某个 $L^\infty$ 函数 $\phi$）。

**谱定理（谱测度形式）**：存在唯一的投影值测度 $E$ 使得
$$T = \int_{\sigma(T)} \lambda dE(\lambda)$$

**函数演算**：对 $f \in L^\infty(\sigma(T))$，可定义 $f(T) = \int f(\lambda) dE(\lambda)$。

## 证明思路

1. **循环子空间**：分解 $H$ 为循环子空间的直和
2. **Gelfand变换**：交换C*-代数的表示
3. **Riesz表示**：从线性泛函构造测度
4. **投影值测度**：建立谱测度的性质
5. **乘法算子**：实现具体的表示形式

## 示例

### 示例 1：紧自伴算子

**问题**：设 $T$ 是紧自伴算子，描述其谱定理。

**解答**：

紧自伴算子有纯点谱：
$$T = \sum_{n} \lambda_n \langle \cdot, e_n \rangle e_n$$

其中 $\lambda_n \to 0$，$\{e_n\}$ 是正交规范基。

这是有限维谱定理的直接推广。

### 示例 2：位置算子

**问题**：描述 $L^2(\mathbb{R})$ 上的位置算子 $Q: f(x) \mapsto xf(x)$。

**解答**：

$Q$ 是无界自伴算子（在适当定义域上）。

谱是全体实数 $\sigma(Q) = \mathbb{R}$。

谱测度是 $E(\Delta)f = \chi_\Delta \cdot f$（乘以区间示性函数）。

## 应用

- **量子力学**：可观测量的谱理论
- **遍历理论**：Koopman算子的谱分析
- **调和分析**：Fourier变换的算子解释
- **偏微分方程**：自伴扩张和谱渐近
- **控制理论**：系统的模态分析

## 相关概念

- [C*-代数](./c-star-algebra.md)：谱定理的代数框架
- [von Neumann代数](./von-neumann-algebra.md)：无界算子的谱理论
- [谱测度](./spectral-measure.md)：谱定理的核心工具
- [正规算子](./normal-operator.md)：谱定理的适用对象
- [函数演算](./functional-calculus.md)：谱定理的应用

## 参考

### 教材

- Reed, M. & Simon, B. Methods of Modern Mathematical Physics I: Functional Analysis. Academic Press, 1980.
- Rudin, W. Functional Analysis. McGraw-Hill, 1991. Chapter 12

### 论文

- von Neumann, J. Mathematische Grundlagen der Quantenmechanik. Springer, 1932.
- Stone, M.H. Linear Transformations in Hilbert Space. AMS, 1932.

### 在线资源

- [Spectral Theorem Wikipedia](https://en.wikipedia.org/wiki/Spectral_theorem)
- [nLab - Spectral Theorem](https://ncatlab.org/nlab/show/spectral+theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
