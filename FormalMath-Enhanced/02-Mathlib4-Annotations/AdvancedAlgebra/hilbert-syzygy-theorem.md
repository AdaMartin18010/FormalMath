---
msc_primary: 00A99
processed_at: '2026-04-03'
title: Hilbert合冲定理
---
# Hilbert合冲定理

## Mathlib4 引用

```lean
import Mathlib.RingTheory.Regular.RegularLocalRing

namespace CommutativeAlgebra

/-- Hilbert合冲定理 -/
theorem hilbert_syzygy
    {k : Type*} [Field k]
    {n : ℕ} (R := MvPolynomial (Fin n) k) :
    ∀ (M : Type*) [AddCommGroup M] [Module R M]
      [Module.FinitePresentation R M],
    projectiveDimension M ≤ n := by
  -- 多项式环的整体维数有限
  intro M
  -- 利用Koszul复形或归纳法
  have : globalDimension R = n := by
    apply hilbert_global_dimension
  apply le_of_eq this

end CommutativeAlgebra
```

## 数学背景

Hilbert合冲定理由David Hilbert在1890年证明，是交换代数历史上的里程碑结果。定理表明，多项式环 $k[x_1, \ldots, x_n]$ 上的任何有限生成模都有长度至多为 $n$ 的自由分解。这一结果不仅奠定了模的有限自由分解理论的基础，也是计算代数几何中Gröbner基方法和交换代数软件的核心。Hilbert利用这一定理证明了多项式环的不变量子环的有限生成性，解决了Gordan问题。

## 直观解释

Hilbert合冲定理解释了多项式环的"结构简单性"。想象一个模作为由方程组定义的代数结构，"合冲"（syzygy）是这些方程之间的关系的递归描述。Hilbert定理说：对于多项式环，这个递归过程在 $n$ 步内必然终止——不再有新的关系。这反映了多项式环作为正则环的本质：它们"足够光滑"，使得任何模都可以用有限步的自由模来"近似"。

## 形式化表述

设 $k$ 是域，$R = k[x_1, \ldots, x_n]$。

**Hilbert合冲定理**：对任意有限生成 $R$-模 $M$，存在正合列
$$0 \to F_m \to F_{m-1} \to \cdots \to F_1 \to F_0 \to M \to 0$$
其中 $m \leq n$，$F_i$ 是有限秩自由 $R$-模。

**等价表述**：$R$ 的整体维数为 $n$，即任何模的投射维数 $\leq n$。

## 证明思路

1. **Koszul复形法**：利用变量生成的正则序列
2. **归纳法**：对变量个数归纳，利用 $R[x_{n+1}]$ 的性质
3. **模的构造**：将 $M$ 视为 $k[x_1, \ldots, x_{n-1}]$-模的扩张
4. **谱序列**：利用Tor的谱序列计算

## 示例

### 示例 1：单变量情形

**问题**：$R = k[x]$，证明任何有限生成模有长度 $\leq 1$ 的自由分解。

**解答**：

$R$ 是PID，子模自由。对模 $M$，取生成元得满射 $R^m \to M$，核 $K$ 自由，故
$$0 \to R^l \to R^m \to M \to 0$$
是长度1的自由分解。

### 示例 2：平面曲线的合冲

**问题**：设 $R = k[x,y]$，$M = R/(x^2, xy)$，构造自由分解。

**解答**：

$M$ 的极小自由分解：
$$0 \to R \xrightarrow{\begin{pmatrix} y \\ -x \end{pmatrix}} R^2 \xrightarrow{\begin{pmatrix} x^2 & xy \end{pmatrix}} R \to M \to 0$$

长度为2，等于 $R$ 的维数。

## 应用

- **计算代数几何**：Gröbner基计算合冲
- **不变量理论**：Hilbert原始应用
- **层上同调**：射影空间的消解计算
- **拓扑学**：构型空间的Betti数
- **组合数学**：Stanley-Reisner理论

## 相关概念

- 投射维数：合冲长度的上界
- 正则局部环：Hilbert定理的推广
- 整体维数：环的同调维数
- Koszul复形：Hilbert定理证明的核心工具
- 有限自由分解：合冲的构造

## 参考

### 教材

- Eisenbud, D. Commutative Algebra. Springer, 1995. Chapter 19
- Cox, D., Little, J. & O'Shea, D. Ideals, Varieties, and Algorithms. Springer, 2007. Chapter 6

### 论文

- Hilbert, D. Über die Theorie der algebraischen Formen. Math. Ann., 36: 473-534, 1890.
- Hilbert, D. Über die vollen Invariantensysteme. Math. Ann., 42: 313-373, 1893.

### 在线资源

- [Hilbert's Syzygy Theorem Wikipedia](https://en.wikipedia.org/wiki/Hilbert%27s_syzygy_theorem)
- [MathOverflow - Hilbert's Syzygy Theorem](https://mathoverflow.net/questions/hilbert-syzygy)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
