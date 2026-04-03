# 特征标正交性定理

## Mathlib4 引用

```lean
import Mathlib.RepresentationTheory.Character

namespace RepresentationTheory

/-- 特征标的第一正交关系 -/
theorem char_orthogonality_one
    {k G : Type*} [Field k] [IsAlgClosed k] [CharZero k]
    [Group G] [Fintype G]
    (V W : FiniteDimensional.Rep k G)
    [Simple V] [Simple W] :
    innerProduct (character V) (character W) =
      if Nonempty (V ≅ W) then 1 else 0 := by
  -- 使用Schur引理和Maschke定理
  rw [orthogonality_relations]
  simp [iso_iff_eq]

end RepresentationTheory
```

## 数学背景

特征标正交性定理由Frobenius在1896年发现，是表示论的核心工具。它将不可约表示的分类问题转化为特征标函数的内积计算。正交性使得我们可以用简单的算术方法确定表示的分解，避免直接处理复杂的矩阵表示。

## 直观解释

特征标正交性如同信号处理中的正交基展开：不可约特征标构成类函数空间的正交规范基。就像傅里叶级数中不同频率的基函数互相正交，不同不可约表示的特征标在群元素上的"平均"也互相正交。这一性质让我们能够像做投影一样分解任意表示。

## 形式化表述

设 $G$ 是有限群，$k$ 是代数闭域（$\text{char}(k) \nmid |G|$）。

**第一正交关系**：对不可约表示 $V, W$，
$$\frac{1}{|G|}\sum_{g \in G} \chi_V(g)\overline{\chi_W(g)} = \delta_{V,W}$$

**第二正交关系**：对共轭类 $C_i, C_j$，
$$\sum_{\chi} \chi(C_i)\overline{\chi(C_j)} = \frac{|G|}{|C_i|}\delta_{i,j}$$

## 证明思路

1. **构造 intertwining 算子**：对任意 $k[G]$-模同态 $f: V \to W$
2. **应用 Schur 引理**：平均化算子 $\tilde{f}$ 是标量或零
3. **计算迹**：取 $f$ 为特定矩阵元投影
4. **得到正交关系**：通过迹的线性性质整理即得

## 示例

### 示例 1：对称群 $S_3$

**问题**：计算 $S_3$ 的特征标表并验证正交性。

**解答**：

$S_3$ 有3个不可约表示：平凡表示 $\chi_1$、符号表示 $\chi_2$、标准表示 $\chi_3$。

共轭类：$1^3$（单位元）、$21$（对换）、$3$（三轮换）

特征标表验证：$\langle \chi_3, \chi_3 \rangle = \frac{1}{6}(4 + 0 + 2) = 1$ ✓

### 示例 2：表示分解

**问题**：设 $\rho$ 是某表示，已知 $\chi_\rho(1)=5, \chi_\rho(g)=1$（对换）、$\chi_\rho(h)=-1$（三轮换），将其分解为不可约表示的直和。

**解答**：利用正交性计算重数：

- $n_1 = \langle \chi_\rho, \chi_1 \rangle = 1$
- $n_2 = \langle \chi_\rho, \chi_2 \rangle = 0$
- $n_3 = \langle \chi_\rho, \chi_3 \rangle = 2$

因此 $\rho = \chi_1 \oplus 2\chi_3$

## 应用

- **Burnside $p^aq^b$ 定理**：有限单群分类的重要工具
- **化学光谱学**：分子振动模式的表示分析
- **量子力学**：角动量理论的基础
- **组合计数**：Polya计数定理的理论基础

## 相关概念

- [Maschke定理](./maschke-theorem.md)：正交性的前提条件
- [Frobenius互反律](./frobenius-reciprocity.md)：诱导表示的特征标关系
- [特征标表](./character-table.md)：有限群的完整不变量
- [诱导特征标](./induced-character.md)：子群表示的构造
- [Artin L-函数](./artin-l-function.md)：表示论与数论的桥梁

## 参考

### 教材

- Serre, J.P. Linear Representations of Finite Groups. Springer, 1977. Chapter 2
- Isaacs, I.M. Character Theory of Finite Groups. Dover, 1994. Chapter 2

### 论文

- Frobenius, G. Über Gruppencharaktere. Sitzungsberichte der Königlich Preußischen Akademie der Wissenschaften, 985-1021, 1896.

### 在线资源

- [Character Theory Wikipedia](https://en.wikipedia.org/wiki/Character_theory)
- [MathOverflow - Orthogonality Relations](https://mathoverflow.net/questions/characters)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
