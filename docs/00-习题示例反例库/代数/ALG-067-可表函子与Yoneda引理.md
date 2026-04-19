---
exercise_id: ALG-067
title: Yoneda引理与可表函子
msc_primary: 00A99
difficulty: ⭐⭐⭐
topics: [Yoneda引理, 可表函子, 自然同构, 表示]
created: 2026-04-10
---

## 题目

设 $\mathcal{C}$ 是局部小范畴（态射形成集合），$F: \mathcal{C}^{op} \to \mathbf{Set}$ 是反变函子。

(1) 叙述并证明 **Yoneda引理**：对任意 $X \in \mathcal{C}$，存在自然同构：

$$\operatorname{Nat}(h_X, F) \cong F(X)$$

其中 $h_X = \operatorname{Hom}_{\mathcal{C}}(-, X)$。

(2) 定义**可表函子**并证明表示在同构意义下唯一；

(3) 应用：证明群 $G$ 的表示与 $G$-集的结构等价。

## 详细解答

### (1) Yoneda引理

**构造映射**：

$\Phi: \operatorname{Nat}(h_X, F) \to F(X)$，$\Phi(\alpha) = \alpha_X(\operatorname{id}_X)$。

$\Psi: F(X) \to \operatorname{Nat}(h_X, F)$，对 $u \in F(X)$，定义自然变换 $\Psi(u)$：

$$\Psi(u)_Y: h_X(Y) = \operatorname{Hom}(Y, X) \to F(Y)，\quad f \mapsto F(f)(u)$$

**验证自然性**：需证对 $g: Z \to Y$：

$$\begin{array}{ccc}
\operatorname{Hom}(Y, X) & \xrightarrow{\Psi(u)_Y} & F(Y) \\
\downarrow{g^*} & & \downarrow{F(g)} \\
\operatorname{Hom}(Z, X) & \xrightarrow{\Psi(u)_Z} & F(Z)
\end{array}$$

交换。即 $F(g)(F(f)(u)) = F(f \circ g)(u)$，由 $F$ 反变得证。

**互逆验证**：

$\Phi(\Psi(u)) = \Psi(u)_X(\operatorname{id}_X) = F(\operatorname{id}_X)(u) = u$。

对 $\alpha: h_X \to F$，$\Psi(\Phi(\alpha))_Y(f) = F(f)(\alpha_X(\operatorname{id}_X)) = \alpha_Y(f)$（由自然性）。

### (2) 可表函子与唯一性

**定义**：函子 $F$ **可表**，若存在对象 $X$ 和自然同构 $h_X \cong F$。

**唯一性**：若 $h_X \cong F \cong h_Y$，则 $h_X \cong h_Y$。

由Yoneda：$\operatorname{Nat}(h_X, h_Y) \cong h_Y(X) = \operatorname{Hom}(X, Y)$。

自然同构对应同构态射，故 $X \cong Y$。

### (3) 群的表示

群 $G$ 可视为单对象范畴 $\mathcal{B}G$（态射是群元，复合是乘法）。

反变函子 $F: \mathcal{B}G^{op} \to \mathbf{Set}$ 即 $G$-集：集合 $S = F(*)$，群作用 $g \cdot s = F(g)(s)$。

可表函子对应：$h_* = \operatorname{Hom}(-, *)$ 在 $\mathcal{B}G$ 上是 $G$ 本身（左正则作用）。

Yoneda给出：$G$-集映射 $G \to S$ 与 $S$ 的元素一一对应（$\operatorname{Hom}_G(G, S) \cong S$）。

## 证明技巧

1. **计算导向**：Yoneda的证明是计算性的，直接构造互逆映射
2. **自然性验证**：检查所有层次的交换性
3. **表示唯一**：利用Yoneda的同构传递

## 常见错误

| 错误类型 | 错误表现 | 正确做法 |
|---------|---------|---------|
| 协变反变 | Yoneda的变体搞混 | 注意函子是协变还是反变 |
| 自然变换方向 | $h_X \to F$ vs $F \to h_X$ | 明确自然变换的方向 |
| 表示对象 | 忽视表示包含同构 | 不只是对象，还包括自然同构 |

## 变式练习

**变式1（难度⭐⭐⭐）**：证明Yoneda嵌入 $y: \mathcal{C} \to [\mathcal{C}^{op}, \mathbf{Set}]$ 是完全忠实的。

**变式2（难度⭐⭐⭐⭐）**：用Yoneda证明极限的唯一性。

**变式3（难度⭐⭐⭐⭐）**：讨论密度定理（Density Theorem）。
