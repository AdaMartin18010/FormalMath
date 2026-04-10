---
number: "ALG-053"
category: 代数
topic: 表示论入门
difficulty: ⭐⭐⭐
title: 诱导表示与Frobenius互反
keywords: [诱导表示, 限制表示, Frobenius互反, 特征标诱导, 子群表示]
prerequisites: [ALG-052, ALG-051]
source: 经典表示论习题
---

## 题目

设 $G$ 是有限群，$H \leq G$ 是子群。

**(a)** 定义**诱导表示**：若 $W$ 是 $H$ 的表示，定义 $\text{Ind}_H^G W = F[G] \otimes_{F[H]} W$。

证明这是 $G$ 的表示，$\dim(\text{Ind}_H^G W) = [G:H] \cdot \dim(W)$。

**(b)** 定义**诱导特征标**：
$$\text{Ind}_H^G \chi(g) = \frac{1}{|H|} \sum_{\substack{x \in G \\ x^{-1}gx \in H}} \chi(x^{-1}gx)$$

证明这是 $\text{Ind}_H^G W$ 的特征标。

**(c)** （Frobenius互反）设 $\chi$ 是 $H$ 的特征标，$\psi$ 是 $G$ 的特征标，证明：
$$\langle \text{Ind}_H^G \chi, \psi \rangle_G = \langle \chi, \text{Res}_H^G \psi \rangle_H$$

**(d)** 计算 $G = S_3$，$H = \{1, (12)\}$ 的诱导特征标。

## 详细解答

### (a) 诱导表示的定义

**定义：**
$$\text{Ind}_H^G W = F[G] \otimes_{F[H]} W$$

**$G$-模结构：**

$F[G]$ 是 $(F[G], F[H])$-双模，故 $F[G] \otimes_{F[H]} W$ 是左 $F[G]$-模。

**维数计算：**

设 $\{g_1, ..., g_m\}$ 是 $H$ 在 $G$ 中的左陪集代表，$m = [G:H]$。

$F[G] = \bigoplus_{i=1}^m g_i F[H]$ 作为右 $F[H]$-模。

$$\text{Ind}_H^G W = \bigoplus_{i=1}^m g_i \otimes W$$

$\dim = m \cdot \dim(W) = [G:H] \cdot \dim(W)$。

**证毕。**

### (b) 诱导特征标的公式

**证明：**

$g \in G$ 作用在 $g_i \otimes w$ 上：
$$g \cdot (g_i \otimes w) = gg_i \otimes w = g_j \otimes h w$$

其中 $gg_i = g_j h$，$h \in H$。

$g$ 在基 $\{g_i \otimes w_k\}$ 上的矩阵有非零对角元当且仅当 $gg_i = g_i h$ 某 $h \in H$。

即 $g_i^{-1}gg_i \in H$。

迹的计算给出公式。

**证毕。**

### (c) Frobenius互反

**证明：**

$$\langle \text{Ind}_H^G \chi, \psi \rangle_G = \frac{1}{|G|} \sum_{g \in G} \text{Ind}_H^G \chi(g) \overline{\psi(g)}$$

代入诱导特征标公式：

$$= \frac{1}{|G||H|} \sum_{g \in G} \sum_{\substack{x \in G \\ x^{-1}gx \in H}} \chi(x^{-1}gx) \overline{\psi(g)}$$

令 $h = x^{-1}gx$，则 $g = xhx^{-1}$：

$$= \frac{1}{|G||H|} \sum_{x \in G} \sum_{h \in H} \chi(h) \overline{\psi(xhx^{-1})}$$

$\psi$ 是类函数，$\psi(xhx^{-1}) = \psi(h) = \text{Res}_H^G \psi(h)$：

$$= \frac{1}{|H|} \sum_{h \in H} \chi(h) \overline{\text{Res}_H^G \psi(h)} = \langle \chi, \text{Res}_H^G \psi \rangle_H$$

**证毕。**

### (d) $S_3$ 的例子

**$G = S_3 = \{1, (12), (13), (23), (123), (132)\}$**

**$H = \{1, (12)\} \cong \mathbb{Z}_2$**

设 $\chi$ 是 $H$ 的非平凡1维特征标：$\chi(1) = 1$，$\chi((12)) = -1$。

**计算 $\text{Ind}_H^G \chi$：**

| 共轭类 | 1 | (12) | (123) |
|--------|---|------|-------|
| 阶 | 1 | 3 | 2 |

- $g = 1$：$\text{Ind}\chi(1) = [G:H] \cdot \chi(1) = 3 \cdot 1 = 3$
- $g = (12)$：$x^{-1}(12)x \in H$ 对 $x \in \{1, (13), (23)\}$
  $\text{Ind}\chi((12)) = \chi((12)) + \chi((13)(12)(13)) + ... = -1 + 1 + 1 = 1$
- $g = (123)$：无共轭元在 $H$，$\text{Ind}\chi((123)) = 0$

特征标：$(3, 1, 0)$，这是 $S_3$ 的2维不可约特征标加平凡特征标。

## 证明技巧

1. **诱导表示的张量积定义：** 自然但需验证性质
2. **Frobenius互反：** 特征标的计算和变量替换
3. **具体计算：** 确定哪些共轭元落入子群

## 常见错误

| 错误 | 说明 |
|------|------|
| 混淆左右陪集 | 需固定 convention |
| 特征标公式遗漏归一化 | 注意$\frac{1}{|H|}$因子 |
| 共轭元计算错误 | 需逐一验证 |

## 变式练习

**变式1：** 证明Mackey子群定理：诱导和限制的交换性。

**变式2：** 计算$A_4$到$S_4$的诱导表示。

**变式3：** 研究Clifford定理：正规子群上的表示分解。
