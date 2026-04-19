---
msc_primary: 00A99
习题编号: ALG-123
学科: 代数
知识点: 表示论-Frobenius互反性
难度: ⭐⭐⭐⭐
预计时间: 25分钟
---

# Frobenius互反性

## 题目

设 $H \subset G$ 是有限群的子群。

**限制**：$\text{Res}_H^G: \text{Rep}(G) \to \text{Rep}(H)$。

**诱导**：$\text{Ind}_H^G: \text{Rep}(H) \to \text{Rep}(G)$，$\text{Ind}_H^G(W) = k[G] \otimes_{k[H]} W$。

(a) 证明Frobenius互反性：对 $V \in \text{Rep}(G)$，$W \in \text{Rep}(H)$：
$$\text{Hom}_G(\text{Ind}_H^G W, V) \cong \text{Hom}_H(W, \text{Res}_H^G V)$$

(b) 计算诱导表示的特征标公式。

(c) 计算 $\text{Ind}_{\langle(12)\rangle}^{S_3}(\text{triv})$ 并分解为不可约表示。

## 解答

### (a) Frobenius互反性

**证明：**

**映射构造**：

给定 $\varphi: W \to \text{Res}_H^G V$（$H$-线性）。

定义 $\tilde{\varphi}: k[G] \otimes_{k[H]} W \to V$：
$$\tilde{\varphi}(g \otimes w) = g \cdot \varphi(w)$$

**良定性**：若 $gh \otimes w = g \otimes hw$：
$$\tilde{\varphi}(gh \otimes w) = gh \cdot \varphi(w) = g \cdot \varphi(hw) = \tilde{\varphi}(g \otimes hw)$$

**逆映射**：

给定 $\psi: \text{Ind}_H^G W \to V$（$G$-线性）。

定义 $\bar{\psi}: W \to V$：$\bar{\psi}(w) = \psi(1 \otimes w)$。

验证 $H$-线性。两者互逆。$\square$

### (b) 诱导特征标公式

**公式**：

$$\chi_{\text{Ind}_H^G W}(g) = \frac{1}{|H|} \sum_{\substack{x \in G \\ x^{-1}gx \in H}} \chi_W(x^{-1}gx)$$

或等价地：
$$= \sum_{\substack{x \in G/H \\ x^{-1}gx \in H}} \chi_W(x^{-1}gx)$$

**证明**：

$\text{Ind}_H^G W = \bigoplus_{x \in G/H} x \otimes W$。

$g$ 作用：$g(x \otimes w) = gx \otimes w = x' \otimes h w$（$gx = x'h$）。

仅当 $x' = x$（即 $x^{-1}gx \in H$）时对迹有贡献。

迹为 $\chi_W(x^{-1}gx)$。$\square$

### (c) $S_3$ 的具体例子

**解答**：

$H = \langle(12)\rangle \cong \mathbb{Z}/2$，$W = \text{triv}$。

$[S_3 : H] = 3$。陪集代表：$1, (123), (132)$。

**特征标**：

- $g = e$：$\chi(g) = 3$。
- $g = (12)$：$(12) \in H$，$1^{-1}(12)1 = (12)$，贡献1。

$(123)^{-1}(12)(123) = (23) \notin H$。

$(132)^{-1}(12)(132) = (13) \notin H$。

$\chi((12)) = 1$。

- $g = (123)$：共轭元不在 $H$（奇偶性）。$\chi((123)) = 0$。

**分解**：

与 $S_3$ 的不可约特征标内积：

- 平凡：$\langle \chi, 1 \rangle = \frac{1}{6}(3 + 3 \cdot 1) = 1$
- 符号：$\langle \chi, \text{sgn} \rangle = \frac{1}{6}(3 - 3) = 0$
- 标准：$\langle \chi, \chi_2 \rangle = \frac{1}{6}(6 + 0) = 1$

因此：$\text{Ind}_H^G(\text{triv}) = \text{triv} \oplus \text{std}$。$\square$

## 证明技巧

1. **张量积的泛性质**：互反性的自然证明
2. **陪集分解**：诱导表示的计算基础
3. **Mackey公式**：诱导-限制的分解

## 常见错误

- ❌ 诱导表示维数计算错误（应为 $[G:H] \cdot \dim W$）
- ❌ 特征标公式中归一化因子遗漏
- ❌ 陪集代表选择的依赖性

## 变式练习

**变式1：** 证明Mackey不可约性判别法。

**变式2：** 计算 $\text{Ind}_{A_3}^{S_3}(\omega)$，$\omega$ 是3次本原单位根表示。
