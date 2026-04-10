---
习题编号: TOP-054
学科: 拓扑
知识点: 代数拓扑-Künneth公式
难度: ⭐⭐⭐⭐
预计时间: 30分钟
---

# Künneth公式

## 题目

设 $X, Y$ 是拓扑空间。

**(a)** 证明Eilenberg-Zilber定理：$C_\bullet(X \times Y) \simeq C_\bullet(X) \otimes C_\bullet(Y)$（链等价）。

**(b)** 证明Künneth公式：存在短正合列：
$$0 \to \bigoplus_{i+j=n} H_i(X) \otimes H_j(Y) \to H_n(X \times Y) \to \bigoplus_{i+j=n-1} \text{Tor}(H_i(X), H_j(Y)) \to 0$$

**(c)** 应用：计算 $H_*(T^2) = H_*(S^1 \times S^1)$。

## 解答

### (a) Eilenberg-Zilber定理

**证明概要**：

**Alexander-Whitney映射**：

$AW: C_\bullet(X \times Y) \to C_\bullet(X) \otimes C_\bullet(Y)$。

对 $\sigma: \Delta^n \to X \times Y$，$\sigma = (\sigma_X, \sigma_Y)$。

$$AW(\sigma) = \sum_{i=0}^n \sigma_X|_{[v_0,\ldots,v_i]} \otimes \sigma_Y|_{[v_i,\ldots,v_n]}$$

**Eilenberg-Zilber映射**：

$EZ: C_\bullet(X) \otimes C_\bullet(Y) \to C_\bullet(X \times Y)$。

用洗牌积构造。

**同伦逆**：$AW \circ EZ = \text{id}$，$EZ \circ AW \simeq \text{id}$。$\square$

### (b) Künneth公式

**证明**：

由(a)，$H_n(X \times Y) = H_n(C_\bullet(X) \otimes C_\bullet(Y))$。

**代数Künneth定理**：

对链复形 $C, D$，若 $C$ 自由，则：
$$0 \to \bigoplus_{i+j=n} H_i(C) \otimes H_j(D) \to H_n(C \otimes D) \to \bigoplus_{i+j=n-1} \text{Tor}(H_i(C), H_j(D)) \to 0$$

奇异链复形自由（由构造）。$\square$

### (c) Torus的同调

**计算**：

$H_0(S^1) = \mathbb{Z}$，$H_1(S^1) = \mathbb{Z}$。

**$n=0$**：
$H_0(T^2) = \mathbb{Z} \otimes \mathbb{Z} = \mathbb{Z}$

**$n=1$**：
$H_1(T^2) = (\mathbb{Z} \otimes \mathbb{Z}) \oplus (\mathbb{Z} \otimes \mathbb{Z}) = \mathbb{Z} \oplus \mathbb{Z}$

**$n=2$**：
$H_2(T^2) = \mathbb{Z} \otimes \mathbb{Z} = \mathbb{Z}$

Tor项为0（自由群）。$\square$

## 证明技巧

1. **Alexander-Whitney**：几何到代数的映射
2. **洗牌积**：代数到几何的对称构造
3. **Tor的计算**：挠系数的处理

## 常见错误

- ❌ 忘记自由性条件
- ❌ Tor项的维数计算
- ❌ 分裂的非自然性

## 变式练习

**变式1：** 计算 $H_*(S^m \times S^n)$。

**变式2：** 计算 $H_*(\mathbb{R}P^2 \times \mathbb{R}P^2)$。
