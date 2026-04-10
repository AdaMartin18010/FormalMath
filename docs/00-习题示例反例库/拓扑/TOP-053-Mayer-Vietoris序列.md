---
习题编号: TOP-053
学科: 拓扑
知识点: 代数拓扑-Mayer-Vietoris
难度: ⭐⭐⭐
预计时间: 25分钟
---

# Mayer-Vietoris序列

## 题目

设 $X = A \cup B$，$\mathring{A} \cup \mathring{B} = X$（内部覆盖）。

**(a)** 证明存在Mayer-Vietoris序列：
$$\cdots \to H_n(A \cap B) \xrightarrow{(i_*, j_*)} H_n(A) \oplus H_n(B) \xrightarrow{k_* - l_*} H_n(X) \xrightarrow{\partial} H_{n-1}(A \cap B) \to \cdots$$

**(b)** 用Mayer-Vietoris计算 $H_*(S^n)$。

**(c)** 设 $X = X_1 \cup X_2$，$X_1 \cap X_2$ 可缩。证明约化Mayer-Vietoris序列存在并应用。

## 解答

### (a) Mayer-Vietoris序列

**证明**：

考虑链复形：
$$0 \to C_\bullet(A \cap B) \xrightarrow{(i_\#, j_\#)} C_\bullet(A) \oplus C_\bullet(B) \xrightarrow{k_\# - l_\#} C_\bullet(A) + C_\bullet(B) \to 0$$

短正合列。

$C_\bullet(A) + C_\bullet(B) \subset C_\bullet(X)$ 诱导同调同构（由细分引理）。

蛇引理给出长正合列。$\square$

### (b) 计算 $H_*(S^n)$

**证明**：

设 $S^n = U \cup V$，$U, V$ 是去北极/南极的开集。

$U, V \cong \mathbb{R}^n$（可缩）。

$U \cap V \simeq S^{n-1}$。

Mayer-Vietoris：
$$\cdots \to \tilde{H}_k(S^{n-1}) \to 0 \oplus 0 \to \tilde{H}_k(S^n) \to \tilde{H}_{k-1}(S^{n-1}) \to 0 \to \cdots$$

因此 $\tilde{H}_k(S^n) \cong \tilde{H}_{k-1}(S^{n-1})$。

归纳：$\tilde{H}_n(S^n) = \mathbb{Z}$，其他为0。$\square$

### (c) 可缩交

**约化序列**：

若 $A \cap B$ 可缩，$\tilde{H}_*(A \cap B) = 0$。

序列简化为：
$$\cdots \to 0 \to \tilde{H}_n(A) \oplus \tilde{H}_n(B) \to \tilde{H}_n(X) \to 0 \to \cdots$$

因此：
$$\tilde{H}_n(X) \cong \tilde{H}_n(A) \oplus \tilde{H}_n(B)$$

**应用**：

$X = S^n \vee S^n$（楔和）。

每个半球与一点相交（可缩）。

$\tilde{H}_n(S^n \vee S^n) = \mathbb{Z} \oplus \mathbb{Z}$。$\square$

## 证明技巧

1. **内部覆盖**：确保链细分的存在
2. **归纳计算**：从低维向高维推进
3. **可缩简化**：长正合列的截断

## 常见错误

- ❌ 忘记内部覆盖的条件
- ❌ 归纳基底的验证
- ❌ 约化同调与通常同调的混淆

## 变式练习

**变式1：** 计算Torus $T^2$ 的同调。

**变式2：** 计算Klein瓶的同调。
