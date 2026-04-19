---
msc_primary: 00A99
习题编号: ALG-138
学科: 代数
知识点: 同调代数-Tor函子与平坦模
难度: ⭐⭐⭐
预计时间: 30分钟
---

# Tor函子与平坦模

## 题目

设 $R$ 是环，$A$ 是右 $R$-模，$B$ 是左 $R$-模。定义 $\text{Tor}_n^R(A, B) = (L_n (A \otimes_R -))(B)$。

**(a)** 证明 $\text{Tor}_0^R(A, B) \cong A \otimes_R B$，并证明 $\text{Tor}_n^R(A, B) = 0$ 对所有 $n \geq 1$ 当 $B$ 平坦时。

**(b)** 证明Tor的平衡性：可用 $A$ 的投射分解或 $B$ 的投射分解计算，结果相同。

**(c)** 证明：$B$ 平坦当且仅当对所有有限生成理想 $I \subset R$，$\text{Tor}_1^R(R/I, B) = 0$。

## 解答

### (a) Tor的初值与平坦模

**证明：**

$\text{Tor}_n(A, B) = H_n(A \otimes_R Q_\bullet)$，$Q_\bullet \to B$ 是投射分解。

$n=0$：
$$\text{Tor}_0(A, B) = \text{coker}(A \otimes Q_1 \to A \otimes Q_0) = A \otimes B$$

**$B$ 平坦**：

$-\otimes B$ 正合，故对任何投射分解 $Q_\bullet \to B$：
$$\cdots \to A \otimes Q_1 \to A \otimes Q_0 \to A \otimes B \to 0$$

是正合的（作为复形，$H_n = 0$ 对 $n \geq 1$）。

因此 $\text{Tor}_n(A, B) = 0$ 对 $n \geq 1$。$\square$

### (b) Tor的平衡性

**证明概要：**

设 $P_\bullet \to A$ 和 $Q_\bullet \to B$ 是投射分解。

构造**双复形** $C_{p,q} = P_p \otimes Q_q$。

**两个谱序列**：

1. 先对 $q$ 取同调：$H'_q(P_p \otimes Q_\bullet) = P_p \otimes H_q(Q_\bullet) = \begin{cases} P_p \otimes B & q = 0 \\ 0 & q > 0 \end{cases}$

   $E^2_{p,q} = H_p(P_\bullet \otimes B) = \text{Tor}_p(A, B)$（用 $P$ 计算）

2. 先对 $p$ 取同调：类似得 $E^2_{p,q} = \text{Tor}_q(A, B)$（用 $Q$ 计算）

两个谱序列都收敛到 $H_{p+q}(\text{Tot}(C_{\bullet, \bullet}))$。

因此两种计算方式同构。$\square$

### (c) 平坦性判别

**证明：**

**($\Rightarrow$)**：$B$ 平坦 $\Rightarrow$ $\text{Tor}_1(R/I, B) = 0$ 显然。

**($\Leftarrow$)**：设对所有有限生成理想 $I$，$\text{Tor}_1(R/I, B) = 0$。

对短正合列 $0 \to I \to R \to R/I \to 0$，有：
$$0 = \text{Tor}_1(R/I, B) \to I \otimes B \to R \otimes B = B$$

故 $I \otimes B \to IB$ 是单射。

由平坦模的判别法（理想判别法），$B$ 平坦。$\square$
