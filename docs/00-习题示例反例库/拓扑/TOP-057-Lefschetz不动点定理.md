---
msc_primary: 00A99
习题编号: TOP-057
学科: 拓扑
知识点: 代数拓扑-Lefschetz不动点
难度: ⭐⭐⭐⭐
预计时间: 35分钟
---

# Lefschetz不动点定理

## 题目

设 $X$ 是有限CW复形，$f: X \to X$ 是连续映射。

**(a) Lefschetz数**：
$$\Lambda(f) = \sum_{k \geq 0} (-1)^k \text{tr}(f_*: H_k(X; \mathbb{Q}) \to H_k(X; \mathbb{Q}))$$

证明若 $f$ 无不动点，则 $\Lambda(f) = 0$。

**(b)** 设 $f \simeq \text{id}_X$，计算 $\Lambda(f)$。

**(c) 应用**：证明Brouwer不动点定理。

---

## 解答

### (a) Lefschetz不动点定理

**证明概要**：

**胞腔逼近**：$f$ 同伦于胞腔映射。

**Lefschetz数的局部计算**：

若 $f$ 无不动点，可构造链映射的迹为零。

用Hopf迹公式：
$$\Lambda(f) = \sum_{\sigma} (-1)^{\dim \sigma} \text{tr}(f_\#: \mathbb{Z}\sigma \to \mathbb{Z}\sigma)$$

无不动点，迹为零。

因此 $\Lambda(f) = 0$。$\square$

**详细展开**：

**步骤1：胞腔逼近**

有限CW复形之间的连续映射总可以同伦于一个**胞腔映射**（即把 $n$-骨架映到 $n$-骨架的映射）。由于Lefschetz数是同伦不变量（同伦的映射诱导相同的同调同态），不妨设 $f$ 是胞腔映射。

**步骤2：链水平上的迹**

胞腔映射 $f$ 诱导链映射 $f_\#: C_\bullet(X) \to C_\bullet(X)$。由**Hopf迹公式**：
$$\sum_k (-1)^k \text{tr}(f_\#: C_k \to C_k) = \sum_k (-1)^k \text{tr}(f_*: H_k \to H_k)$$

右边就是 $\Lambda(f)$。

**步骤3：无不动点蕴含迹为零**

设 $f$ 无不动点。对CW复形，可以利用**Simplicial Approximation**将 $f$ 进一步调整为**无不动点的单纯映射**（可能需要细分）。

对无不动点的单纯映射，每个单形 $\sigma$ 都被送到不同的单形 $f(\sigma) \neq \sigma$。因此在链水平上：
$$f_\#(\sigma) = \sum_{\tau \neq \sigma} a_\tau \tau$$

即 $f_\#$ 在对角基元上的分量为零，故 $\text{tr}(f_\#: C_k \to C_k) = 0$。

**步骤4：综合**

由Hopf迹公式：
$$\Lambda(f) = \sum_k (-1)^k \cdot 0 = 0$$

**逆否命题**：若 $\Lambda(f) \neq 0$，则 $f$ 必有不动点。$\square$

---

### (b) 同伦于恒等

**计算**：

$f \simeq \text{id}$，则 $f_* = \text{id}$ 于同调。

$$\Lambda(f) = \sum_k (-1)^k \dim H_k(X; \mathbb{Q}) = \chi(X)$$

Euler示性数。

**推论**：若 $\chi(X) \neq 0$，则任何与恒等同伦的映射有不动点。$\square$

**详细解释**：

若 $f \simeq \text{id}_X$，则对所有 $k$，$f_* = \text{id}: H_k(X; \mathbb{Q}) \to H_k(X; \mathbb{Q})$。

恒等映射的迹等于空间的维数：
$$\text{tr}(\text{id}: H_k \to H_k) = \dim_\mathbb{Q} H_k(X; \mathbb{Q})$$

因此：
$$\Lambda(f) = \sum_k (-1)^k \dim H_k(X; \mathbb{Q}) = \chi(X)$$

**应用**：对紧流形 $M$，若 $\chi(M) \neq 0$，则任何与恒等同伦的自映射都有不动点。

经典例子：
- $S^{2n}$：$\chi = 2 \neq 0$，任何度数为1的映射有不动点
- $S^{2n+1}$：$\chi = 0$，存在无不动点的映射（如对跖映射 $x \mapsto -x$）
- $\mathbb{C}P^n$：$\chi = n+1 \neq 0$
- $T^n$（$n$-维环面）：$\chi = 0$（$n \geq 1$）

---

### (c) Brouwer不动点定理

**证明**：

$D^n$ 是有限CW复形，$\chi(D^n) = 1 \neq 0$。

设 $f: D^n \to D^n$ 连续。

若 $f$ 无不动点，考虑边界限制。

或用：$D^n$ 可缩，$H_k(D^n) = 0$（$k>0$）。

$\Lambda(f) = \text{tr}(f_*: H_0 \to H_0) = 1 \neq 0$。

因此 $f$ 有不动点。$\square$

**详细展开**：

**方法1：利用可缩性**

$n$-维闭球 $D^n$ 是可缩空间，因此：
- $H_0(D^n; \mathbb{Q}) = \mathbb{Q}$
- $H_k(D^n; \mathbb{Q}) = 0$（$k > 0$）

对任意连续映射 $f: D^n \to D^n$，诱导的同调同态：
- $f_*: H_0 \to H_0$ 是恒等映射（因 $H_0$ 由连通分支的基点生成）

因此：
$$\Lambda(f) = \text{tr}(f_*: H_0 \to H_0) = 1 \neq 0$$

由Lefschetz不动点定理，$f$ 必有不动点。

**方法2：反证法（经典证明）**

假设 $f: D^n \to D^n$ 无不动点。定义 $r: D^n \to S^{n-1}$：

对 $x \in D^n$，$r(x)$ 是射线 $\overrightarrow{xf(x)}$ 与边界 $S^{n-1}$ 的交点。

$r$ 是连续收缩映射（retraction），即 $r|_{S^{n-1}} = \text{id}$。

但代数拓扑中已证明：不存在 $D^n$ 到 $S^{n-1}$ 的收缩映射（因为 $H_{n-1}(S^{n-1}) = \mathbb{Z}$ 而 $H_{n-1}(D^n) = 0$，收缩诱导的矛盾）。

因此 $f$ 必有不动点。$\square$

---

## 证明技巧

1. **Hopf迹公式**：同调与链复形的联系。关键洞察：在链水平上可能更容易计算，但同调上的迹与链上的迹相同（由长正合序列的Euler性质）。

2. **胞腔逼近**：将一般连续映射替换为更容易处理的胞腔映射，不改变Lefschetz数。

3. **Euler示性数**：$\chi(X)$ 是Lefschetz数的特殊情况（$f = \text{id}$），是拓扑学中最基本的全局不变量之一。

## 常见错误

- ❌ 忘记有理系数的必要性：在挠系数存在时，$\text{tr}$ 在有理系数下定义更简洁。实际上Lefschetz数也可以用整数系数定义，但需要更谨慎处理挠部分。
- ❌ 不动点与周期点的混淆：Lefschetz定理给出不动点存在的充分条件，但不提供周期点（$f^n(x) = x$）的信息。
- ❌ 反例构造中的边界条件：在应用Lefschetz定理时，必须确认空间是有限CW复形（或更一般的紧ENRs）。

## 变式练习

**变式1：** 证明紧Lie群的Euler示性数为0（若非平凡）。

**提示**：非平凡紧Lie群 $G$ 存在非零左不变向量场，即存在无不动点的自映射同伦于恒等。由Lefschetz定理，$\chi(G) = 0$。

**变式2：** 计算Torus上映射的Lefschetz数。

**提示**：$T^n = (S^1)^n$，$H_k(T^n; \mathbb{Q}) = \mathbb{Q}^{\binom{n}{k}}$。设 $f: T^n \to T^n$ 由矩阵 $A \in GL(n, \mathbb{Z})$ 诱导，则 $\Lambda(f) = \det(I - A)$。
