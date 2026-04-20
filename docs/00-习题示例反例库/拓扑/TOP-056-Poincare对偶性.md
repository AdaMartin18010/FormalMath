---
msc_primary: 00A99
习题编号: TOP-056
学科: 拓扑
知识点: 代数拓扑-Poincare对偶
难度: ⭐⭐⭐⭐⭐
预计时间: 40分钟
---

# Poincaré对偶性

## 题目

设 $M$ 是 $n$ 维闭可定向流形。

**(a)** 证明Poincaré对偶：存在基本类 $[M] \in H_n(M)$ 使得：
$$\frown [M]: H^k(M) \to H_{n-k}(M)$$
是同构。

**(b)** 证明上同调版本：$H^k(M) \cong H^{n-k}(M)^*$。

**(c)** 计算 $H^*(\mathbb{C}P^n)$ 的环结构，用Poincaré对偶验证。

---

## 解答

### (a) Poincaré对偶

**证明概要**：

**基本类**：

$M$ 可定向，局部定向整体相容。

$H_n(M) = \mathbb{Z}$，生成元 $[M]$。

**帽积**：
$\frown: H^k(M) \times H_n(M) \to H_{n-k}(M)$。

**局部验证**：

对 $M = \mathbb{R}^n$，$H^k(\mathbb{R}^n) = 0$（$k>0$），显然。

对 $M = S^n$，直接计算验证。

**Mayer-Vietoris论证**：

用开覆盖归纳，局部对偶性拼成整体。

由五引理，对偶映射是同构。$\square$

**详细展开**：

**基本类的构造**：

取 $M$ 的三角剖分（或光滑结构）。可定向性意味着可以在每个 $n$-单形上选择定向，使得相邻单形在公共面上的诱导定向相反。

将所有定向 $n$-单形求和得到基本链：
$$[M] = \sum_{\sigma} \epsilon(\sigma) \sigma \in C_n(M)$$

其中 $\epsilon(\sigma) = \pm 1$ 是定向。由于可定向性，$\partial[M] = 0$，因此 $[M]$ 定义了一个同调类 $[M] \in H_n(M) \cong \mathbb{Z}$。

**帽积的定义**：

在链水平上，对 $\varphi \in C^k(M)$ 和 $\sigma = [v_0, ..., v_n]$：
$$\varphi \frown \sigma = \varphi([v_0, ..., v_k]) \cdot [v_k, ..., v_n] \in C_{n-k}(M)$$

这诱导了上同调到同调的映射。

**归纳证明（Mayer-Vietoris）**：

设 $M = U \cup V$，其中 $U, V$ 是开集。有Mayer-Vietoris序列：
$$\cdots \to H^k(U \cup V) \to H^k(U) \oplus H^k(V) \to H^k(U \cap V) \to H^{k+1}(U \cup V) \to \cdots$$

假设对 $U, V, U \cap V$ Poincaré对偶成立。通过五引理，对 $U \cup V$ 也成立。

**基本情形**：
- $M = \mathbb{R}^n$：$H^k(\mathbb{R}^n) = 0$（$k > 0$），$H_0(\mathbb{R}^n) = \mathbb{Z}$。对 $k = 0$，$H^0 \to H_n$ 将 $1 \mapsto [M]$，是同构。
- $M = S^n$：直接计算。$H^0(S^n) \cong H_n(S^n) \cong \mathbb{Z}$，$H^n(S^n) \cong H_0(S^n) \cong \mathbb{Z}$，其他为0。

---

### (b) 上同调对偶

**证明**：

由万有系数：
$$H_{n-k}(M) \cong H^{n-k}(M)^* \oplus \text{Ext}(H^{n-k-1}(M), \mathbb{Z})$$

闭流形，无挠（或适当处理）。

$H^k(M) \cong H_{n-k}(M) \cong H^{n-k}(M)^*$。$\square$

**详细解释**：

万有系数定理对同调给出：
$$H_{n-k}(M; \mathbb{Z}) \cong H^{n-k}(M; \mathbb{Z})^* \oplus \text{Ext}^1_\mathbb{Z}(H^{n-k-1}(M; \mathbb{Z}), \mathbb{Z})$$

对紧流形，$H^*(M; \mathbb{Z})$ 是有限生成Abel群，因此：
- 自由部分：$\text{rank } H_{n-k} = \text{rank } H^{n-k}$
- 挠部分：$\text{Ext}(\mathbb{Z}/m, \mathbb{Z}) = \mathbb{Z}/m$，需要仔细处理

**杯积配对**：Poincaré对偶等价于杯积配对的非退化性：
$$H^k(M) \times H^{n-k}(M) \xrightarrow{\smile} H^n(M) \xrightarrow{\langle -, [M] \rangle} \mathbb{Z}$$

$(\alpha, \beta) \mapsto \langle \alpha \smile \beta, [M] \rangle$ 是非退化双线性型。

---

### (c) $\mathbb{C}P^n$ 的计算

**结果**：

$H^*(\mathbb{C}P^n) = \mathbb{Z}[x]/(x^{n+1})$，$|x| = 2$。

**Poincaré对偶验证**：

$\dim \mathbb{C}P^n = 2n$。

对偶配对：$H^{2k} \times H^{2n-2k} \to H^{2n} = \mathbb{Z}$。

$x^k \smile x^{n-k} = x^n$。

生成 $H^{2n}$，配对非退化。$\square$

**详细计算**：

$\mathbb{C}P^n$ 有胞腔分解：
- 一个 $0$-胞腔 $e^0$
- 一个 $2$-胞腔 $e^2$
- 一个 $4$-胞腔 $e^4$
- ...
- 一个 $2n$-胞腔 $e^{2n}$

因此 $H^{2k}(\mathbb{C}P^n) = \mathbb{Z}$（$0 \leq k \leq n$），其他为0。

设 $x \in H^2(\mathbb{C}P^n)$ 是生成元（超平面类的Poincaré对偶）。

**杯积结构**：$x^k \in H^{2k}$ 是生成元。这是因为 $x$ 对应于 $\mathbb{C}P^{n-1} \subset \mathbb{C}P^n$（超平面），而 $x^k$ 对应于 $\mathbb{C}P^{n-k}$（$k$ 个超平面的交）。

**Poincaré对偶验证**：

对 $0 \leq k \leq n$，考虑配对：
$$H^{2k} \times H^{2n-2k} \to H^{2n} = \mathbb{Z}$$
$$(x^k, x^{n-k}) \mapsto x^k \smile x^{n-k} = x^n$$

在 $H^{2n}$ 中，$x^n$ 是基本类的对偶，因此 $\langle x^n, [\mathbb{C}P^n] \rangle = 1$。

配对的矩阵是 $1 \times 1$ 矩阵 $(1)$，显然非退化。$\square$

---

## 证明技巧

1. **基本类的局部构造**：利用可定向性和三角剖分/光滑结构
2. **Mayer-Vietoris归纳**：从局部到整体的系统方法
3. **杯积与帽积的关系**：$\alpha \frown (\beta \frown [M]) = (\alpha \smile \beta) \frown [M]$

## 常见错误

- ❌ 忘记可定向条件：非可定向流形有 $\mathbb{Z}/2$ 系数的 Poincaré 对偶，但 $\mathbb{Z}$ 系数版本失效
- ❌ 边界与闭流形的混淆：Poincaré 对偶仅对闭（紧无边界）流形成立。对有边界流形，需要 Lefschetz 对偶
- ❌ 对偶映射的方向：$H^k \to H_{n-k}$（帽积），不是 $H_{n-k} \to H^k$

## 变式练习

**变式1：** 证明非可定向流形的$\mathbb{Z}/2$对偶。

**提示**：在 $\mathbb{Z}/2$ 系数下，定向的障碍消失。证明对任意 $n$ 维闭流形（不必可定向），$H^k(M; \mathbb{Z}/2) \cong H_{n-k}(M; \mathbb{Z}/2)$。

**变式2：** 计算 $H^*(\mathbb{H}P^n)$。

**提示**：四元数射影空间有类似的胞腔分解，但维数间隔为4。
