---
习题编号: ANA-123
学科: 实分析
知识点: 算子理论-紧算子与Fredholm理论
难度: ⭐⭐⭐⭐⭐
预计时间: 50分钟
---

# 紧算子与Fredholm理论

## 题目

设 $X, Y$ 是Banach空间。$T \in \mathcal{B}(X,Y)$ 称为**紧算子**，若 $T(B_X)$ 是相对紧集，其中 $B_X$ 是 $X$ 的单位球。

**(a)** 证明紧算子理想性质：紧算子全体 $\mathcal{K}(X)$ 是 $\mathcal{B}(X)$ 的闭双边理想。

**(b)** 证明Riesz-Fredholm定理：设 $T \in \mathcal{K}(X)$，则
- $\dim \ker(I - T) < \infty$
- $\text{ran}(I - T)$ 是闭的
- $\text{codim } \text{ran}(I - T) = \dim \ker(I - T)$

**(c)** 证明紧算子的谱 $\sigma(T)$ 是可数集，且0是唯一可能的聚点。

## 解答

### (a) 紧算子理想

**证明：**

**子空间**：若 $S, T$ 紧，则 $(S+T)(B_X) \subset S(B_X) + T(B_X)$ 是相对紧集（紧集之和紧）。

**理想性质**：
- 左乘：$AT(B_X) = A(T(B_X))$，紧集的连续像紧
- 右乘：$TA(B_X) \subset T(\|A\| B_X) = \|A\| T(B_X)$ 相对紧

**闭性**：设 $T_n \to T$，$T_n$ 紧。证 $T$ 紧。

对任意 $\varepsilon > 0$，$T_n(B_X)$ 可被有限 $\varepsilon$-网覆盖。

$T(B_X)$ 可被 $T_n(B_X)$ 的有限 $2\varepsilon$-网覆盖。$\square$

### (b) Riesz-Fredholm定理

**证明概要：**

**Step 1**：$\ker(I-T)$ 有限维。

在 $\ker(I-T)$ 上，$T = I$，故单位球紧，因此有限维。

**Step 2**：值域闭性。

设 $(I-T)x_n \to y$。需证 $y \in \text{ran}(I-T)$。

若 $\{x_n\}$ 无界，取 $\|x_n\| \to \infty$。令 $z_n = x_n/\|x_n\|$。

$(I-T)z_n \to 0$，且 $\{Tz_n\}$ 有收敛子列，故 $\{z_n\}$ 有收敛子列 $z \in \ker(I-T)$，$\|z\|=1$。

但 $z_n \perp \ker(I-T)$ 可选取，矛盾。

因此 $\{x_n\}$ 有界，有子列 $Tx_n \to w$，则 $x_n \to y + w$，故 $y = (I-T)(y+w)$。

**Step 3**：余维数等于核维数。

用对偶性：$\text{ran}(I-T)^\perp = \ker(I-T^*)$。

同理对 $T^*$ 应用。$\square$

### (c) 紧算子的谱

**证明：**

设 $\lambda \neq 0$，证 $\lambda$ 是特征值或属于预解集。

考虑 $\lambda^{-1}T$，紧算子。

若 $\lambda \in \sigma(T)$，则 $I - \lambda^{-1}T$ 不可逆。

由(b)，要么 $\ker(I - \lambda^{-1}T) \neq 0$（特征值），要么值域不闭（但(b)说值域闭），故必是特征值。

**可数性**：对 $n \in \mathbb{N}$，$\sigma(T) \cap \{\lambda : |\lambda| \geq 1/n\}$ 有限。

否则有无穷多个特征值 $\lambda_k$，$|\lambda_k| \geq 1/n$，对应特征向量 $e_k$。

$E_k = \text{span}\{e_1, \ldots, e_k\}$，取 $x_k \in E_k \setminus E_{k-1}$，$\|x_k\| = 1$，$\text{dist}(x_k, E_{k-1}) \geq 1/2$。

则 $\{Tx_k/\lambda_k\}$ 无Cauchy子列，与紧性矛盾。

因此 $\sigma(T)$ 可数，0是唯一可能的聚点。$\square$

## 证明技巧

1. **紧性判据**：有限覆盖/序列紧等价
2. **Riesz引理**：有限维子空间的距离估计
3. **谱点分类**：紧算子谱的离散性

## 常见错误

- ❌ 紧算子值域闭性的误解
- ❌ Fredholm指标计算中忽略余维数
- ❌ 紧算子谱聚点性质的证明漏洞

## 变式练习

**变式1：** 证明Hilbert-Schmidt算子是紧算子。

**变式2：** 计算 $L^2([0,1])$ 上积分算子 $Tf(x) = \int_0^x f(t)dt$ 的谱。
