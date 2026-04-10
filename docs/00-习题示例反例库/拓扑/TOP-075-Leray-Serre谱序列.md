---
习题编号: TOP-075
学科: 拓扑
知识点: 同伦论-Leray-Serre谱序列
难度: ⭐⭐⭐⭐⭐
预计时间: 55分钟
---

# Leray-Serre谱序列

## 题目

设 $p: E \to B$ 是纤维化，纤维 $F$。

**(a)** 陈述Leray-Serre谱序列：若 $B$ 单连通，则
$$E^2_{p,q} = H_p(B; H_q(F)) \Rightarrow H_{p+q}(E)$$

**(b)** 用Serre谱序列计算 $H^*(\Omega S^n)$（回路空间）。

**(c)** 计算纤维化 $S^1 \to S^{2n+1} \to \mathbb{C}P^n$ 的谱序列。

## 解答

### (a) Leray-Serre谱序列

**陈述：**

对纤维化 $F \to E \to B$，$B$ 道路连通。

若 $\pi_1(B)$ 作用在 $H_*(F)$ 平凡，则
$$E^2_{p,q} = H_p(B; H_q(F))$$
收敛到 $H_{p+q}(E)$。

微分 $d^r: E^r_{p,q} \to E^r_{p-r, q+r-1}$。

### (b) 球面回路空间

**计算：**

纤维化 $\Omega S^n \to PS^n \to S^n$，$PS^n$ 可缩。

$E^2_{p,q} = H_p(S^n; H_q(\Omega S^n))$。

$p = 0, n$ 非零。

$E^2$ 页只有两行，$d^n$ 连接：
$$d^n: E^n_{n, q} \to E^n_{0, q+n-1}$$

由收敛到0，$H_q(\Omega S^n) \cong H_{q+n-1}(\Omega S^n)$。

归纳得：$H_k(\Omega S^n) = \mathbb{Z}$ 对 $k \equiv 0 \pmod{n-1}$，否则0（当 $n$ 偶）。

### (c) Hopf纤维化谱序列

**计算：**

$E^2_{p,q} = H_p(\mathbb{C}P^n; H_q(S^1))$。

$q = 0, 1$。

$d^2: E^2_{p, 1} \to E^2_{p-2, 2} = 0$。

故 $E^2 = E^\infty$。

$H_k(S^{2n+1})$ 滤过确定。
