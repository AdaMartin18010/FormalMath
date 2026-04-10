---
习题编号: ANA-138
学科: 实分析
知识点: 实分析-Radon-Nikodym定理
难度: ⭐⭐⭐⭐
预计时间: 35分钟
---

# Radon-Nikodym定理应用

## 题目

**(a)** 证明Radon-Nikodym定理：若 $\nu \ll \mu$（$\sigma$-有限），则存在唯一（a.e.）可测 $f$ 使
$$\nu(E) = \int_E f d\mu$$
记 $f = \frac{d\nu}{d\mu}$。

**(b)** 证明链式法则：若 $\nu \ll \mu \ll \lambda$，则
$$\frac{d\nu}{d\lambda} = \frac{d\nu}{d\mu} \cdot \frac{d\mu}{d\lambda} \quad \lambda\text{-a.e.}$$

**(c)** 设 $\mu$ 是 $\mathbb{R}^n$ 上有限Borel测度，证明
$$D\mu(x) = \lim_{r \to 0} \frac{\mu(B(x,r))}{|B(x,r)|}$$
对a.e. $x$ 存在（Lebesgue微分定理）。

## 解答

### (a) Radon-Nikodym定理

**证明概要：**

设 $\mu, \nu$ 有限，$\nu \ll \mu$。

**Step 1**：考虑 $\mathcal{F} = \{f \geq 0 : \int_E f \leq \nu(E), \forall E\}$。

$\mathcal{F} \neq \emptyset$（$f = 0$）。令 $\alpha = \sup \int f$。

**Step 2**：取 $f_n$ 使 $\int f_n \to \alpha$，设 $g_n = \max(f_1, \ldots, f_n)$。

可证 $g_n \in \mathcal{F}$，$g_n \uparrow f$，$\int f = \alpha$。

**Step 3**：定义 $\nu_s(E) = \nu(E) - \int_E f$。

若 $\nu_s \neq 0$，存在 $E$ 使 $\nu_s(E) > 0$。

取 $\varepsilon$ 小，构造新函数属于 $\mathcal{F}$ 且积分更大，矛盾。

故 $\nu_s = 0$，即 $\nu(E) = \int_E f$。$\square$

### (b) 链式法则

**证明：**

对任意 $E$：
$$\nu(E) = \int_E \frac{d\nu}{d\mu} d\mu = \int_E \frac{d\nu}{d\mu} \cdot \frac{d\mu}{d\lambda} d\lambda$$

由唯一性，$\frac{d\nu}{d\lambda} = \frac{d\nu}{d\mu} \cdot \frac{d\mu}{d\lambda}$。$\square$

### (c) Lebesgue微分定理

**证明概要：**

对 $\mu = f dx$，$f \in L^1_{loc}$，证
$$\lim_{r \to 0} \frac{1}{|B(x,r)|} \int_{B(x,r)} f(y) dy = f(x) \quad \text{a.e.}$$

**Step 1**：对 $f$ 连续，显然。

**Step 2**：极大函数估计。

$$Mf(x) = \sup_{r > 0} \frac{1}{|B(x,r)|} \int_{B(x,r)} |f|$$

弱$(1,1)$估计：$|\{Mf > \alpha\}| \leq \frac{C}{\alpha} \|f\|_{L^1}$。

**Step 3**：逼近。

对 $f \in L^1$，取连续 $g$ 使 $\|f-g\|_{L^1} < \varepsilon$。

$$\limsup_{r \to 0} |A_r f(x) - f(x)| \leq M(f-g)(x) + |f(x) - g(x)|$$

由极大函数弱估计和选择公理，得a.e.收敛。$\square$
