---
msc_primary: 35-XX
msc_secondary:
  - 35J05
  - 35K05
  - 35L05
processed_at: '2026-04-20'
title: 偏微分方程·波动、热与Laplace方程习题集
---

# 偏微分方程·波动、热与Laplace方程习题集

> 覆盖 D'Alembert 公式、分离变量法、能量方法、Green 函数与最大值原理。共 20 题。

---

### 题1. D'Alembert 公式推导
**题目**：从波动方程 $u_{tt}=c^2u_{xx}$ 出发，通过变量替换 $\xi=x+ct$，$\eta=x-ct$，推导一般解并进而得到初值问题的 D'Alembert 公式。

**难度**：★★☆☆☆

**解答**：$u_{\xi\eta}=0$，故 $u=F(\xi)+G(\eta)=F(x+ct)+G(x-ct)$。由 $u(0,x)=f(x)$，$u_t(0,x)=g(x)$，解得
$$u(t,x)=\frac{f(x+ct)+f(x-ct)}{2}+\frac{1}{2c}\int_{x-ct}^{x+ct}g(s)\,ds.$$

---

### 题2. 波动方程的依赖区域
**题目**：设初值 $f,g$ 仅在区间 $[a,b]$ 上非零。确定 $u(t,x)$ 的非零区域。

**难度**：★★☆☆☆

**解答**：由 D'Alembert 公式，$u(t,x)$ 非零当且仅当 $[x-ct,x+ct]\cap[a,b]\neq\varnothing$。即 $x\in[a-ct,b+ct]$。特征锥传播速度为 $c$。

---

### 题3. 热方程的基本解
**题目**：验证 $K(t,x)=(4\pi t)^{-n/2}e^{-|x|^2/4t}$（$t>0$）满足热方程 $K_t=\Delta K$，且 $\int_{\mathbb{R}^n}K(t,x)\,dx=1$。

**难度**：★★★☆☆

**解答**：直接计算偏导：$\partial_t K=(-\frac{n}{2t}+\frac{|x|^2}{4t^2})K$；$\Delta K=\sum\partial_{x_i}^2 K=\sum(-\frac{1}{2t}+\frac{x_i^2}{4t^2})K=(-\frac{n}{2t}+\frac{|x|^2}{4t^2})K$。积分：$\int e^{-|x|^2/4t}dx=(4\pi t)^{n/2}$。

---

### 题4. 热方程初值问题解的唯一性
**题目**：设 $u(t,x)$ 在 $[0,T]\times\mathbb{R}^n$ 上满足 $u_t=\Delta u$，$u(0,x)=0$，且 $|u(t,x)|\le Ae^{a|x|^2}$。证明 $u\equiv 0$。

**难度**：★★★★☆

**解答**：Tikhonov 反例说明增长条件必要。在给定条件下，对任意 $(t_0,x_0)$，取热核卷积表示并利用唯一性定理得 $u(t_0,x_0)=0$。

---

### 题5. 最大值原理（热方程）
**题目**：设 $u$ 在有界区域 $\Omega\times[0,T]$ 上满足 $u_t-\Delta u=0$。证明 $\max u$ 在抛物边界 $\partial_p(\Omega\times[0,T])=(\partial\Omega\times[0,T])\cup(\Omega\times\{0\})$ 上取得。

**难度**：★★★☆☆

**解答**：令 $v=u+\varepsilon|x|^2$。若 $v$ 在内部 $(x_0,t_0)$ 取最大，则 $v_t\ge 0$，$\Delta v\le 0$，故 $v_t-\Delta v\ge 0$。但 $v_t-\Delta v=2n\varepsilon>0$，矛盾（需精细调整）。标准证法：强最大值原理。

---

### 题6. Laplace 方程的均值性质
**题目**：设 $u$ 在 $\Omega$ 上调和。证明对任意球 $B_r(x)\subset\Omega$：
$$u(x)=\frac{1}{|\partial B_r|}\int_{\partial B_r(x)}u\,dS=\frac{1}{|B_r|}\int_{B_r(x)}u\,dy.$$

**难度**：★★★☆☆

**解答**：令 $\phi(r)=\frac{1}{|\partial B_r|}\int_{\partial B_r(x)}u\,dS$。计算 $\phi'(r)=\frac{1}{|\partial B_r|}\int_{\partial B_r}\partial_\nu u\,dS=\frac{1}{|\partial B_r|}\int_{B_r}\Delta u\,dy=0$。故 $\phi(r)=\phi(0)=u(x)$。

---

### 题7. 强最大值原理
**题目**：设 $\Omega$ 连通，$u$ 在 $\Omega$ 上调和，在 $\bar\Omega$ 上连续。若 $u$ 在内部某点达到最大值，则 $u$ 为常数。

**难度**：★★★☆☆

**解答**：设 $M=\max_{\bar\Omega}u$，$E=\{x\in\Omega:u(x)=M\}$。$E$ 非空（已知内部有最大值点）。由均值性质，$E$ 既开又闭（在 $\Omega$ 中），故 $E=\Omega$。

---

### 题8. Green 第一恒等式
**题目**：设 $\Omega$ 有光滑边界，$u,v\in C^2(\bar\Omega)$。证明
$$\int_\Omega (u\Delta v+\nabla u\cdot\nabla v)\,dx=\int_{\partial\Omega}u\partial_\nu v\,dS.$$

**难度**：★★☆☆☆

**解答**：散度定理：$\int_\Omega\nabla\cdot(u\nabla v)=\int_{\partial\Omega}u\partial_\nu v$。左边 $=\int(\nabla u\cdot\nabla v+u\Delta v)$。

---

### 题9. 分离变量法（波动方程）
**题目**：求解 $u_{tt}=u_{xx}$，$x\in(0,\pi)$，$t>0$，边界条件 $u(t,0)=u(t,\pi)=0$，初值 $u(0,x)=\sin x$，$u_t(0,x)=0$。

**难度**：★★☆☆☆

**解答**：设 $u(t,x)=T(t)X(x)$，得 $T''/T=X''/X=-\lambda$。$X_n(x)=\sin(nx)$，$\lambda_n=n^2$。$T_n(t)=A_n\cos(nt)+B_n\sin(nt)$。由初值：$u(t,x)=\cos t\sin x$。

---

### 题10. 分离变量法（热方程）
**题目**：求解 $u_t=u_{xx}$，$x\in(0,\pi)$，$t>0$，$u(t,0)=u(t,\pi)=0$，$u(0,x)=x(\pi-x)$。

**难度**：★★★☆☆

**解答**：$u(t,x)=\sum_{n=1}^\infty B_n e^{-n^2t}\sin(nx)$。$B_n=\frac{2}{\pi}\int_0^\pi x(\pi-x)\sin(nx)\,dx=\frac{4(1-(-1)^n)}{\pi n^3}$。

---

### 题11. Poisson 方程 Green 函数（半空间）
**题目**：求上半空间 $\mathbb{R}^n_+$ 的 Green 函数，并写出 Dirichlet 问题的解公式。

**难度**：★★★★☆

**解答**：镜像法：$G(x,y)=\Phi(x-y)-\Phi(x-y^*)$，其中 $y^*$ 为 $y$ 关于边界反射，$\Phi$ 为基本解。解：$u(x)=\int_{\mathbb{R}^n_+}G(x,y)f(y)\,dy+\int_{\partial\mathbb{R}^n_+}\partial_\nu G(x,y)g(y)\,dS$。

---

### 题12. 能量守恒（波动方程）
**题目**：设 $u$ 满足 $u_{tt}=c^2\Delta u$ 在 $\mathbb{R}^n$ 中。证明能量 $E(t)=\frac{1}{2}\int_{\mathbb{R}^n}(u_t^2+c^2|\nabla u|^2)\,dx$ 守恒。

**难度**：★★☆☆☆

**解答**：$E'(t)=\int(u_tu_{tt}+c^2\nabla u\cdot\nabla u_t)=\int u_t(u_{tt}-c^2\Delta u)=0$（分部积分，边界项消失）。

---

### 题13. 热方程能量衰减
**题目**：设 $u$ 满足 $u_t=\Delta u$ 在 $\Omega$ 中，$u|_{\partial\Omega}=0$。证明 $\frac{d}{dt}\int_\Omega u^2\,dx\le 0$。

**难度**：★★☆☆☆

**解答**：$\frac{d}{dt}\int u^2=2\int uu_t=2\int u\Delta u=-2\int|\nabla u|^2\le 0$。

---

### 题14. Huygens 原理
**题目**：解释波动方程在奇数维空间满足 Huygens 原理，而偶数维不满足。

**难度**：★★★★☆

**解答**：奇数维 ($n\ge 3$) 的 Kirchhoff/POisson 公式仅依赖特征球面 $\partial B_{ct}(x)$ 上的值，扰动过后不留尾迹。偶数维依赖整个球 $B_{ct}(x)$，有尾迹效应。

---

### 题15. Laplace 方程径向解
**题目**：求 $\Delta u=0$ 在 $\mathbb{R}^n\setminus\{0\}$ 上的径向解 $u=u(r)$。

**难度**：★★☆☆☆

**解答**：$\Delta u=u''+\frac{n-1}{r}u'=0$。解得 $u(r)=Ar^{2-n}+B$（$n\neq 2$）；$u(r)=A\ln r+B$（$n=2$）。

---

### 题16. 热方程的无限传播速度
**题目**：设 $u$ 为热方程初值问题解，初值 $u(0,x)\ge 0$ 且在某紧集外为 0。证明对任意 $t>0$，$u(t,x)>0$ 对所有 $x$ 成立。

**难度**：★★★☆☆

**解答**：$u(t,x)=\int K(t,x-y)u(0,y)\,dy$。热核 $K(t,z)>0$ 对所有 $z$ 成立，故积分恒正。

---

### 题17. 波动方程的有限传播速度
**题目**：设 $u$ 满足波动方程，初值在 $B_R(0)$ 外为 0。证明 $u(t,x)=0$ 当 $|x|>R+ct$。

**难度**：★★☆☆☆

**解答**：由 D'Alembert 公式（一维）或 Kirchhoff 公式（高维），解仅依赖以 $x$ 为中心、半径 $ct$ 的球/区间上的初值。若该球与初值支撑不交，则 $u(t,x)=0$。

---

### 题18. 调和函数的 Liouville 定理
**题目**：证明有上界（或下界）的全局调和函数必为常数。

**难度**：★★★☆☆

**解答**：设 $u\le M$。令 $v=M-u\ge 0$ 调和。对任意 $x,y$，由 Harnack 不等式，$v(y)\le C_nv(x)$。令 $R\to\infty$，得 $v$ 有界。再用梯度估计得 $|\nabla u|\le C/R\to 0$，故 $u$ 常数。

---

### 题19. 热方程的相似解
**题目**：求热方程 $u_t=u_{xx}$ 形如 $u(t,x)=t^\alpha f(x/t^\beta)$ 的自相似解，并确定 $\alpha,\beta$。

**难度**：★★★★☆

**解答**：量纲分析：设 $\xi=x/\sqrt{t}$（$\beta=1/2$）。代入得 $f''+\frac{\xi}{2}f'+\alpha f=0$。取 $\alpha=-1/2$ 得 $f(\xi)=e^{-\xi^2/4}$（高斯解），即基本解。

---

### 题20. 三维波动方程的 Kirchhoff 公式
**题目**：推导三维波动方程初值问题的 Kirchhoff 公式。

**难度**：★★★★☆

**解答**：
$$u(t,x)=\partial_t\left(\frac{1}{4\pi c^2t}\int_{|y-x|=ct}f(y)\,dS\right)+\frac{1}{4\pi c^2t}\int_{|y-x|=ct}g(y)\,dS.$$
由球平均降维法或 Fourier 变换得到。

---

**Lean4 对应**：分析学形式化目前对 PDE 支持有限，主要参考 `Mathlib4` 的 Sobolev 空间与分布论进展。
