---
msc_primary: 00A99
习题编号: ANA-110
学科: 实分析
知识点: 函数空间-BMO
难度: ⭐⭐⭐⭐⭐
预计时间: 35分钟
---

# BMO空间与John-Nirenberg不等式

## 题目

**BMO**（有界平均振动）：
$$\|f\|_{BMO} = \sup_Q \frac{1}{|Q|} \int_Q |f - f_Q| dx < \infty$$
其中 $f_Q = \frac{1}{|Q|}\int_Q f$ 是平均。

(a) 证明 $L^\infty \subset BMO$，但 $\log|x| \in BMO(\mathbb{R})$ 而 $\notin L^\infty$。

(b) 证明John-Nirenberg不等式：存在常数 $c_1, c_2$ 使得对所有方体 $Q$：
$$\left|\left\{x \in Q: |f(x) - f_Q| > \lambda\right\}\right| \leq c_1 |Q| \exp\left(-\frac{c_2 \lambda}{\|f\|_{BMO}}\right)$$

(c) 证明 $BMO \subset \bigcap_{p < \infty} L^p_{loc}$。

## 解答

### (a) BMO的基本例子

**证明：**

**$L^\infty \subset BMO$**：

若 $|f| \leq M$，则 $|f - f_Q| \leq 2M$，故 $\|f\|_{BMO} \leq 2M$。

**$\log|x| \in BMO$**：

设 $Q = (a, b)$，$0 < a < b$。

**情形1**：$Q$ 不包含0。$\log|x|$ 在 $Q$ 光滑，振动有界。

**情形2**：$Q$ 包含0。设 $Q = (-r, r)$。

$f_Q = 0$（对称性）。

$$\frac{1}{2r} \int_{-r}^r |\log|x|| dx = \frac{1}{r} \int_0^r (-\log x) dx$$

$$= \frac{1}{r} [-x\log x + x]_0^r = 1 - \log r + 1 = O(1)$$

有界，故 $\|\log|x|\|_{BMO} < \infty$。

但 $\log|x|$ 在0附近无界。$\square$

### (b) John-Nirenberg不等式

**证明概要：**

用CZ分解的迭代。

设 $\|f\|_{BMO} = 1$，固定方体 $Q_0$。

**Step 1**：第一层分解。

对 $f - f_{Q_0}$ 在 $Q_0$ 上做CZ分解，水平 $\lambda_0 = 2$。

得方体 $\{Q_{1,j}\}$ 使得 $|f - f_{Q_0}| \leq 2$ 于 $G_1 = Q_0 \setminus \bigcup Q_{1,j}$。

且 $\frac{1}{|Q_{1,j}|}\int_{Q_{1,j}} |f - f_{Q_0}| \leq 2$。

由BMO定义，$|f_{Q_{1,j}} - f_{Q_0}| \leq 2$。

**Step 2**：迭代。

对每个 $Q_{1,j}$，继续CZ分解 $f - f_{Q_{1,j}}$。

在第 $k$ 层，$|f - f_{Q_0}| \leq 2k$ 于好集。

坏集测度指数衰减。

**Step 3**：指数估计。

经过 $k$ 层，坏集测度 $\leq 2^{-k}|Q_0|$。

对 $\lambda = 2k$，得：
$$|\{|f - f_{Q_0}| > \lambda\}| \leq |Q_0| 2^{-\lambda/2}$$

整理即得不等式。$\square$

### (c) BMO的局部可积性

**证明：**

由JN不等式，对任意 $p < \infty$：
$$\frac{1}{|Q|}\int_Q |f - f_Q|^p dx = p \int_0^\infty \lambda^{p-1} \frac{|\{|f-f_Q| > \lambda\}|}{|Q|} d\lambda$$

$$\leq c_1 p \int_0^\infty \lambda^{p-1} e^{-c_2 \lambda /\|f\|_{BMO}} d\lambda < \infty$$

因此 $f \in L^p_{loc}$ 对所有 $p < \infty$。$\square$

## 证明技巧

1. **对称性简化**：对数函数在对称区间上的平均
2. **迭代CZ分解**：获得指数衰减的关键
3. **分布函数计算**：$L^p$ 范数用层蛋糕表示

## 常见错误

- ❌ 在(a)中忽略 $Q$ 包含原点的情形
- ❌ JN不等式证明中迭代层次计算错误
- ❌ 忘记BMO是商空间（模去常数）

## 变式练习

**变式1：** 证明 $H^1$ 的对偶是BMO（Fefferman定理）。

**变式2：** 证明 $\log|P| \in BMO$ 对任何多项式 $P$。
