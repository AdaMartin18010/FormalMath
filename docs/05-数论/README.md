---
title: "数论基础导论"
msc_primary: "11"
---

# 数论基础导论

## 1. 引言

**数论**（Number Theory）是研究整数性质及其结构的数学分支，被誉为"数学的皇后"。从古希腊时代对素数的朴素追问，到现代密码学中 RSA 算法的数学根基，数论始终处于数学研究的核心位置。本导论系统梳理数论的基石概念——整除性、最大公约数、素数理论、同余算术以及欧拉定理，为后续初等数论、解析数论与代数数论的深入学习奠定坚实基础。

---

## 2. 整除性与带余除法

### 2.1 整除的严格定义

**定义 2.1（整除）**. 设 $a, b \in \mathbb{Z}$，且 $b \neq 0$。若存在整数 $q \in \mathbb{Z}$ 使得
$$
a = bq,
$$
则称 $b$ **整除** $a$（$b$ divides $a$），记为 $b \mid a$。此时 $b$ 称为 $a$ 的**因数**（divisor），$a$ 称为 $b$ 的**倍数**（multiple）。若不存在这样的 $q$，则记为 $b \nmid a$。

**基本性质**. 对任意整数 $a, b, c$，整除关系满足：
1. **自反性**：$a \mid a$（$a \neq 0$）；
2. **传递性**：若 $a \mid b$ 且 $b \mid c$，则 $a \mid c$；
3. **线性组合性**：若 $a \mid b$ 且 $a \mid c$，则 $a \mid (bx + cy)$ 对所有 $x, y \in \mathbb{Z}$ 成立。

### 2.2 带余除法定理

**定理 2.1（带余除法）**. 设 $a, b \in \mathbb{Z}$ 且 $b > 0$。则存在唯一的整数对 $(q, r)$ 使得
$$
a = bq + r, \quad 0 \leq r < b.
$$

**证明**.

**存在性**：考虑集合 $S = \{a - bk \mid k \in \mathbb{Z}, \; a - bk \geq 0\}$。取 $k = -|a|$，则 $a - b(-|a|) = a + b|a| \geq 0$（因 $b > 0$），故 $S$ 非空。由良序原理（well-ordering principle），$S$ 有最小元 $r = a - bq$。若 $r \geq b$，则 $r - b = a - b(q+1) \in S$ 且更小，矛盾。故 $0 \leq r < b$。

**唯一性**：设 $a = bq_1 + r_1 = bq_2 + r_2$，其中 $0 \leq r_1, r_2 < b$。不妨设 $r_1 \geq r_2$，则
$$
b(q_1 - q_2) = r_2 - r_1.
$$
左边绝对值要么为 $0$，要么 $\geq b$；右边满足 $0 \leq r_1 - r_2 < b$。故两边必须为 $0$，即 $r_1 = r_2$ 且 $q_1 = q_2$。$\square$

### 2.3 例子

**例 2.1**. 设 $a = 47, b = 5$。则 $47 = 5 \times 9 + 2$，故商 $q = 9$，余数 $r = 2$。验证 $0 \leq 2 < 5$。

**例 2.2**. 设 $a = -31, b = 7$。取 $q = -5$，则 $-31 = 7 \times (-5) + 4$，余数 $r = 4$ 满足 $0 \leq 4 < 7$。注意此处若取 $q = -4$，则余数为 $-3$，不满足非负条件，说明商 $q$ 的唯一性由余数约束 $0 \leq r < b$ 保证。

---

## 3. 最大公约数与欧几里得算法

### 3.1 最大公约数

**定义 3.1（最大公约数）**. 设 $a, b \in \mathbb{Z}$ 不全为零。整数 $d$ 称为 $a$ 与 $b$ 的**最大公约数**（greatest common divisor），记为 $\gcd(a, b)$ 或 $(a, b)$，若满足：
1. $d \mid a$ 且 $d \mid b$（公因子）；
2. 若 $c \mid a$ 且 $c \mid b$，则 $c \mid d$（最大性）。

约定 $\gcd(0, 0) = 0$。最大公约数在相差一个符号的意义下唯一，通常取正值。

### 3.2 欧几里得算法

**定理 3.1（欧几里得算法）**. 设 $a = bq + r$ 为带余除法，则
$$
\gcd(a, b) = \gcd(b, r).
$$

**证明**. 设 $d = \gcd(a, b)$。由 $r = a - bq$ 及整除的线性组合性，$d \mid r$。故 $d$ 是 $b$ 与 $r$ 的公因子，从而 $d \leq \gcd(b, r)$。反之，设 $d' = \gcd(b, r)$，则 $d' \mid b$ 且 $d' \mid r$，从而 $d' \mid a = bq + r$。故 $d' \leq \gcd(a, b) = d$。因此 $d = d'$。$\square$

该定理提供了计算 $\gcd$ 的递归算法：反复用余数替换除数，直至余数为 $0$，最后的非零余数即为最大公约数。

**定理 3.2（Bézout 恒等式）**. 设 $a, b \in \mathbb{Z}$ 不全为零。则存在整数 $x, y$ 使得
$$
\gcd(a, b) = ax + by.
$$

**证明**. 设 $S = \{am + bn \mid m, n \in \mathbb{Z}, \; am + bn > 0\}$。因 $a, b$ 不全为零，$S$ 非空。由良序原理，$S$ 有最小元 $d = ax + by$。

先证 $d \mid a$。由带余除法，$a = dq + r$，$0 \leq r < d$。则
$$
r = a - dq = a - (ax + by)q = a(1 - xq) + b(-yq).
$$
若 $r > 0$，则 $r \in S$ 且 $r < d$，与 $d$ 的最小性矛盾。故 $r = 0$，$d \mid a$。同理 $d \mid b$。

再证最大性：若 $c \mid a$ 且 $c \mid b$，则 $c \mid (ax + by) = d$。故 $d = \gcd(a, b)$。$\square$

### 3.3 例子

**例 3.1（欧几里得算法计算）**. 计算 $\gcd(252, 180)$：
$$
\begin{aligned}
252 &= 1 \times 180 + 72, \\
180 &= 2 \times 72 + 36, \\
72 &= 2 \times 36 + 0.
\end{aligned}
$$
故 $\gcd(252, 180) = 36$。

回代求 Bézout 系数：
$$
\begin{aligned}
36 &= 180 - 2 \times 72 \\
   &= 180 - 2 \times (252 - 1 \times 180) \\
   &= 3 \times 180 - 2 \times 252.
\end{aligned}
$$
故 $x = -2, y = 3$ 满足 $36 = (-2) \times 252 + 3 \times 180$。

**例 3.2（互素）**. 若 $\gcd(a, b) = 1$，则称 $a$ 与 $b$ **互素**（coprime 或 relatively prime）。例如 $\gcd(8, 15) = 1$。由 Bézout 恒等式，存在 $x, y$ 使得 $8x + 15y = 1$。事实上 $8 \times 2 + 15 \times (-1) = 1$。互素整数在模运算中扮演关键角色。

---

## 4. 素数与算术基本定理

### 4.1 素数与合数

**定义 4.1（素数）**. 设整数 $p > 1$。若 $p$ 的正因数只有 $1$ 和 $p$ 本身，则称 $p$ 为**素数**（prime number）。大于 $1$ 的非素数整数称为**合数**（composite number）。

**引理 4.1（素数性质）**. 设 $p$ 为素数。若 $p \mid ab$，则 $p \mid a$ 或 $p \mid b$。

**证明**. 设 $p \nmid a$。因 $p$ 为素数，$\gcd(a, p) = 1$。由 Bézout 恒等式，存在 $x, y$ 使 $ax + py = 1$。两边乘以 $b$：
$$
abx + pby = b.
$$
由 $p \mid ab$ 且 $p \mid pb$，得 $p \mid b$。$\square$

### 4.2 算术基本定理

**定理 4.1（算术基本定理）**. 每个大于 $1$ 的整数 $n$ 都可以唯一地（不计素因子排列顺序）表示为
$$
n = p_1^{e_1} p_2^{e_2} \cdots p_k^{e_k},
$$
其中 $p_1 < p_2 < \cdots < p_k$ 为素数，$e_i \geq 1$。此表示称为 $n$ 的**标准分解式**。

**证明**.

**存在性**：对 $n$ 归纳。$n = 2$ 显然。设对一切 $m < n$ 成立。若 $n$ 为素数，则已得。若 $n$ 为合数，则 $n = ab$ 且 $1 < a, b < n$。由归纳假设，$a, b$ 均可分解为素数乘积，故 $n$ 亦可。

**唯一性**：设 $n$ 有两分解 $n = p_1 \cdots p_s = q_1 \cdots q_t$（允许重复）。对 $p_1$，由引理 4.1，$p_1 \mid q_j$ 对某个 $j$。因 $q_j$ 为素数，$p_1 = q_j$。两边约去 $p_1$，对余下部分继续此过程。由归纳法，两种分解的素数及其重数完全一致。$\square$

### 4.3 素数无限性

**定理 4.2（Euclid）**. 素数有无穷多个。

**证明（反证法）**. 假设素数仅有有限个：$p_1, p_2, \ldots, p_k$。令
$$
N = p_1 p_2 \cdots p_k + 1.
$$
则 $N > 1$，且对任意 $i$，$p_i \nmid N$（因 $N \equiv 1 \pmod{p_i}$）。故 $N$ 的素因子不在 $\{p_1, \ldots, p_k\}$ 中，矛盾。$\square$

### 4.4 例子

**例 4.1（标准分解）**. $360 = 2^3 \times 3^2 \times 5^1$。由唯一分解定理，可快速计算：
$$
\gcd(360, 504) = 2^{\min(3,3)} \times 3^{\min(2,2)} \times 5^{\min(1,0)} = 2^3 \times 3^2 = 72.
$$

**例 4.2（Mersenne 数）**. 形如 $M_p = 2^p - 1$ 的数称为 **Mersenne 数**。若 $M_p$ 为素数，则 $p$ 必为素数（逆不成立）。例如 $M_2 = 3, M_3 = 7, M_5 = 31$ 均为素数，而 $M_{11} = 2047 = 23 \times 89$ 为合数。Mersenne 素数是已知最大素数的重要来源。

---

## 5. 同余理论

### 5.1 同余的定义

**定义 5.1（同余）**. 设 $m \in \mathbb{Z}^+$，$a, b \in \mathbb{Z}$。若 $m \mid (a - b)$，则称 $a$ 与 $b$ **模 $m$ 同余**（congruent modulo $m$），记为
$$
a \equiv b \pmod{m}.
$$
整数 $m$ 称为**模**（modulus）。

同余关系是整数集 $\mathbb{Z}$ 上的等价关系，将 $\mathbb{Z}$ 划分为 $m$ 个等价类，称为**剩余类**：
$$
\overline{a} = \{a + km \mid k \in \mathbb{Z}\}, \quad a = 0, 1, \ldots, m-1.
$$

### 5.2 同余的运算性质

**定理 5.1**. 若 $a \equiv b \pmod{m}$，$c \equiv d \pmod{m}$，则：
1. $a + c \equiv b + d \pmod{m}$；
2. $a - c \equiv b - d \pmod{m}$；
3. $ac \equiv bd \pmod{m}$；
4. 若 $n \in \mathbb{Z}^+$，则 $a^n \equiv b^n \pmod{m}$。

**证明**. 由 $m \mid (a-b)$ 且 $m \mid (c-d)$，得 $m \mid [(a-b) \pm (c-d)] = (a \pm c) - (b \pm d)$，即 (1)(2)。对 (3)，
$$
ac - bd = ac - bc + bc - bd = c(a-b) + b(c-d),
$$
右边两项均被 $m$ 整除，故 $m \mid (ac - bd)$。(4) 由 (3) 迭代可得。$\square$

### 5.3 线性同余方程

**定理 5.2**. 设 $a, b \in \mathbb{Z}$，$m \in \mathbb{Z}^+$。同余方程
$$
ax \equiv b \pmod{m}
$$
有解当且仅当 $d = \gcd(a, m) \mid b$。此时恰有 $d$ 个互不同余的解模 $m$。

**证明**. 方程 $ax \equiv b \pmod{m}$ 等价于存在 $y \in \mathbb{Z}$ 使 $ax + my = b$。由 Bézout 恒等式，此线性Diophantine方程有解当且仅当 $d \mid b$。

设 $x_0$ 为一特解，则通解为
$$
x = x_0 + \frac{m}{d} t, \quad t \in \mathbb{Z}.
$$
当 $t = 0, 1, \ldots, d-1$ 时，$x$ 模 $m$ 互不同余，故恰有 $d$ 个解。$\square$

### 5.4 例子

**例 5.1**. 解 $7x \equiv 3 \pmod{11}$。因 $\gcd(7, 11) = 1 \mid 3$，方程有唯一解。由 Bézout 系数 $7 \times 8 + 11 \times (-5) = 1$，两边乘 $3$ 得 $7 \times 24 \equiv 3 \pmod{11}$。故 $x \equiv 24 \equiv 2 \pmod{11}$。验证：$7 \times 2 = 14 \equiv 3 \pmod{11}$。

**例 5.2**. 解 $6x \equiv 9 \pmod{15}$。$d = \gcd(6, 15) = 3 \mid 9$，故有 $3$ 个解。先约简为 $2x \equiv 3 \pmod{5}$，解得 $x \equiv 4 \pmod{5}$。因此原方程的三个解为：
$$
x \equiv 4, \; 9, \; 14 \pmod{15}.
$$

---

## 6. 欧拉函数与欧拉定理

### 6.1 欧拉函数

**定义 6.1（欧拉函数）**. 设 $n \in \mathbb{Z}^+$。定义 **Euler $\varphi$-函数**为
$$
\varphi(n) = \#\{a \in \mathbb{Z} \mid 1 \leq a \leq n, \; \gcd(a, n) = 1\},
$$
即区间 $[1, n]$ 中与 $n$ 互素的整数个数。

**定理 6.1（Euler 函数的积性）**. 若 $\gcd(m, n) = 1$，则 $\varphi(mn) = \varphi(m)\varphi(n)$。

**证明（概要）**. 由中国剩余定理，映射 $a \mapsto (a \bmod m, a \bmod n)$ 给出环同构
$$
\mathbb{Z}/mn\mathbb{Z} \cong \mathbb{Z}/m\mathbb{Z} \times \mathbb{Z}/n\mathbb{Z}.
$$
单位群之间的对应保持互素性，故 $\varphi(mn) = \varphi(m)\varphi(n)$。$\square$

**推论**. 若 $n = p_1^{e_1} \cdots p_k^{e_k}$ 为标准分解，则
$$
\varphi(n) = n \prod_{i=1}^k \left(1 - \frac{1}{p_i}\right) = \prod_{i=1}^k p_i^{e_i-1}(p_i - 1).
$$

### 6.2 欧拉定理与费马小定理

**定理 6.2（Euler 定理）**. 设 $n \in \mathbb{Z}^+$，$a \in \mathbb{Z}$，且 $\gcd(a, n) = 1$。则
$$
a^{\varphi(n)} \equiv 1 \pmod{n}.
$$

**证明**. 考虑模 $n$ 的既约剩余系（reduced residue system）$R = \{r_1, r_2, \ldots, r_{\varphi(n)}\}$，其中每个 $r_i$ 满足 $\gcd(r_i, n) = 1$。因 $\gcd(a, n) = 1$，集合 $aR = \{ar_1, ar_2, \ldots, ar_{\varphi(n)}\}$ 也是既约剩余系（模 $n$ 下互不同余且均与 $n$ 互素）。故
$$
\prod_{i=1}^{\varphi(n)} r_i \equiv \prod_{i=1}^{\varphi(n)} (ar_i) = a^{\varphi(n)} \prod_{i=1}^{\varphi(n)} r_i \pmod{n}.
$$
因 $\prod r_i$ 与 $n$ 互素，可两边约去，得 $a^{\varphi(n)} \equiv 1 \pmod{n}$。$\square$

**定理 6.3（Fermat 小定理）**. 设 $p$ 为素数，$a \in \mathbb{Z}$，$p \nmid a$。则
$$
a^{p-1} \equiv 1 \pmod{p}.
$$

**证明**. 素数 $p$ 时，$\varphi(p) = p-1$（因 $1, 2, \ldots, p-1$ 均与 $p$ 互素）。由 Euler 定理即得。$\square$

### 6.3 例子

**例 6.1**. 计算 $3^{100} \bmod 7$。因 $7$ 为素数且 $7 \nmid 3$，由 Fermat 小定理，$3^6 \equiv 1 \pmod{7}$。于是
$$
3^{100} = 3^{16 \times 6 + 4} = (3^6)^{16} \cdot 3^4 \equiv 1^{16} \cdot 81 \equiv 4 \pmod{7}.
$$

**例 6.2**. 计算 $5^{2024} \bmod 12$。$\varphi(12) = 12(1 - 1/2)(1 - 1/3) = 4$。因 $\gcd(5, 12) = 1$，由 Euler 定理 $5^4 \equiv 1 \pmod{12}$。于是
$$
5^{2024} = (5^4)^{506} \equiv 1^{506} \equiv 1 \pmod{12}.
$$

---

## 7. 内容导航

- **01-初等数论** — 整除、同余、原根与二次剩余
- **02-解析数论** — 素数分布、Riemann $\zeta$ 函数
- **03-代数数论** — 代数整数、理想类群
- **04-算术几何** — 椭圆曲线、Diophantine 方程
- **07-深度扩展** — 高级专题与前沿进展
- **算法实现与计算实践 / 高级习题**
- **L函数 / p进数 / 模形式 / 椭圆曲线算术**

---

## 8. 相关链接

- [项目总索引](../../INDEX.md)
- [组合数学与离散数学](../09-组合数学与离散数学)
- [未解决问题](../00-未解决问题)

---

**最后更新**: 2026年4月
**维护者**: FormalMath项目组
