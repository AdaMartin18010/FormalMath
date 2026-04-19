---
title: "数论基础导论"
msc_primary: "11"
---

# 数论基础导论

数论（Number Theory）是研究整数性质及其结构的数学分支，被誉为"数学的皇后"。从古希腊时代对素数的朴素追问，到现代密码学中 RSA 算法的数学根基，数论始终处于数学研究的核心位置。本导论系统梳理数论的基石概念——整除性、最大公约数、素数理论、同余算术以及欧拉定理，为后续初等数论、解析数论与代数数论的深入学习奠定坚实基础。

## 1. 整除性与带余除法

### 1.1 整除的严格定义

**定义 1.1（整除）**. 设 $a, b \in \mathbb{Z}$，且 $b \neq 0$。若存在整数 $q \in \mathbb{Z}$ 使得 $a = bq$，则称 $b$ 整除 $a$，记 $b \mid a$。

**定理 1.2（带余除法）**. 对任意 $a, b \in \mathbb{Z}$，$b > 0$，存在唯一的 $q, r \in \mathbb{Z}$ 使得 $a = bq + r$，$0 \leq r < b$。

*证明*. 考虑集合 $S = \{a - bk : k \in \mathbb{Z}, a - bk \geq 0\}$。$S$ 为非负整数集的非空子集（取 $k$ 充分小），故有最小元 $r = a - bq$。若 $r \geq b$，则 $r - b = a - b(q+1) \in S$ 且更小，矛盾。唯一性：设 $a = bq + r = bq' + r'$，则 $b(q-q') = r' - r$。由 $|r'-r| < b$ 得 $q = q'$，$r = r'$。$\square$

## 2. 最大公约数与辗转相除法

### 2.1 最大公约数

**定义 2.1（GCD）**. $d = \gcd(a,b)$ 是满足 $d \mid a$，$d \mid b$ 且对任意 $c \mid a, c \mid b$ 有 $c \mid d$ 的最大正整数。

**定理 2.2（Bézout 恒等式）**. 对任意 $a, b \in \mathbb{Z}$，存在 $x, y \in \mathbb{Z}$ 使得 $\gcd(a,b) = ax + by$。

*证明*. 设 $S = \{ax + by : x, y \in \mathbb{Z}, ax + by > 0\}$。$S$ 非空（取 $x = \operatorname{sgn}(a), y = 0$），令 $d = ax_0 + by_0$ 为最小元。若 $d \nmid a$，则 $a = dq + r$，$0 < r < d$，$r = a(1-qx_0) + b(-qy_0) \in S$ 且更小，矛盾。故 $d \mid a$，同理 $d \mid b$。若 $c \mid a, c \mid b$，则 $c \mid d$。$\square$

### 2.2 辗转相除法

**算法 2.3（Euclidean 算法）**. 
1. $r_0 = a$，$r_1 = b$；
2. $r_{k-1} = q_k r_k + r_{k+1}$，$0 \leq r_{k+1} < r_k$；
3. 直到 $r_{n+1} = 0$，则 $\gcd(a,b) = r_n$。

## 3. 素数理论

### 3.1 素数与算术基本定理

**定义 3.1（素数）**. 整数 $p > 1$ 称为素数，若其正因子只有 $1$ 和 $p$。

**定理 3.2（欧几里得）**. 素数有无穷多个。

*证明*. 假设素数有限：$p_1, \dots, p_n$。令 $N = p_1 \cdots p_n + 1$。$N > 1$，故 $N$ 有素因子 $q$。若 $q = p_i$，则 $q \mid N - p_1\cdots p_n = 1$，矛盾。$\square$

**定理 3.3（算术基本定理）**. 每个大于 1 的整数可唯一分解为素数的乘积（不计顺序）。

*证明*. 存在性：对 $n$ 归纳，$n$ 为素数或 $n = ab$（$1 < a, b < n$）。唯一性：设 $n = p_1 \cdots p_k = q_1 \cdots q_l$。$p_1 \mid q_1 \cdots q_l$，由素数性质 $p_1 = q_j$。消去归纳。$\square$

## 4. 同余与欧拉定理

### 4.1 同余算术

**定义 4.1（同余）**. $a \equiv b \pmod{m}$ 当且仅当 $m \mid (a-b)$。

**定理 4.2（中国剩余定理）**. 设 $m_1, \dots, m_k$ 两两互素。则对任意 $a_1, \dots, a_k$，同余方程组 $x \equiv a_i \pmod{m_i}$ 有唯一解模 $M = m_1 \cdots m_k$。

*证明*. 令 $M_i = M/m_i$。由 $\gcd(M_i, m_i) = 1$，存在 $y_i$ 使 $M_i y_i \equiv 1 \pmod{m_i}$。则 $x = \sum a_i M_i y_i$ 为解。唯一性：若 $x, x'$ 均为解，则 $m_i \mid (x-x')$，故 $M \mid (x-x')$。$\square$

### 4.2 欧拉定理

**定义 4.3（Euler 函数）**. $\varphi(n) = |(\mathbb{Z}/n\mathbb{Z})^\times|$，即 $1 \leq k \leq n$ 中与 $n$ 互素的整数个数。

**定理 4.4（Euler）**. 若 $\gcd(a,n) = 1$，则 $a^{\varphi(n)} \equiv 1 \pmod{n}$。

*证明*. $(\mathbb{Z}/n\mathbb{Z})^\times$ 为 $\varphi(n)$ 阶乘法群。由 Lagrange 定理，$a^{\varphi(n)} \equiv 1$。$\square$

**推论 4.5（Fermat 小定理）**. $p$ 素数，$p \nmid a$，则 $a^{p-1} \equiv 1 \pmod{p}$。

## 5. 例子

### 5.1 例子：RSA 算法

选择素数 $p, q$，$n = pq$，$\varphi(n) = (p-1)(q-1)$。选 $e$ 使 $\gcd(e, \varphi(n)) = 1$，计算 $d = e^{-1} \pmod{\varphi(n)}$。

加密：$c = m^e \pmod{n}$。解密：$m = c^d \pmod{n}$。

正确性：$c^d = m^{ed} = m^{1+k\varphi(n)} \equiv m \pmod{n}$（由 Euler 定理）。

### 5.2 例子：二次互反律

**定理 5.1（Gauss 二次互反律）**. 对相异奇素数 $p, q$：

$$\left(\frac{p}{q}\right)\left(\frac{q}{p}\right) = (-1)^{\frac{p-1}{2}\cdot\frac{q-1}{2}}.$$

其中 Legendre 符号 $\left(\frac{a}{p}\right) = 1$（$a$ 为模 $p$ 二次剩余），$-1$（非剩余），$0$（$p \mid a$）。

## 6. 交叉引用

- [代数数论](docs/05-数论/代数数论-基础.md) — 数域与理想分解
- [解析数论](docs/05-数论/解析数论-基础.md) — ζ 函数与素数分布
- [模形式](docs/05-数论/模形式-基础.md) — 自守形式与 L-函数
- [密码学](docs/24-密码学/零知识证明-基础.md) — 数论在密码学中的应用
- [抽象代数](docs/02-代数结构/02-核心理论/群论/01-群论-增强版.md) — 群论基础

---

**适用**：docs/05-数论/
