---
msc_primary: "11G05"
msc_secondary: ["11G40", "11G07", "14H52"]
---

# 椭圆曲线与BSD猜想 - 深度扩展版 / Elliptic Curves and BSD Conjecture - Deep Extension

> **教学深度**：研究生进阶 / 研究入门
> **参考标准**：Silverman "The Arithmetic of Elliptic Curves", Diamond-Shurman
> **MSC2020**: 11G05 (椭圆曲线), 11G40 (L函数的BSD猜想)

---

## 目录 / Table of Contents

- [椭圆曲线与BSD猜想 - 深度扩展版 / Elliptic Curves and BSD Conjecture - Deep Extension](#椭圆曲线与bsd猜想---深度扩展版--elliptic-curves-and-bsd-conjecture---deep-extension)
  - [目录 / Table of Contents](#目录)
  - [1. 椭圆曲线的算术基础](#1-椭圆曲线的算术基础)
    - [1.1 Weierstrass方程与群结构](#11-weierstrass方程与群结构)
    - [1.2 挠子群与判别式](#12-挠子群与判别式)
  - [2. Mordell-Weil定理](#2-mordell-weil定理)
    - [2.1 有理点群的有限生成性](#21-有理点群的有限生成性)
    - [2.2 高度函数与下降法](#22-高度函数与下降法)
  - [3. BSD猜想的陈述](#3-bsd猜想的陈述)
    - [3.1 解析秩与代数秩](#31-解析秩与代数秩)
    - [3.2 精细BSD公式](#32-精细bsd公式)
  - [4. BSD猜想的进展](#4-bsd猜想的进展)
    - [4.1 Coates-Wiles定理](#41-coates-wiles定理)
    - [4.2 Gross-Zagier与Kolyvagin](#42-gross-zagier与kolyvagin)
  - [参考文献](#参考文献)

---

## 一、椭圆曲线的算术基础

### 1.1 Weierstrass方程与群结构

**定义 1.1**（椭圆曲线）：设 $K$ 是域，$\text{char}(K) \neq 2, 3$。$K$ 上的**椭圆曲线** $E$ 是射影平面中由Weierstrass方程定义的曲线：
$$E: y^2 = x^3 + ax + b, \quad a, b \in K$$

要求**判别式**非零：$\Delta = -16(4a^3 + 27b^2) \neq 0$（保证非奇异）。

**例 1.2**（具体椭圆曲线）：

**(a)** $E_1: y^2 = x^3 - x$（congruence number curve）

- $a = -1$, $b = 0$
- $\Delta = -16(-4) = 64 \neq 0$
- $j$-不变量：$j = 1728 \cdot \frac{4a^3}{4a^3 + 27b^2} = 1728$

**(b)** $E_2: y^2 = x^3 + 1$（椭圆曲线 $27a3$）

- $a = 0$, $b = 1$
- $\Delta = -432$
- $j = 0$

**定理 1.3**（群结构）：椭圆曲线 $E(K)$ 上的点集具有自然的阿贝尔群结构，其中：

- 单位元是无穷远点 $\mathcal{O} = [0:1:0]$
- 逆元：$-(x, y) = (x, -y)$
- 加法：三点共线则其和为 $\mathcal{O}$

**几何加法法则**：设 $P, Q \in E(K)$，$R = P + Q$ 的构造：

1. 画直线 $L$ 通过 $P$ 和 $Q$（若 $P = Q$ 则取切线）
2. $L$ 与 $E$ 交于第三点 $R'$
3. $R = -R'$（即关于 $x$-轴反射）

**例 1.4**（在 $E: y^2 = x^3 - x$ 上计算）：

$P = (0, 0)$ 是2阶点，因直线 $OP$ 与 $E$ 在无穷远点相交，故 $2P = \mathcal{O}$。

$Q = (2, \sqrt{6})$ 的倍点计算：切线斜率 $\lambda = \frac{3x^2 - 1}{2y} = \frac{11}{2\sqrt{6}}$，
$$2Q = \left(\lambda^2 - 2x, \lambda(x - x_{2Q}) - y\right)$$

### 1.2 挠子群与判别式

**定理 1.5**（Mazur定理，1977）：设 $E/\mathbb{Q}$ 是椭圆曲线，则挠子群 $E(\mathbb{Q})_{\text{tors}}$ 必为以下之一：

- 循环群：$\mathbb{Z}/n\mathbb{Z}$，$n \in \{1, 2, \ldots, 10, 12\}$
- 直积：$\mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/2n\mathbb{Z}$，$n \in \{1, 2, 3, 4\}$

**例 1.6**：

| 曲线 | 方程 | 挠子群 |
|------|------|--------|
| $X_0(11)$ | $y^2 + y = x^3 - x^2$ | $\mathbb{Z}/5\mathbb{Z}$ |
| $X_0(14)$ | $y^2 + xy + y = x^3 + 4x - 6$ | $\mathbb{Z}/6\mathbb{Z}$ |
| $X_0(15)$ | $y^2 + xy + y = x^3 + x^2$ | $\mathbb{Z}/4\mathbb{Z}$ |

---

## 二、Mordell-Weil定理

### 2.1 有理点群的有限生成性

**定理 2.1**（Mordell-Weil定理）：设 $E/\mathbb{Q}$ 是椭圆曲线，则 $E(\mathbb{Q})$ 是有限生成阿贝尔群：
$$E(\mathbb{Q}) \cong E(\mathbb{Q})_{\text{tors}} \times \mathbb{Z}^r$$

其中 $r = \text{rank}(E)$ 称为**秩**。

**历史背景**：

- **Poincaré (1901)**：提出猜想
- **Mordell (1922)**：证明 $\mathbb{Q}$ 上的情形
- **Weil (1928)**：推广到任意数域和阿贝尔簇

**例 2.2**：

**(a)** $E: y^2 = x^3 - x$：$\text{rank}(E) = 0$，$E(\mathbb{Q}) = \{\mathcal{O}, (0,0), (\pm 1, 0)\} \cong \mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/2\mathbb{Z}$

**(b)** $E: y^2 = x^3 - 2$：$\text{rank}(E) = 0$，由Fermat证明 $x^3 = y^2 + 2$ 的唯一整数解为 $(x,y) = (3, \pm 5)$

**(c)** $E: y^2 = x^3 - 4x$：$\text{rank}(E) = 1$，生成元 $P = (2, 2\sqrt{2})$（在 $\mathbb{Q}(\sqrt{2})$ 上）

### 2.2 高度函数与下降法

**定义 2.3**（标准高度）：点 $P \in E(\mathbb{Q})$ 的**标准高度**（Néron-Tate高度）定义为：
$$\hat{h}(P) = \lim_{n \to \infty} \frac{h(2^n P)}{4^n}$$

其中 $h(x) = \log(\max\{|m|, |n|\})$ 为Weil高度，$x = m/n$。

**定理 2.4**（高度的性质）：

1. $\hat{h}(P) \geq 0$，且 $\hat{h}(P) = 0 \Leftrightarrow P$ 是挠点
2. $\hat{h}$ 是二次型：$\hat{h}(mP) = m^2 \hat{h}(P)$
3. 配对 $\langle P, Q \rangle = \frac{1}{2}(\hat{h}(P+Q) - \hat{h}(P) - \hat{h}(Q))$ 是半正定的

**证明框架**（Mordell-Weil定理）：

1. **弱Mordell-Weil定理**：$E(\mathbb{Q})/2E(\mathbb{Q})$ 有限
   - 利用下降（descent）和同源（isogeny）
   - 关键：$E(\mathbb{Q})/2E(\mathbb{Q}) \hookrightarrow \text{Sel}^{(2)}(E/\mathbb{Q})$

2. **高度论证**：
   - 若 $E(\mathbb{Q})$ 有无限生成元，则高度无界
   - 但高度函数控制点的"大小"

3. **有限生成**：结合弱定理与高度函数的有理性

---

## 三、BSD猜想的陈述

### 3.1 解析秩与代数秩

**定义 3.1**（Hasse-Weil L-函数）：设 $E/\mathbb{Q}$ 是椭圆曲线，定义其**L-函数**：
$$L(E, s) = \prod_{p \nmid N} \frac{1}{1 - a_p p^{-s} + p^{1-2s}} \prod_{p \mid N} \frac{1}{1 - a_p p^{-s}}$$

其中 $N$ 是导子（conductor），$a_p = p + 1 - |E(\mathbb{F}_p)|$。

**定理 3.2**（Wiles等，2001）：$L(E, s)$ 可全纯延拓到整个复平面，且满足函数方程：
$$\Lambda(E, s) = (2\pi)^{-s}\Gamma(s)N^{s/2}L(E, s) = \pm \Lambda(E, 2-s)$$

**定义 3.3**（解析秩）：定义**解析秩**为 $L(E, s)$ 在 $s = 1$ 处的零点阶：
$$r_{\text{an}} = \text{ord}_{s=1} L(E, s)$$

**定义 3.4**（代数秩）：**代数秩**定义为：
$$r_{\text{alg}} = \text{rank}(E(\mathbb{Q}))$$

**BSD猜想 I（秩部分）**：
$$r_{\text{an}} = r_{\text{alg}}$$

### 3.2 精细BSD公式

**BSD猜想 II（精细公式）**：设 $r = r_{\text{an}} = r_{\text{alg}}$，则：
$$\lim_{s \to 1} \frac{L(E, s)}{(s-1)^r} = \frac{\Omega_E \cdot \text{Reg}(E) \cdot |\text{Sha}(E)| \cdot \prod_p c_p}{|E(\mathbb{Q})_{\text{tors}}|^2}$$

其中：

- $\Omega_E = \int_{E(\mathbb{R})} \frac{dx}{|2y + a_1 x + a_3|}$：实周期

- $\text{Reg}(E) = \det(\langle P_i, P_j \rangle)$：调节子（高度配对矩阵）
- $\text{Sha}(E)$：Tate-Shafarevich群，$\text{Sha}(E) = \ker(H^1(K, E) \to \prod_v H^1(K_v, E))$
- $c_p = [E(\mathbb{Q}_p) : E^0(\mathbb{Q}_p)]$：Tamagawa数

**例 3.5**（$E: y^2 = x^3 - x$ 的BSD验证）：

- $r_{\text{alg}} = 0$，$E(\mathbb{Q}) \cong \mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/2\mathbb{Z}$
- $L(E, 1) = \frac{\Omega_E}{4} \cdot \frac{1}{4} = \frac{\Omega_E}{16}$
- 数值验证：$L(E, 1) \approx 0.6555$，$\Omega_E \approx 5.2441$

---

## 四、BSD猜想的进展

### 4.1 Coates-Wiles定理

**定理 4.1**（Coates-Wiles, 1977）：设 $E/\mathbb{Q}$ 是具有复乘（CM）的椭圆曲线，$K$ 是CM域。若 $L(E, 1) \neq 0$，则 $E(\mathbb{Q})$ 有限（即 $r_{\text{alg}} = 0$）。

**方法概述**：

- 利用椭圆单位（elliptic units）
- Iwasawa理论：构造 $p$-adic L-函数
- 证明：解析非零 $\Rightarrow$ 代数有限

**历史意义**：首个BSD部分结果，开创了Iwasawa理论方法。

### 4.2 Gross-Zagier与Kolyvagin

**定理 4.2**（Gross-Zagier, 1986）：设 $E/\mathbb{Q}$ 是模椭圆曲线，$K$ 是虚二次域满足Heegner条件。则：
$$L'(E/K, 1) = C \cdot \hat{h}(P_K)$$

其中 $P_K$ 是Heegner点，$C \neq 0$ 是显式常数。

**推论**：若 $L(E, 1) = 0$ 但 $L'(E, 1) \neq 0$，则 $r_{\text{alg}} \geq 1$。

**定理 4.3**（Kolyvagin, 1988）：设 $E$ 是模椭圆曲线，若存在Heegner点 $P_K$ 使得 $\hat{h}(P_K) \neq 0$，则：

1. $r_{\text{alg}} = 1$
2. $|\text{Sha}(E)| < \infty$

**综合结果（Kolyvagin定理）**：

对模椭圆曲线（即所有有理椭圆曲线），BSD秩猜想在以下情形成立：

- $r_{\text{an}} = 0$：$r_{\text{alg}} = 0$（由Coates-Wiles方法扩展）
- $r_{\text{an}} = 1$：$r_{\text{alg}} = 1$（由Gross-Zagier + Kolyvagin）

**现代进展（2020s）**：

| 结果 | 作者 | 内容 |
|------|------|------|
| $p$- converse定理 | Skinner-Urban | $r_{\text{alg}} = 0 \Rightarrow r_{\text{an}} = 0$ |
| 平均BSD | Bhargava-Shankar | 平均秩 $\leq 0.885$ |
| 66% BSD | Bhargava等 | 至少66%的曲线满足BSD秩猜想 |

---

## 参考文献

1. **Silverman, J.H.** (1986). *The Arithmetic of Elliptic Curves*. Springer. — 椭圆曲线算术的圣经
2. **Silverman, J.H.** (1994). *Advanced Topics in the Arithmetic of Elliptic Curves*. Springer. — 进阶主题，包括Heegner点
3. **Diamond, F. & Shurman, J.** (2005). *A First Course in Modular Forms*. Springer. — 模形式与椭圆曲线联系
4. **Washington, L.C.** (2008). *Elliptic Curves: Number Theory and Cryptography* (2nd ed.). CRC Press. — 应用视角
5. **Coates, J. & Wiles, A.** (1977). On the conjecture of Birch and Swinnerton-Dyer. *Inventiones Mathematicae*, 39(3), 223-251.
6. **Gross, B.H. & Zagier, D.B.** (1986). Heegner points and derivatives of L-series. *Inventiones Mathematicae*, 84(2), 225-320.
7. **Kolyvagin, V.A.** (1988). Finiteness of $E(\mathbb{Q})$ and $\text{Sha}(E, \mathbb{Q})$ for a subclass of Weil curves. *Math. USSR Izv.*, 32(3), 523-541.

---

*文档版本: 1.0*
*MSC2020: 11G05, 11G40*
*创建日期: 2026年4月*
*最后更新: 2026年4月*
