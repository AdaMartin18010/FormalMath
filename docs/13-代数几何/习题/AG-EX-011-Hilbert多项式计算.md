---
习题编号: AG-EX-011
标题: Hilbert多项式计算
类型: 代数型
难度: ⭐⭐⭐⭐
章节: Hartshorne Ch III
对应课程: Harvard Math 232br
预计用时: 90-120分钟
msc: 13D40, 14C05
---

# AG-EX-011: Hilbert多项式计算

## 题目

### 原题 (Hartshorne III.5.1)

设 $X \subseteq \mathbb{P}^n$ 是闭子概形，$\mathcal{F}$ 是凝聚层。

**(a)** 定义Hilbert函数 $h(m) = \dim_k H^0(X, \mathcal{F}(m))$。证明对 $m \gg 0$，$h(m)$ 是多项式（Hilbert多项式）。

**(b)** 对 $X = \mathbb{P}^n$，$\mathcal{F} = \mathcal{O}_X$，计算Hilbert多项式。

**(c)** 对 $X = V(f) \subseteq \mathbb{P}^n$ 是次数为 $d$ 的超曲面，计算 $P_X(m)$。

### 计算题目

设 $X \subseteq \mathbb{P}^3$ 是 $(2, 3)$-型完全交曲线。

**(a)** 计算 $X$ 的Hilbert多项式。

**(b)** 计算 $X$ 的算术亏格 $p_a(X)$。

**(c)** 验证 $P_X(0) = \chi(\mathcal{O}_X)$。

---

## 解答

### 主题目解答

#### (a) Hilbert多项式的存在性

**证明概要**:

**Step 1**: 对射影空间本身。

$H^0(\mathbb{P}^n, \mathcal{O}(m)) = S_m$（$m$次齐次多项式）。

$$\dim S_m = \binom{m+n}{n} = \frac{m^n}{n!} + \cdots$$

这是 $n$ 次多项式。

**Step 2**: 一般情形用归纳。

对短正合列:
$$0 \to \mathcal{F}(m-1) \xrightarrow{\cdot f} \mathcal{F}(m) \to \mathcal{F}|_H(m) \to 0$$

其中 $H$ 是超平面。

取上同调的长正合列，$h(m) - h(m-1)$ 满足归纳假设。

故 $h(m)$ 是多项式。

---

#### (b) $\mathbb{P}^n$ 的Hilbert多项式

**计算**:

$$P_{\mathbb{P}^n}(m) = \binom{m+n}{n} = \frac{(m+n)(m+n-1)\cdots(m+1)}{n!}$$

展开:
$$P_{\mathbb{P}^n}(m) = \frac{m^n}{n!} + \frac{(n+1)m^{n-1}}{2(n-1)!} + \cdots + 1$$

**特例**:
- $n = 1$: $P(m) = m + 1$
- $n = 2$: $P(m) = \frac{(m+2)(m+1)}{2} = \frac{m^2}{2} + \frac{3m}{2} + 1$

---

#### (c) 超曲面的Hilbert多项式

设 $X = V(f) \subseteq \mathbb{P}^n$，$\deg(f) = d$。

**正合列**:
$$0 \to \mathcal{O}_{\mathbb{P}^n}(m-d) \xrightarrow{\cdot f} \mathcal{O}_{\mathbb{P}^n}(m) \to \mathcal{O}_X(m) \to 0$$

**Hilbert函数**:
$$h_X(m) = h_{\mathbb{P}^n}(m) - h_{\mathbb{P}^n}(m-d)$$

$$= \binom{m+n}{n} - \binom{m-d+n}{n}$$

**多项式**:

对 $m \geq d$:
$$P_X(m) = \binom{m+n}{n} - \binom{m-d+n}{n}$$

**特例** ($n = 2$，平面曲线):

$$P_X(m) = \binom{m+2}{2} - \binom{m-d+2}{2}$$

$$= \frac{(m+2)(m+1)}{2} - \frac{(m-d+2)(m-d+1)}{2}$$

$$= dm + 1 - \frac{(d-1)(d-2)}{2}$$

---

### 计算题目解答

#### (a) 完全交曲线的Hilbert多项式

设 $X = Q \cap C \subseteq \mathbb{P}^3$，其中:
- $Q$ 是二次曲面
- $C$ 是三次曲面

**理想**: $I_X = (f_2, f_3)$，$\deg(f_2) = 2$，$\deg(f_3) = 3$。

**自由分解**:
$$0 \to \mathcal{O}(-5) \to \mathcal{O}(-2) \oplus \mathcal{O}(-3) \to \mathcal{O} \to \mathcal{O}_X \to 0$$

**Hilbert函数**:

$$h_X(m) = h_{\mathbb{P}^3}(m) - h_{\mathbb{P}^3}(m-2) - h_{\mathbb{P}^3}(m-3) + h_{\mathbb{P}^3}(m-5)$$

**Hilbert多项式**:

$$P_X(m) = \binom{m+3}{3} - \binom{m+1}{3} - \binom{m}{3} + \binom{m-2}{3}$$

展开:
- $\binom{m+3}{3} = \frac{m^3 + 6m^2 + 11m + 6}{6}$
- $\binom{m+1}{3} = \frac{m^3 - m}{6}$
- $\binom{m}{3} = \frac{m^3 - 3m^2 + 2m}{6}$
- $\binom{m-2}{3} = \frac{m^3 - 9m^2 + 26m - 24}{6}$

合并:
$$P_X(m) = \frac{1}{6}[(m^3 + 6m^2 + 11m + 6) - (m^3 - m) - (m^3 - 3m^2 + 2m) + (m^3 - 9m^2 + 26m - 24)]$$

$$= \frac{1}{6}[6m + 6 - 24] = m - 3 + 6 = 6m - 3$$

等等，让我重新计算：

实际上对曲线 ($\dim = 1$)，Hilbert多项式应为一次:

$$P_X(m) = (\deg X) \cdot m + (1 - p_a)$$

对 $(2,3)$-完全交，$\deg(X) = 2 \cdot 3 = 6$。

由Riemann-Roch对曲线:
$$P_X(m) = 6m + 1 - g$$

需要计算 $g$（亏格）。

**由完全交公式**:

$(d_1, d_2)$-完全交在 $\mathbb{P}^3$ 的亏格:
$$g = \frac{1}{2}d_1d_2(d_1 + d_2 - 4) + 1$$

$$g = \frac{1}{2} \cdot 2 \cdot 3 \cdot (2 + 3 - 4) + 1 = 3 \cdot 1 + 1 = 4$$

故:
$$P_X(m) = 6m + 1 - 4 = 6m - 3$$

验证 $P_X(0) = -3$... 这不对。

让我重新推导：对曲线，$P_X(m) = h^0(\mathcal{O}_X(m))$ 对 $m \gg 0$。

由Riemann-Roch:
$$h^0(L) - h^1(L) = \deg(L) + 1 - g$$

对 $L = \mathcal{O}_X(m)$，$\deg(L) = m \cdot \deg(X) = 6m$。

对 $m \gg 0$，$h^1(L) = 0$（Serre消没）。

故 $P_X(m) = 6m + 1 - g = 6m + 1 - 4 = 6m - 3$。

但 $P_X(0) = -3$，而 $\chi(\mathcal{O}_X) = 1 - g = -3$。一致！

---

#### (b) 算术亏格

**定义**: $p_a(X) = (-1)^{\dim X}(P_X(0) - 1)$

对曲线:
$$p_a = -(P_X(0) - 1) = -(-3 - 1) = 4$$

或用:
$$p_a = g = 4$$

---

#### (c) 验证 $\chi(\mathcal{O}_X) = P_X(0)$

$$\chi(\mathcal{O}_X) = h^0(\mathcal{O}_X) - h^1(\mathcal{O}_X) = 1 - g = 1 - 4 = -3$$

$$P_X(0) = -3$$

**结论**: $\chi(\mathcal{O}_X) = P_X(0) = -3$ ✓

---

## 解题技巧

### 技巧1: Hilbert多项式速算

```
┌─────────────────────────────────────────┐
│  Hilbert多项式 P(m) 的性质:             │
│  1. deg(P) = dim(X)                     │
│  2. (dim X)! · 首项系数 = deg(X)        │
│  3. P(0) = χ(O_X)                       │
│  4. 对 m < 0: P(m) = (-1)^dim h^{dim}   │
└─────────────────────────────────────────┘
```

### 技巧2: 完全交公式

对 $(d_1, \ldots, d_r)$-完全交在 $\mathbb{P}^n$:

$$P_X(m) = \sum_{S \subseteq [r]} (-1)^{|S|} \binom{m - \sum_{i \in S}d_i + n}{n}$$

### 技巧3: 平面曲线亏格

$\mathbb{P}^2$ 中光滑 $d$ 次曲线:
$$g = \frac{(d-1)(d-2)}{2}$$

---

## 变式与推广

### 变式1: 一般完全交

计算 $(2, 2, 2)$-完全交曲面在 $\mathbb{P}^5$ 的Hilbert多项式。

---

### 变式2: 射影丛

设 $X = \mathbb{P}(\mathcal{E})$ 是向量丛的射影化。

**问题**: 用Riemann-Roch计算Hilbert多项式。

---

### 变式3: Hilbert概形

**定义**: Hilbert概形 $H_{P, \mathbb{P}^n}$ 参数化 $\mathbb{P}^n$ 中Hilbert多项式为 $P$ 的子概形。

**问题**: 描述 $H_{m+1, \mathbb{P}^3}$（直线）。

---

## 相关概念

| 概念 | 定义 | 符号 |
|:---|:---|:---:|
| Hilbert函数 | 截面维数 | $h(m)$ |
| Hilbert多项式 | 渐近多项式 | $P(m)$ |
| 算术亏格 | $P(0) - 1$ | $p_a$ |
| 完全交 | 由余维数个方程定义 | - |

## 参考文献

1. Hartshorne, R. *Algebraic Geometry*, Ch III, §5
2. Eisenbud, D. *Commutative Algebra*, Ch 12
3. Harris, J. *Algebraic Geometry*, Ch 13

---

**创建日期**: 2026-04-10  
**难度**: ⭐⭐⭐⭐  
**预计用时**: 90-120分钟
