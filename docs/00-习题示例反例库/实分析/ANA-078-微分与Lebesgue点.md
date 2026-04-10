---
exercise_id: ANA-078
title: Lebesgue微分定理与绝对连续性
difficulty: ⭐⭐⭐⭐
topics: [Lebesgue微分定理, Hardy-Littlewood极大函数, 绝对连续函数]
created: 2026-04-10
---

## 题目

设 $f \in L^1_{loc}(\mathbb{R}^n)$。

(1) 叙述 **Lebesgue微分定理**，并说明其意义；

(2) 定义 **Hardy-Littlewood极大函数** $Mf(x) = \sup_{r>0}\frac{1}{|B(x,r)|}\int_{B(x,r)}|f(y)|dy$，证明 $M$ 是弱 $(1,1)$ 型算子；

(3) 设 $F(x) = \int_a^x f(t)dt$ 对 $f \in L^1[a,b]$，证明 $F$ 绝对连续且 $F' = f$ a.e.。

## 详细解答

### (1) Lebesgue微分定理

**定理陈述**：设 $f \in L^1_{loc}(\mathbb{R}^n)$，则对几乎处处的 $x$：

$$\lim_{r \to 0} \frac{1}{|B(x,r)|}\int_{B(x,r)} f(y)dy = f(x)$$

更一般地，对a.e. $x$：

$$\lim_{r \to 0} \frac{1}{|B(x,r)|}\int_{B(x,r)} |f(y) - f(x)|dy = 0$$

这样的点称为 $f$ 的 **Lebesgue点**。

**意义**：
- 推广了微积分基本定理：积分平均在细尺度上恢复函数值
- 建立了积分与微分的联系
- 在调和分析、偏微分方程中有重要应用

**等价形式**：对任何**良好收缩**到 $x$ 的集合族 $\{E_r\}$：

$$\lim_{r \to 0} \frac{1}{|E_r|}\int_{E_r} f(y)dy = f(x)$$

### (2) 极大函数的弱 $(1,1)$ 有界性

**定理**：$M$ 是弱 $(1,1)$ 型，即：

$$|\{x : Mf(x) > \lambda\}| \leq \frac{C_n}{\lambda}\|f\|_{L^1}$$

对所有 $\lambda > 0$ 和 $f \in L^1$。

**证明**（覆盖论证）：

设 $E_\lambda = \{x : Mf(x) > \lambda\}$。

对每个 $x \in E_\lambda$，存在球 $B_x = B(x, r_x)$ 使得：

$$\frac{1}{|B_x|}\int_{B_x}|f| > \lambda$$

即 $|B_x| < \frac{1}{\lambda}\int_{B_x}|f|$。

**Vitali覆盖引理**：从 $\{B_x\}_{x \in E_\lambda}$ 中可选出不交子族 $\{B_{x_k}\}$ 使得 $E_\lambda \subset \bigcup_k 3B_{x_k}$（3倍扩张）。

因此：

$$|E_\lambda| \leq \sum_k |3B_{x_k}| = 3^n \sum_k |B_{x_k}|$$

$$< \frac{3^n}{\lambda}\sum_k \int_{B_{x_k}}|f| \leq \frac{3^n}{\lambda}\|f\|_{L^1}$$

（最后一步利用球的不交性）

因此 $C_n = 3^n$。

**注**：$M$ 不是强 $(1,1)$ 型，但 $M: L^p \to L^p$ 对 $p > 1$ 有界。

### (3) 不定积分与绝对连续性

**绝对连续性定义**：$F$ 在 $[a,b]$ 上绝对连续，若对任意 $\varepsilon > 0$，存在 $\delta > 0$ 使得对任何不交区间族 $\{(a_k, b_k)\}$：

$$\sum_k (b_k - a_k) < \delta \Rightarrow \sum_k |F(b_k) - F(a_k)| < \varepsilon$$

**证明 $F$ 绝对连续**：

$$|F(b_k) - F(a_k)| = \left|\int_{a_k}^{b_k} f\right| \leq \int_{a_k}^{b_k}|f|$$

因此：

$$\sum_k |F(b_k) - F(a_k)| \leq \sum_k \int_{a_k}^{b_k}|f| = \int_{\bigcup_k (a_k, b_k)}|f|$$

由积分的绝对连续性（$f \in L^1$），当 $|\bigcup_k (a_k, b_k)| = \sum_k (b_k - a_k) < \delta$ 时，上式 $< \varepsilon$。

**证明 $F' = f$ a.e.**：

由Lebesgue微分定理，对a.e. $x$：

$$F'(x) = \lim_{h \to 0}\frac{F(x+h) - F(x)}{h} = \lim_{h \to 0}\frac{1}{h}\int_x^{x+h}f(t)dt = f(x)$$

## 证明技巧

1. **覆盖论证**：Vitali覆盖是处理极大函数的核心工具
2. **弱型估计**：通过分布函数控制，常用于端点情况
3. **绝对连续性**：将整体性质分解为局部小量的控制

## 常见错误

| 错误类型 | 错误表现 | 正确做法 |
|---------|---------|---------|
| 极大函数性质 | 认为 $M$ 是 $L^1$ 有界 | $M$ 只是弱 $(1,1)$，$Mf \notin L^1$ 一般 |
| 微分定理范围 | 认为对所有点成立 | 只在Lebesgue点（a.e.）成立 |
| 绝对连续与有界变差 | 混淆两个概念 | 绝对连续 $
Rightarrow$ 有界变差，但逆不真 |

## 变式练习

**变式1（难度⭐⭐⭐）**：证明若 $f \in L^1_{loc}$，则 $Mf$ 下半连续。

**变式2（难度⭐⭐⭐⭐）**：设 $f$ 是有界变差函数，证明 $f$ 几乎处处可微。

**变式3（难度⭐⭐⭐⭐）**：证明 $M: L^p \to L^p$ 对 $1 < p \leq \infty$ 有界（用Marcinkiewicz插值）。
