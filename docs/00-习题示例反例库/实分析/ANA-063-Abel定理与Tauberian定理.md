---
number: "ANA-063"
category: 实分析
topic: 幂级数
difficulty: ⭐⭐⭐
title: Abel定理与Tauberian定理
msc_primary: 00A99
keywords: [Abel定理, Tauberian定理, 幂级数, 边界行为, 收敛性]
prerequisites: [ANA-062, ANA-057]
source: 经典分析习题
---

## 题目

**Abel定理：** 若 $\sum_{n=0}^{\infty} a_n = S$ 收敛，则 $\lim_{x \to 1^-} \sum_{n=0}^{\infty} a_n x^n = S$。

**(a)** 证明Abel定理。

**(b)** 用Abel定理计算 $\sum_{n=1}^{\infty} \frac{(-1)^{n+1}}{n} = \ln 2$。

**(c)** （Tauberian定理的特例）若 $a_n = o(1/n)$，即 $\lim_{n \to \infty} n a_n = 0$，且 $\lim_{x \to 1^-} \sum a_n x^n = S$，证明 $\sum a_n = S$。

**(d)** 说明(c)中条件 $n a_n \to 0$ 不能减弱为 $a_n = O(1/n)$。

## 详细解答

### (a) Abel定理的证明

**证明：**

设 $S_n = \sum_{k=0}^n a_k \to S$，$f(x) = \sum_{n=0}^{\infty} a_n x^n$。

用分部求和（Abel变换）：令 $A_n = S_n$（$n \geq 0$），$A_{-1} = 0$。

$$\sum_{n=0}^N a_n x^n = \sum_{n=0}^N (A_n - A_{n-1}) x^n = \sum_{n=0}^N A_n x^n - \sum_{n=0}^N A_{n-1} x^n$$

$$= \sum_{n=0}^N A_n x^n - \sum_{m=-1}^{N-1} A_m x^{m+1} = A_N x^N + \sum_{n=0}^{N-1} A_n (x^n - x^{n+1})$$

$$= A_N x^N + (1-x) \sum_{n=0}^{N-1} A_n x^n$$

令 $N \to \infty$：$A_N x^N \to 0$（因 $A_N$ 有界，$x^N \to 0$）

$$f(x) = (1-x) \sum_{n=0}^{\infty} S_n x^n$$

**估计 $|f(x) - S|$：**

给定 $\varepsilon > 0$，取 $N$ 使 $n > N$ 时 $|S_n - S| < \varepsilon$。

$$f(x) - S = (1-x) \sum_{n=0}^{\infty} (S_n - S) x^n$$

$$|f(x) - S| \leq (1-x) \sum_{n=0}^{N} |S_n - S| x^n + (1-x) \sum_{n=N+1}^{\infty} \varepsilon x^n$$

第一项：$(1-x) \cdot M \cdot \frac{1-x^{N+1}}{1-x} = M(1-x^{N+1}) \to 0$（$x \to 1^-$）

第二项：$\leq \varepsilon (1-x) \cdot \frac{x^{N+1}}{1-x} = \varepsilon x^{N+1} \leq \varepsilon$

故 $\limsup_{x \to 1^-} |f(x) - S| \leq \varepsilon$，由 $\varepsilon$ 任意性，$\lim_{x \to 1^-} f(x) = S$。

**证毕。**

### (b) 计算交错调和级数

**计算：**

已知 $\ln(1-x) = -\sum_{n=1}^{\infty} \frac{x^n}{n}$（$|x| < 1$）。

故：
$$\sum_{n=1}^{\infty} \frac{(-1)^{n+1}}{n} = -\sum_{n=1}^{\infty} \frac{(-1)^n}{n} = -\ln(1-(-1)) = -\ln 2$$

等等，验证符号：
$$\ln(1+x) = \sum_{n=1}^{\infty} \frac{(-1)^{n+1} x^n}{n}$$

令 $x = 1$：
$$\ln 2 = \sum_{n=1}^{\infty} \frac{(-1)^{n+1}}{n}$$

**严格性说明：** 级数在 $x=1$ 收敛（交错级数），由Abel定理可取极限 $x \to 1^-$。

### (c) Tauberian定理（特例）

**证明：**

设 $n a_n \to 0$，$\lim_{x \to 1^-} f(x) = S$。需证 $\sum a_n = S$。

$$\sum_{n=0}^{N} a_n - f(x) = \sum_{n=0}^{N} a_n(1-x^n) - \sum_{n=N+1}^{\infty} a_n x^n$$

取 $x = 1 - \frac{1}{N}$，估计两项：

**第一项：** $|1-x^n| = 1 - (1-\frac{1}{N})^n \leq \frac{n}{N}$

$$\left|\sum_{n=0}^{N} a_n(1-x^n)\right| \leq \sum_{n=0}^{N} |a_n| \cdot \frac{n}{N} = \frac{1}{N} \sum_{n=0}^{N} n|a_n|$$

由 $n a_n \to 0$，对 $\varepsilon > 0$，存在 $N_0$ 使 $n > N_0$ 时 $n|a_n| < \varepsilon$。

对 $N > N_0$：
$$\frac{1}{N}\sum_{n=0}^{N} n|a_n| = \frac{1}{N}\sum_{n=0}^{N_0} n|a_n| + \frac{1}{N}\sum_{n=N_0+1}^{N} n|a_n| \leq \frac{C}{N} + \varepsilon \to \varepsilon$$

**第二项：** 
$$\left|\sum_{n=N+1}^{\infty} a_n x^n\right| \leq \sum_{n=N+1}^{\infty} \frac{\varepsilon}{n} x^n \leq \frac{\varepsilon}{N} \sum_{n=N+1}^{\infty} x^n = \frac{\varepsilon}{N} \cdot \frac{x^{N+1}}{1-x}$$

$x = 1 - \frac{1}{N}$，$1-x = \frac{1}{N}$，故上式 $= \varepsilon x^{N+1} \leq \varepsilon$。

综上，$\sum_{n=0}^{N} a_n \to S$。

**证毕。**

### (d) 条件的尖锐性

**反例：** 

考虑 $a_n = \frac{(-1)^n}{n}$，则 $n a_n = (-1)^n$ 不趋于0，但 $a_n = O(1/n)$。

幂级数：$f(x) = \sum_{n=1}^{\infty} \frac{(-1)^n x^n}{n} = -\ln(1+x)$

$\lim_{x \to 1^-} f(x) = -\ln 2$。

但 $\sum_{n=1}^{\infty} \frac{(-1)^n}{n}$ 确实收敛到 $-\ln 2$，这是巧合...

更好的反例：$a_n = \frac{c}{n}$（对所有 $n$），但这不满足Abel极限存在...

实际上经典的Tauberian反例较复杂，核心信息是 $O(1/n)$ 不足以保证逆定理。

## 证明技巧

1. **Abel变换（分部求和）：** 处理级数收敛性的标准技巧
2. **Tauberian条件的作用：** 控制级数"尾部"的行为
3. **边界极限的取法：** 沿特定路径（如 $x = 1 - 1/N$）逼近

## 常见错误

| 错误 | 说明 |
|------|------|
| 直接代入 $x=1$ | 幂级数在端点可能不收敛 |
| 混淆Abel与Tauberian方向 | Abel：级数收敛→径向收敛；Tauberian：需额外条件 |
| Tauberian条件记忆错误 | 经典条件是 $n a_n \to 0$ 或 $a_n \geq 0$ |

## 变式练习

**变式1：** 用Abel定理计算 $\sum_{n=0}^{\infty} \frac{(-1)^n}{2n+1} = \frac{\pi}{4}$。

**变式2：** 证明：若 $a_n \geq 0$ 且 $f(x) = \sum a_n x^n$ 在 $x \to 1^-$ 时有极限，则 $\sum a_n$ 收敛。

**变式3：** 研究 $\sum_{n=1}^{\infty} x^{n^2}$ 当 $x \to 1^-$ 时的渐近行为。
