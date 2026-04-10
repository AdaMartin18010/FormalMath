---
number: "ALG-035"
category: 代数
topic: 域扩张与Galois理论
difficulty: ⭐⭐⭐
title: Galois对应（伽罗瓦对应）基本定理
keywords: [Galois对应, 子群, 中间域, 固定域, 基本定理]
prerequisites: [ALG-034, ALG-033]
source: 经典代数习题
---

## 题目

设 $K/F$ 是有限Galois扩张，$G = \text{Gal}(K/F)$。

**Galois对应基本定理：**

子群 $H \leq G$ $\longleftrightarrow$ 中间域 $E$（$F \subset E \subset K$）

- $H \mapsto K^H = \{x \in K : \sigma(x) = x, \forall \sigma \in H\}$（固定域）
- $E \mapsto \text{Gal}(K/E) = \{\sigma \in G : \sigma|_E = \text{id}\}$

**(a)** 证明上述对应是互逆的：$K^{\text{Gal}(K/E)} = E$，$\text{Gal}(K/K^H) = H$。

**(b)** 证明：$H_1 \leq H_2 \Leftrightarrow K^{H_2} \subset K^{H_1}$（反包含）。

**(c)** 证明：$[K : K^H] = |H|$，$[K^H : F] = [G : H]$。

**(d)** 对 $K = \mathbb{Q}(\sqrt{2}, \sqrt{3})$，$F = \mathbb{Q}$，写出完整的Galois对应。

## 详细解答

### (a) 互逆性

**证明：**

**步骤1：** $E \subset K^{\text{Gal}(K/E)}$

对任意 $x \in E$，$\sigma \in \text{Gal}(K/E)$，由定义 $\sigma(x) = x$。

故 $x \in K^{\text{Gal}(K/E)}$。

**步骤2：** $K^{\text{Gal}(K/E)} \subset E$（关键！）

设 $\alpha \in K^{\text{Gal}(K/E)}$，需证 $\alpha \in E$。

设 $f(x)$ 是 $\alpha$ 在 $E$ 上的极小多项式，次数为 $d = [E(\alpha) : E]$。

Galois群的元素将 $\alpha$ 映到其共轭元，这些共轭元都在 $K$ 中。

$\text{Gal}(K/E)$ 固定 $E$ 中元素，故 $\sigma(\alpha)$ 也是 $f$ 的根，对所有 $\sigma \in \text{Gal}(K/E)$。

因 $\alpha \in K^{\text{Gal}(K/E)}$，$\sigma(\alpha) = \alpha$ 对所有 $\sigma \in \text{Gal}(K/E)$。

故 $\text{Gal}(K/E)$ 只提供一个根，即 $\alpha$ 是 $f$ 的唯一根，$d = 1$，$\alpha \in E$。

**步骤3：** $H \subset \text{Gal}(K/K^H)$

对任意 $\sigma \in H$，$x \in K^H$，由定义 $\sigma(x) = x$。

故 $\sigma$ 固定 $K^H$，$\sigma \in \text{Gal}(K/K^H)$。

**步骤4：** $\text{Gal}(K/K^H) \subset H$

设 $E = K^H$，则 $H \subset \text{Gal}(K/E)$。

由步骤2的同样论证，$[K : E] = |\text{Gal}(K/E)|$。

由Artin定理，$[K : K^H] = |H|$。

故 $|H| = [K : K^H] = [K : E] = |\text{Gal}(K/E)|$。

$H \subset \text{Gal}(K/E)$ 且基数相等，故相等。

**证毕。**

### (b) 包含关系的反转

**证明：**

**($\Rightarrow$)** 设 $H_1 \leq H_2$。

$K^{H_2} = \{x : \sigma(x) = x, \forall \sigma \in H_2\}$。

对 $x \in K^{H_2}$，$\sigma \in H_1 \subset H_2$，有 $\sigma(x) = x$。

故 $x \in K^{H_1}$，$K^{H_2} \subset K^{H_1}$。

**($\Leftarrow$)** 设 $K^{H_2} \subset K^{H_1}$。

$\text{Gal}(K/K^{H_2}) \supset \text{Gal}(K/K^{H_1})$。

由(a)，$H_2 \supset H_1$。

**证毕。**

### (c) 次数公式

**证明：**

**步骤1：** $[K : K^H] = |H|$

这是Artin定理的直接推论。

**步骤2：** $[K^H : F] = [G : H]$

由塔律：
$$[K : F] = [K : K^H] \cdot [K^H : F]$$

因 $K/F$ Galois，$[K : F] = |G|$。

$$|G| = |H| \cdot [K^H : F]$$

故 $[K^H : F] = \frac{|G|}{|H|} = [G : H]$。

**证毕。**

### (d) $\mathbb{Q}(\sqrt{2}, \sqrt{3})$ 的Galois对应

**已知：** $G = \text{Gal}(K/\mathbb{Q}) = \{\text{id}, \sigma, \tau, \sigma\tau\} \cong \mathbb{Z}_2 \times \mathbb{Z}_2$

其中：
- $\sigma(\sqrt{2}) = -\sqrt{2}$，$\sigma(\sqrt{3}) = \sqrt{3}$
- $\tau(\sqrt{2}) = \sqrt{2}$，$\tau(\sqrt{3}) = -\sqrt{3}$

**子群格：**

- $G$（4阶）
- $\langle\sigma\rangle = \{\text{id}, \sigma\}$（2阶）
- $\langle\tau\rangle = \{\text{id}, \tau\}$（2阶）
- $\langle\sigma\tau\rangle = \{\text{id}, \sigma\tau\}$（2阶）
- $\{\text{id}\}$（1阶）

**Galois对应：**

| 子群 $H$ | 固定域 $K^H$ | 扩张次数 $[K^H : \mathbb{Q}]$ |
|----------|-------------|---------------------------|
| $G$ | $\mathbb{Q}$ | 4 |
| $\langle\sigma\rangle$ | $\mathbb{Q}(\sqrt{3})$ | 2 |
| $\langle\tau\rangle$ | $\mathbb{Q}(\sqrt{2})$ | 2 |
| $\langle\sigma\tau\rangle$ | $\mathbb{Q}(\sqrt{6})$ | 2 |
| $\{\text{id}\}$ | $K$ | 1 |

**验证：** $\sigma\tau(\sqrt{6}) = \sigma\tau(\sqrt{2}\sqrt{3}) = (-\sqrt{2})(-\sqrt{3}) = \sqrt{6}$。✓

## 证明技巧

1. **Galois对应的验证：** 证明两个映射互逆是核心
2. **Artin定理的应用：** $[K : K^H] = |H|$ 是计算的关键
3. **具体例子的对应：** 从子群格出发，计算固定域

## 常见错误

| 错误 | 说明 |
|------|------|
| 混淆包含方向 | 子群越大，固定域越小 |
| 忘记验证中间域 | 需要确认固定域的形式 |
| 次数计算错误 | $[K:K^H] = |H|$ 而非 $[K^H:F] = |H|$ |

## 变式练习

**变式1：** 对 $x^3 - 2$ 的分裂域，写出完整的Galois对应。

**变式2：** 证明中间域 $E/F$ 正规当且仅当对应子群 $H$ 是 $G$ 的正规子群。

**变式3：** 设 $K/F$ 是$p$次循环扩张（$p$素数），证明中间域只有$K$和$F$。
