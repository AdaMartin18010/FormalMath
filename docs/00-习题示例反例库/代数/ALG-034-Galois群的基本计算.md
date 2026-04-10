---
number: "ALG-034"
category: 代数
topic: 域扩张与Galois理论
difficulty: ⭐⭐⭐
title: Galois群的基本计算
keywords: [Galois群, 自同构, 分裂域, 置换, 伽罗瓦对应]
prerequisites: [ALG-033, ALG-032]
source: 经典代数习题
---

## 题目

**(a)** 求 $\text{Gal}(\mathbb{Q}(\sqrt{2})/\mathbb{Q})$ 并确定其结构。

**(b)** 求 $\text{Gal}(\mathbb{Q}(\sqrt{2}, \sqrt{3})/\mathbb{Q})$ 并确定其结构。

**(c)** 求 $\text{Gal}(\mathbb{Q}(\omega)/\mathbb{Q})$，其中 $\omega = e^{2\pi i/3}$。

**(d)** 设 $K$ 是 $x^3 - 2$ 在 $\mathbb{Q}$ 上的分裂域，求 $\text{Gal}(K/\mathbb{Q})$。

## 详细解答

### (a) 二次扩张的Galois群

**解：**

$K = \mathbb{Q}(\sqrt{2})$，$[K : \mathbb{Q}] = 2$。

$\sigma \in \text{Gal}(K/\mathbb{Q})$ 由 $\sigma(\sqrt{2})$ 决定。

$\sqrt{2}$ 的极小多项式是 $x^2 - 2$，根为 $\pm\sqrt{2}$。

$\sigma(\sqrt{2})$ 必须是另一根，故：
- $\sigma(\sqrt{2}) = \sqrt{2}$：恒等自同构 $\text{id}$
- $\sigma(\sqrt{2}) = -\sqrt{2}$：自同构 $\sigma: a + b\sqrt{2} \mapsto a - b\sqrt{2}$

$$\text{Gal}(\mathbb{Q}(\sqrt{2})/\mathbb{Q}) = \{\text{id}, \sigma\} \cong \mathbb{Z}/2\mathbb{Z}$$

### (b) 双二次扩张的Galois群

**解：**

$K = \mathbb{Q}(\sqrt{2}, \sqrt{3})$，$[K : \mathbb{Q}] = 4$。

$\sigma \in \text{Gal}(K/\mathbb{Q})$ 由 $\sigma(\sqrt{2})$ 和 $\sigma(\sqrt{3})$ 决定。

- $\sigma(\sqrt{2}) \in \{\sqrt{2}, -\sqrt{2}\}$（2种选择）
- $\sigma(\sqrt{3}) \in \{\sqrt{3}, -\sqrt{3}\}$（2种选择）

共4个自同构：

| 自同构 | $\sqrt{2} \mapsto$ | $\sqrt{3} \mapsto$ |
|--------|-------------------|-------------------|
| $\text{id}$ | $\sqrt{2}$ | $\sqrt{3}$ |
| $\sigma$ | $-\sqrt{2}$ | $\sqrt{3}$ |
| $\tau$ | $\sqrt{2}$ | $-\sqrt{3}$ |
| $\sigma\tau$ | $-\sqrt{2}$ | $-\sqrt{3}$ |

验证：$\sigma^2 = \tau^2 = \text{id}$，$\sigma\tau = \tau\sigma$。

$$\text{Gal}(\mathbb{Q}(\sqrt{2}, \sqrt{3})/\mathbb{Q}) \cong \mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/2\mathbb{Z}$$

（Klein四元群）

### (c) 分圆扩张的Galois群

**解：**

$K = \mathbb{Q}(\omega)$，$\omega = e^{2\pi i/3}$，$[K : \mathbb{Q}] = 2$。

$\omega$ 的极小多项式是 $\Phi_3(x) = x^2 + x + 1$，根为 $\omega, \omega^2$。

$\sigma \in \text{Gal}(K/\mathbb{Q})$：
- $\sigma(\omega) = \omega$：恒等
- $\sigma(\omega) = \omega^2$：自同构 $\sigma$

注意 $\omega^2 = \bar{\omega}$（复共轭）。

$$\text{Gal}(\mathbb{Q}(\omega)/\mathbb{Q}) \cong \mathbb{Z}/2\mathbb{Z}$$

同构于 $(\mathbb{Z}/3\mathbb{Z})^\times$（分圆域的一般性质）。

### (d) 三次多项式的Galois群

**解：**

$K = \mathbb{Q}(\sqrt[3]{2}, \omega)$ 是 $x^3 - 2$ 的分裂域，$[K : \mathbb{Q}] = 6$。

$\text{Gal}(K/\mathbb{Q})$ 的阶为6。

三个根：$\alpha_1 = \sqrt[3]{2}$，$\alpha_2 = \omega\sqrt[3]{2}$，$\alpha_3 = \omega^2\sqrt[3]{2}$。

$\sigma \in \text{Gal}(K/\mathbb{Q})$ 置换三个根，给出嵌入 $\text{Gal}(K/\mathbb{Q}) \hookrightarrow S_3$。

因 $|\text{Gal}(K/\mathbb{Q})| = 6 = |S_3|$，故：

$$\text{Gal}(K/\mathbb{Q}) \cong S_3$$

**具体描述：**

生成元：
- $\sigma: \sqrt[3]{2} \mapsto \omega\sqrt[3]{2}$，$\omega \mapsto \omega$（3-循环）
- $\tau: \sqrt[3]{2} \mapsto \sqrt[3]{2}$，$\omega \mapsto \omega^2$（对换，复共轭）

关系：$\sigma^3 = \tau^2 = \text{id}$，$\tau\sigma\tau = \sigma^{-1}$。

## 证明技巧

1. **Galois群的计算：** 自同构由生成元的像决定，像必须是共轭元
2. **置换表示：** Galois群嵌入根的置换群
3. **群结构的确定：** 计算阶数、找生成元、验证关系

## 常见错误

| 错误 | 说明 |
|------|------|
| 忘记验证自同构的存在性 | 需要证明特定映射确实延拓为自同构 |
| 混淆Galois群与中间域 | 中间域对应子群 |
| 认为所有扩张都是Galois的 | 需要正规且可分 |

## 变式练习

**变式1：** 求 $\text{Gal}(\mathbb{Q}(\sqrt[4]{2}, i)/\mathbb{Q})$。

**变式2：** 证明 $\text{Gal}(\mathbb{Q}(\zeta_n)/\mathbb{Q}) \cong (\mathbb{Z}/n\mathbb{Z})^\times$。

**变式3：** 设 $f(x)$ 是4次不可约多项式，讨论其Galois群的可能结构。
