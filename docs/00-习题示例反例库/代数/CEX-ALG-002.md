---
id: CEX-ALG-002
category: 代数
topic: 环论
concept: 单位元与零因子
title: 无逆元的环元素（零因子）
difficulty: 中等
keywords: [零因子, 单位元, 整环, 可逆元, 环]
related: [CEX-ALG-003]
---

# CEX-ALG-002: 无逆元的环元素（零因子）

## 反例构造

考虑环 $R = \mathbb{Z}/6\mathbb{Z} = \{0, 1, 2, 3, 4, 5\}$（模6剩余类环），乘法为模6乘法。

考察元素 $\bar{2} \in R$：
- 存在 $\bar{3} \in R$ 使得 $\bar{2} \cdot \bar{3} = \bar{6} = \bar{0}$
- 但 $\bar{2} \neq \bar{0}$ 且 $\bar{3} \neq \bar{0}$

## 反例分析

**证明 $\bar{2}$ 无乘法逆元：**

假设存在 $\bar{x} \in R$ 使得 $\bar{2} \cdot \bar{x} = \bar{1}$。

这等价于 $2x \equiv 1 \pmod{6}$，即 $2x = 6k + 1$ 对某个整数 $k$。

左边 $2x$ 是偶数，右边 $6k + 1$ 是奇数，矛盾！

**零因子与不可逆的关系：**

$$\bar{2} \cdot \bar{3} = \bar{0}, \quad \bar{2} \neq \bar{0}, \quad \bar{3} \neq \bar{0}$$

若 $\bar{2}$ 可逆，设逆为 $\bar{2}^{-1}$，则：
$$\bar{3} = \bar{2}^{-1} \cdot \bar{2} \cdot \bar{3} = \bar{2}^{-1} \cdot \bar{0} = \bar{0}$$
矛盾！

## 直观解释

**零因子的本质：** 在 $\mathbb{Z}/6\mathbb{Z}$ 中，数字2和3都不是"零"，但它们相乘却得到"零"。这就像两个非零的数"合作"消灭了对方。

**钟表类比：** 想象一个6小时制的钟表。
- 从0开始，每次+2，经过3次回到0（$2+2+2=6\equiv 0$）
- 从0开始，每次+3，经过2次回到0（$3+3=6\equiv 0$）

这说明2和3在模6意义下有"周期性归零"的特性，因此无法找到逆元（逆元需要"撤销"操作，但零因子有多个原像）。

**与整数环的对比：** 在 $\mathbb{Z}$ 中，只有 $\pm 1$ 可逆，但没有零因子（因为若 $ab=0$ 则 $a=0$ 或 $b=0$）。模 $n$ 环当 $n$ 为合数时才会出现零因子。

## 相关定理

**定理（零因子不可逆）**
> 若 $R$ 是含幺环，$a \in R$ 是左零因子（即存在 $b \neq 0$ 使 $ab = 0$），则 $a$ 无左逆元。

说明：这是本例的核心原理——零因子与可逆性互斥。

**定理（整环的单位群）**
> 若 $R$ 是整环（无零因子的交换含幺环），则 $R^\times = R \setminus \{0\}$ 当且仅当 $R$ 是域。

说明：$\mathbb{Z}/6\mathbb{Z}$ 不是整环（有零因子），因此 $(\mathbb{Z}/6\mathbb{Z})^\times \subsetneq (\mathbb{Z}/6\mathbb{Z}) \setminus \{0\}$。

**定理（有限整环是域）**
> 有限整环必为域。

说明：本例中 $\mathbb{Z}/6\mathbb{Z}$ 不是整环，因此即使有限也不是域。

## 避免此反例的条件

| 条件 | 结论 | 例子 |
|------|------|------|
| $R$ 是域 | 所有非零元可逆 | $\mathbb{Q}, \mathbb{R}, \mathbb{C}, \mathbb{Z}/p\mathbb{Z}$（$p$ 素数） |
| $R$ 是整环 | 无零因子 | $\mathbb{Z}, \mathbb{Z}[i]$ |
| $n$ 是素数 | $\mathbb{Z}/n\mathbb{Z}$ 是域 | $\mathbb{Z}/5\mathbb{Z}$ 中 $\bar{2}^{-1} = \bar{3}$ |
| $R$ 是除环 | 非零元都可逆 | 四元数环 $\mathbb{H}$ |
| $\gcd(a, n) = 1$ | $\bar{a}$ 在 $\mathbb{Z}/n\mathbb{Z}$ 中可逆 | 在 $\mathbb{Z}/6\mathbb{Z}$ 中，$\bar{5}$ 可逆 |

**可逆元判定（模 $n$ 环）：**
$$\bar{a} \in (\mathbb{Z}/n\mathbb{Z})^\times \iff \gcd(a, n) = 1$$

在 $\mathbb{Z}/6\mathbb{Z}$ 中：$(\mathbb{Z}/6\mathbb{Z})^\times = \{\bar{1}, \bar{5}\}$
