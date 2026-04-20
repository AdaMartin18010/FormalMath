---
msc_primary: 20

  - 20A99
  - 00A99
  - 00A99
  - 03B35
title: Fermat 小定理 - 工作示例
processed_at: '2026-04-05'
---
# Fermat 小定理 - 工作示例

**类型**: 证明示例 **领域**: 数论 **难度**: L1 **创建日期**: 2026年2月2日

---

## 元信息

| 属性 | 内容 |
|------|------|
| **主题** | 若 \(p\) 为素数、\(p \nmid a\) 则 \(a^{p-1} \equiv 1 \pmod{p}\) |
| **领域** | 数论 |
| **MSC** | 11A07 |

---

## 一、定义与理论背景

### 1.1 模运算与同余

设 \(m \geq 2\) 为整数。若 \(m \mid (a-b)\)，记 \(a \equiv b \pmod{m}\)，称为 **\(a\) 与 \(b\) 模 \(m\) 同余**。同余关系是等价关系，且保持加法和乘法。

### 1.2 模 \(p\) 乘法群

设 \(p\) 为素数。记 \((\mathbb{Z}/p\mathbb{Z})^\times = \{\overline{1}, \overline{2}, \ldots, \overline{p-1}\}\)，即模 \(p\) 的既约剩余类。这是 **\(p-1\) 阶循环群**，由原根生成。

---

## 二、核心定理

### 定理 2.1（Fermat 小定理）

设 \(p\) 为素数，\(a \in \mathbb{Z}\) 且 \(p \nmid a\)。则：

$$
a^{p-1} \equiv 1 \pmod{p}
$$

等价形式：对任意 \(a \in \mathbb{Z}\)，有 \(a^p \equiv a \pmod{p}\)。

### 定理 2.2（Euler 定理，推广）

设 \(n \geq 2\)，\(\gcd(a,n) = 1\)。记 Euler 函数 \(\varphi(n) = |(\mathbb{Z}/n\mathbb{Z})^\times|\)。则：

$$
a^{\varphi(n)} \equiv 1 \pmod{n}
$$

当 \(n = p\) 为素数时，\(\varphi(p) = p-1\)，即得 Fermat 小定理。

### 定理 2.3（Wilson 定理，对偶）

\(p\) 为素数当且仅当 \((p-1)! \equiv -1 \pmod{p}\)。

---

## 三、证明过程

### 证法一：Lagrange 定理（群论）

\(G = (\mathbb{Z}/p\mathbb{Z})^\times\) 是 \(p-1\) 阶乘法群。由条件 \(p \nmid a\) 知 \(\overline{a} \in G\)。根据 **Lagrange 定理**：群中任意元素的阶整除群的阶。故 \(\overline{a}^{p-1} = \overline{1}\)，即 \(a^{p-1} \equiv 1 \pmod{p}\)。

### 证法二：组合计数（初等）

考虑 \(p\) 元集合上的染色问题：用 \(a\) 种颜色对正 \(p\) 边形的顶点染色。旋转等价的染色视为相同。由 Burnside 引理或轨道计数，非单色染色类数为：

$$
\frac{a^p - a}{p}
$$

这必须是整数，故 \(p \mid (a^p - a)\)。

### 证法三：数学归纳法

对 \(a\) 用归纳法。\(a = 1\) 显然。设 \(a^p \equiv a \pmod{p}\)，则：

$$
(a+1)^p = \sum_{k=0}^{p} \binom{p}{k} a^k \equiv a^p + 1 \equiv a + 1 \pmod{p}
$$

因为 \(p \mid \binom{p}{k}\) 对 \(1 \leq k \leq p-1\) 成立。

---

## 四、题目与完整解答

### 题目

证明 Fermat 小定理。

### 完整解答

**证法（群论视角，最简洁）**：

设 \(p\) 为素数，\(p \nmid a\)。考虑模 \(p\) 乘法群：

$$
G = (\mathbb{Z}/p\mathbb{Z})^\times = \{\overline{a} : 1 \leq a \leq p-1\}
$$

\(|G| = p-1\)。因 \(p \nmid a\)，故 \(\overline{a} \in G\)。由 Lagrange 定理，元素 \(\overline{a}\) 的阶 \(d = \operatorname{ord}_p(a)\) 满足 \(d \mid |G| = p-1\)。设 \(p-1 = d \cdot m\)，则：

$$
a^{p-1} = (a^d)^m \equiv 1^m = 1 \pmod{p}
$$

证毕。

---

## 五、应用与拓展

### 5.1 素性测试

- **Fermat 测试**：若 \(a^{n-1} \not\equiv 1 \pmod{n}\)，则 \(n\) 必为合数
- **伪素数**：满足 \(2^{n-1} \equiv 1 \pmod{n}\) 的合数 \(n\) 称为以 2 为底的伪素数
- **Carmichael 数**：对所有与 \(n\) 互素的 \(a\) 都满足 Fermat 小定理的合数（如 561 = 3×11×17）

### 5.2 RSA 加密

RSA 算法基于 Euler 定理：设 \(n = pq\)，\(ed \equiv 1 \pmod{\varphi(n)}\)。对明文 \(m\)：

$$
(m^e)^d = m^{ed} = m^{1 + k\varphi(n)} \equiv m \pmod{n}
$$

Fermat 小定理是这一原理的素数特例。

### 5.3 计算应用

大数模幂可用**快速幂算法**（平方-乘算法）在 \(O(\log p)\) 时间内计算 \(a^{p-1} \bmod p\)。

---

**文档状态**: ✅ 完成 **最后更新**: 2026年4月20日
