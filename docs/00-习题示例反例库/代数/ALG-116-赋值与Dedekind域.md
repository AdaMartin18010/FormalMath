---
msc_primary: 00A99
习题编号: ALG-116
学科: 代数
知识点: 代数数论-Dedekind域
难度: ⭐⭐⭐⭐
预计时间: 30分钟
---

# 赋值与Dedekind域

## 题目

**Dedekind域**：整闭、Noether、素理想非零即极大的整环。

(a) 证明Dedekind域中每个非零理想唯一分解为素理想的乘积。

(b) 设 $K$ 是数域，证明 $\mathcal{O}_K$ 是Dedekind域。

(c) 设 $\mathfrak{p} \subset \mathcal{O}_K$ 是素理想，定义 $\mathfrak{p}$-adic赋值：
$$v_\mathfrak{p}(x) = \max\{n : x \in \mathfrak{p}^n\}$$
证明这是离散赋值，并描述其赋值环。

## 解答

### (a) 理想的唯一分解

**证明：**

**存在性**：

对非零理想 $I$，考虑所有不能分解为素理想乘积的理想集合。

若有此集合，由Noether性，有极大元 $J$。

$J$ 非素，故存在 $a,b \notin J$ 使 $ab \in J$。

$J \subsetneq J + (a)$，$J \subsetneq J + (b)$。

由极大性，两者可分解，故 $J$ 可分解，矛盾。

**唯一性**：

设 $\mathfrak{p}_1 \cdots \mathfrak{p}_r = \mathfrak{q}_1 \cdots \mathfrak{q}_s$。

$\mathfrak{p}_1 \supset \mathfrak{q}_1 \cdots \mathfrak{q}_s$。

由素性，$\mathfrak{p}_1 \supset \mathfrak{q}_1$，故 $\mathfrak{p}_1 = \mathfrak{q}_1$（极大性）。

消去，归纳得唯一性。$\square$

### (b) 整数环是Dedekind域

**证明：**

**整闭**：$\mathcal{O}_K$ 定义上是整闭的。

**Noether**：作为有限生成 $\mathbb{Z}$-模，是Noether。

**维数1**：

素理想对应素元（理想的素分解）。

$\mathfrak{p} \cap \mathbb{Z} = (p)$ 是素数。

$\mathcal{O}_K/\mathfrak{p}$ 是 $\mathbb{F}_p$ 的有限扩张，故是域。

因此非零素理想极大。$\square$

### (c) $\mathfrak{p}$-adic赋值

**证明：**

**离散赋值**：

$v_\mathfrak{p}: K^* \to \mathbb{Z}$。

- $v_\mathfrak{p}(xy) = v_\mathfrak{p}(x) + v_\mathfrak{p}(y)$：理想乘法的赋值加性。

- $v_\mathfrak{p}(x+y) \geq \min(v_\mathfrak{p}(x), v_\mathfrak{p}(y))$：理想包含。

**赋值环**：

$R_\mathfrak{p} = \{x \in K : v_\mathfrak{p}(x) \geq 0\}$

$= \mathcal{O}_{K,\mathfrak{p}}$（$\mathcal{O}_K$ 于 $\mathfrak{p}$ 的局部化）。

这是DVR（离散赋值环），极大理想 $\mathfrak{p}R_\mathfrak{p}$。

$\square$

## 证明技巧

1. **Noether归纳**：理想分解的存在性
2. **整扩张的素理想**：维数控制
3. **局部化与赋值**：DVR的几何解释

## 常见错误

- ❌ 忘记唯一性证明中的消去步骤
- ❌ 混淆Dedekind域与PID
- ❌ 赋值环忘记包含0

## 变式练习

**变式1：** 证明PID是Dedekind域。

**变式2：** 计算 $\mathbb{Q}(i)$ 中 $(5)$ 的素理想分解。
