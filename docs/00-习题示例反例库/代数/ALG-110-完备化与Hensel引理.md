---
习题编号: ALG-110
学科: 代数
知识点: 交换代数-完备化
难度: ⭐⭐⭐⭐
预计时间: 35分钟
---

# 完备化与Hensel引理

## 题目

设 $(R, \mathfrak{m})$ 是Noether局部环，**$\mathfrak{m}$-adic完备化**：
$$\hat{R} = \varprojlim R/\mathfrak{m}^n$$

(a) 证明 $\hat{R}$ 是平坦 $R$-代数，且 $\hat{R}$ 是局部环，极大理想为 $\mathfrak{m}\hat{R}$。

(b) 证明Hensel引理：设 $R$ 是 $\mathfrak{m}$-adic完备的，$f \in R[x]$。

若存在 $a \in R$ 使得 $f(a) \equiv 0 \pmod{\mathfrak{m}}$，$f'(a) \not\equiv 0 \pmod{\mathfrak{m}}$，则存在唯一的 $\alpha \in R$ 使得 $f(\alpha) = 0$，$\alpha \equiv a \pmod{\mathfrak{m}}$。

(c) 应用：证明 $\mathbb{Z}_p$ 中每个单位是 $(p-1)$-次单位根的提升。

## 解答

### (a) 完备化的基本性质

**证明：**

**平坦性**：

$\hat{R}$ 作为逆向极限，平坦性来自：

$M \mapsto \hat{M} = \varprojlim M/\mathfrak{m}^n M$ 是正合函子（对有限生成模）。

由Noether性，$\hat{R} \otimes_R M \cong \hat{M}$。

**局部性**：

$\hat{R}/\mathfrak{m}\hat{R} \cong R/\mathfrak{m}$ 是域。

对 $x \in \hat{R} \setminus \mathfrak{m}\hat{R}$，像于 $R/\mathfrak{m}$ 非零，故可逆。

用几何级数提升可逆性。$\square$

### (b) Hensel引理

**证明（Newton迭代）**：

定义序列：
$$a_{n+1} = a_n - \frac{f(a_n)}{f'(a_n)}$$

**Step 1**：良定性。

由 $f'(a) \not\equiv 0 \pmod{\mathfrak{m}}$，$f'(a)$ 可逆。

**Step 2**：收敛性。

设 $f(a_n) \equiv 0 \pmod{\mathfrak{m}^{2^n}}$。

Taylor展开：
$$f(a_{n+1}) = f(a_n) + f'(a_n)(a_{n+1} - a_n) + \cdots$$

$$= f(a_n) - f'(a_n) \frac{f(a_n)}{f'(a_n)} + O(f(a_n)^2) = O(f(a_n)^2)$$

因此 $f(a_{n+1}) \equiv 0 \pmod{\mathfrak{m}^{2^{n+1}}}$。

**Step 3**：极限。

$\{a_n\}$ 是Cauchy列，收敛到 $\alpha \in R$（完备性）。

$f(\alpha) = \lim f(a_n) = 0$。$\square$

### (c) $p$-进单位根

**证明**：

设 $u \in \mathbb{Z}_p^\times$。

考虑 $f(x) = x^{p-1} - 1$。

于 $\mathbb{F}_p$，$f$ 有 $p-1$ 个根（乘法群循环）。

设 $\bar{a} \in \mathbb{F}_p$ 是本原元，$f(\bar{a}) = 0$，$f'(\bar{a}) = (p-1)\bar{a}^{p-2} \neq 0$。

由Hensel引理，存在唯一的 $a \in \mathbb{Z}_p$ 使得 $a^{p-1} = 1$，$a \equiv \bar{a} \pmod{p}$。

因此 $\mathbb{Z}_p$ 包含所有 $(p-1)$-次单位根。$\square$

## 证明技巧

1. **逆向极限**：完备化的范畴论定义
2. **Newton迭代**：二次收敛的快速算法
3. **Taylor展开**：$p$-进分析中的多项式逼近

## 常见错误

- ❌ 忘记验证完备化的Noether性
- ❌ Hensel条件中导数非零模极大理想
- ❌ $p$-进绝对值与模 $p$ 的混淆

## 变式练习

**变式1：** 证明 $\mathbb{Z}_p$ 中平方数的判定准则。

**变式2：** 用Hensel引理分解 $x^2 - 2$ 于 $\mathbb{Q}_7$。
