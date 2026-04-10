---
习题编号: TOP-056
学科: 拓扑
知识点: 代数拓扑-Poincare对偶
难度: ⭐⭐⭐⭐⭐
预计时间: 40分钟
---

# Poincaré对偶性

## 题目

设 $M$ 是 $n$ 维闭可定向流形。

**(a)** 证明Poincaré对偶：存在基本类 $[M] \in H_n(M)$ 使得：
$$\frown [M]: H^k(M) \to H_{n-k}(M)$$
是同构。

**(b)** 证明上同调版本：$H^k(M) \cong H^{n-k}(M)^*$。

**(c)** 计算 $H^*(\mathbb{C}P^n)$ 的环结构，用Poincaré对偶验证。

## 解答

### (a) Poincaré对偶

**证明概要**：

**基本类**：

$M$ 可定向，局部定向整体相容。

$H_n(M) = \mathbb{Z}$，生成元 $[M]$。

**帽积**：
$\frown: H^k(M) \times H_n(M) \to H_{n-k}(M)$。

**局部验证**：

对 $M = \mathbb{R}^n$，$H^k(\mathbb{R}^n) = 0$（$k>0$），显然。

对 $M = S^n$，直接计算验证。

**Mayer-Vietoris论证**：

用开覆盖归纳，局部对偶性拼成整体。

由五引理，对偶映射是同构。$\square$

### (b) 上同调对偶

**证明**：

由万有系数：
$H_{n-k}(M) \cong H^{n-k}(M)^* \oplus \text{Ext}(H^{n-k-1}(M), \mathbb{Z})$。

闭流形，无挠（或适当处理）。

$H^k(M) \cong H_{n-k}(M) \cong H^{n-k}(M)^*$。$\square$

### (c) $\mathbb{C}P^n$ 的计算

**结果**：

$H^*(\mathbb{C}P^n) = \mathbb{Z}[x]/(x^{n+1})$，$|x| = 2$。

**Poincaré对偶验证**：

$\dim \mathbb{C}P^n = 2n$。

对偶配对：$H^{2k} \times H^{2n-2k} \to H^{2n} = \mathbb{Z}$。

$x^k \smile x^{n-k} = x^n$。

生成 $H^{2n}$，配对非退化。$\square$

## 证明技巧

1. **基本类的局部构造**
2. **Mayer-Vietoris归纳**
3. **杯积与帽积的关系**

## 常见错误

- ❌ 忘记可定向条件
- ❌ 边界与闭流形的混淆
- ❌ 对偶映射的方向

## 变式练习

**变式1：** 证明非可定向流形的$\mathbb{Z}/2$对偶。

**变式2：** 计算 $H^*(\mathbb{H}P^n)$。
