---
msc_primary: 00A99
习题编号: GEO-071
学科: 几何
知识点: 几何-Yamabe问题
难度: ⭐⭐⭐⭐
预计时间: 50分钟
---

# Yamabe 问题

## 题目

**(a)** 证明 Yamabe 泛函的共形不变性。

**(b)** 讨论 Aubin-Schoen 的完备解。

**(c)** 证明紧致情况下的解的存在性。

---

## 解答

### (a) Yamabe泛函

#### 定义

设 $(M, g)$ 是 $n$ 维紧Riemann流形（$n \geq 3$）。

**Yamabe泛函**：
$$Q(u) = \frac{\int_M \left(\frac{4(n-1)}{n-2}|\nabla u|^2 + R u^2\right) dV_g}{\left(\int_M u^{\frac{2n}{n-2}} dV_g\right)^{\frac{n-2}{n}}}$$

其中 $u > 0$ 光滑。

**共形变换**：$\tilde{g} = u^{\frac{4}{n-2}} g$。

#### 共形不变性

**定理**：$Q(u)$ 只依赖于共形类 $[g]$。

**证明**：设 $\tilde{g} = u^{\frac{4}{n-2}} g$，则：
- $\tilde{R} = u^{-\frac{n+2}{n-2}}\left(-\frac{4(n-1)}{n-2}\Delta u + Ru\right)$
- $dV_{\tilde{g}} = u^{\frac{2n}{n-2}} dV_g$

直接计算验证 $Q_{\tilde{g}}(1) = Q_g(u)$。

$\square$

#### Yamabe常数

$$Y(M, [g]) = \inf_{u > 0} Q(u)$$

---

### (b) Aubin-Schoen解

#### Yamabe方程

极值点 $u$ 满足**Yamabe方程**：
$$-\frac{4(n-1)}{n-2}\Delta u + Ru = \lambda u^{\frac{n+2}{n-2}}$$

其中 $\lambda = Y(M, [g])$。

#### Aubin定理

**定理**（Aubin, 1976）：
$$Y(M, [g]) \leq Y(S^n, g_{std})$$

且若严格不等式成立，则Yamabe方程有正解。

**证明**：用test function集中在小球上，局部类似于 $S^n$。

#### Schoen的解决

**定理**（Schoen, 1984）：若 $Y(M, [g]) = Y(S^n)$，则 $(M, g)$ 共形等价于 $S^n$。

**证明**：用**正质量定理**（Schoen-Yau）。

若 $Y(M) = Y(S^n)$ 但 $M$ 不共形于 $S^n$，则在Universal cover上构造渐近平坦度量，其ADM质量为0。

由正质量定理，这必须是平坦的，矛盾。

$\square$

---

### (c) 紧致存在性

#### 总结

**定理**（Yamabe, Aubin, Schoen, Trudinger）：任意紧Riemann流形 $(M, g)$（$n \geq 3$）存在共形度量 $\tilde{g} = u^{\frac{4}{n-2}}g$ 使得标量曲率 $R_{\tilde{g}}$ 是常数。

#### 证明策略

1. **$Y(M) < Y(S^n)$**：Aubin的变分法直接得到解
2. **$Y(M) = Y(S^n)$**：Schoen用正质量定理
3. **$Y(M) > Y(S^n)$**：不可能（由Aubin的不等式）

#### 历史

- 1960：Yamabe提出，但证明有gap
- 1976：Aubin解决 $Y(M) < Y(S^n)$ 情形
- 1984：Schoen完全解决