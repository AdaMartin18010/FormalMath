---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# IMO 2006 Problem 6

## 题目

设 $a, b, c$ 是一个三角形的三边长。证明：
$$\sqrt{a+b-c} + \sqrt{b+c-a} + \sqrt{c+a-b} \leq \sqrt{a} + \sqrt{b} + \sqrt{c}$$

并确定等号成立的条件。

## 分类

- **领域**: 代数（不等式）
- **难度**: 4分
- **关键词**: 三角形不等式、根式不等式、代换法、Jensen不等式

## 解答

### 分析

这是一个关于三角形边长的不等式，涉及平方根。观察特点：

1. 由三角形不等式，$a+b-c > 0$ 等，所以根号内为正
2. 具有对称性
3. 形式类似于某种"三角不等式"

### 证明

**方法1：代换法**

设 $x = b+c-a$，$y = c+a-b$，$z = a+b-c$。

由三角形不等式，$x, y, z > 0$。

解出：
$$a = \frac{y+z}{2}, \quad b = \frac{z+x}{2}, \quad c = \frac{x+y}{2}$$

原不等式变为：
$$\sqrt{x} + \sqrt{y} + \sqrt{z} \leq \sqrt{\frac{y+z}{2}} + \sqrt{\frac{z+x}{2}} + \sqrt{\frac{x+y}{2}}$$

即需证明：
$$\sum_{cyc} \sqrt{x} \leq \sum_{cyc} \sqrt{\frac{y+z}{2}}$$

由AM-GM不等式：
$$\sqrt{\frac{y+z}{2}} \geq \frac{\sqrt{y} + \sqrt{z}}{2}$$

（这由 $(\sqrt{y}-\sqrt{z})^2 \geq 0$ 展开得到）

因此：
$$\sum_{cyc} \sqrt{\frac{y+z}{2}} \geq \sum_{cyc} \frac{\sqrt{y}+\sqrt{z}}{2} = \sqrt{x} + \sqrt{y} + \sqrt{z}$$

等号成立当且仅当 $x = y = z$，即 $a = b = c$（等边三角形）。

**方法2：Jensen不等式**

函数 $f(t) = \sqrt{t}$ 是凹函数。利用Jensen不等式：

$$\sqrt{a+b-c} = \sqrt{2a - (a+b+c) + 2b + 2c - 2b - 2c + a+b-c}...$$

此方法较复杂，不如代换法简洁。

**方法3：直接平方**

设 $S = \sqrt{a+b-c} + \sqrt{b+c-a} + \sqrt{c+a-b}$，$T = \sqrt{a} + \sqrt{b} + \sqrt{c}$。

计算 $S^2$ 和 $T^2$ 并比较。此方法计算量较大。

### 结论

不等式成立，等号当且仅当 $\boxed{a = b = c}$（三角形为等边三角形）时成立。

## 数学概念

### 核心概念

1. **三角形代换（Ravi代换）**
   设 $a = y+z$，$b = z+x$，$c = x+y$（或本题的变体），将三角形边长条件转化为正变量条件。

2. **凹函数与Jensen不等式**
   对于凹函数 $f$：$f\left(\frac{x+y}{2}\right) \geq \frac{f(x)+f(y)}{2}$

3. **AM-GM不等式**
   $$\frac{x+y}{2} \geq \sqrt{xy}$$

### 与FormalMath主项目的链接

- [三角形不等式](../../concept/algebra/triangle-inequalities.md)
- [Ravi代换](../../concept/algebra/ravi-substitution.md)
- [Jensen不等式](../../concept/algebra/jensen-inequality.md)
- [凸函数与凹函数](../../concept/analysis/convex-functions.md)

## 变体与推广

### 变体1（幂次推广）

对于 $p \in (0, 1]$，证明：
$$(a+b-c)^p + (b+c-a)^p + (c+a-b)^p \leq a^p + b^p + c^p$$

### 变体2（加权形式）

对于正权重 $w_1, w_2, w_3$，研究加权不等式。

### 推广（n维）

对于 $n$ 维单形的棱长，类似的周长型不等式。

## 参考

- [IMO 2006 Official Solutions](https://www.imo-official.org/problems/IMO2006SL.pdf)
- [AoPS讨论贴](https://artofproblemsolving.com/community/c6h101493p572827)
- 相关技巧：Ravi代换、三角形边长不等式

---

*解答整理：FormalMath项目团队*
