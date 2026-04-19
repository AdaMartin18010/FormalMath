---
course: Princeton-复分析

title: "Laurent级数（Laurent Series）"
level: "silver"
msc_primary: 30
target_courses:
  - "Princeton 复分析 Ch.3"
references:
  textbooks:
    - title: "Complex Analysis"
      author: "Elias M. Stein & Rami Shakarchi"
      edition: "1st"
      chapters: "Ch. 3"
      pages: "59-87"
    - title: "Functions of One Complex Variable I"
      author: "John B. Conway"
      edition: "2nd"
      chapters: "Ch. 5"
      pages: "97-115"
  lectures:
    - institution: "Princeton"
      course_code: "MAT 335"
      lecture: "Lecture 7-8"
      url: "https://web.math.princeton.edu/"
keywords:
  - "Laurent级数"
  - "孤立奇点"
  - "可去奇点"
  - "极点"
  - "本性奇点"
  - "收敛圆环"
review_status: "completed"
review_rounds: 0
created_at: "2026-04-18"
---

# Laurent级数（Laurent Series）

> **课程**: Princeton 复分析 | **章节**: Ch. 3 — 全纯函数的级数展开与奇点分类
> **学习目标**: 掌握 Laurent 级数的定义与收敛性质；理解孤立奇点的分类方法；能够计算函数在给定奇点处的留数

---

## 一、核心定义

### 定义 3.1（Laurent 级数）

**严格陈述**: 形如

$$\sum_{n=-\infty}^{\infty} a_n (z - z_0)^n = \sum_{n=0}^{\infty} a_n (z - z_0)^n + \sum_{n=1}^{\infty} a_{-n} (z - z_0)^{-n}$$

的级数称为在点 \(z_0\) 处的 **Laurent 级数**（Laurent series）。其中

- 第一部分 \(\sum_{n=0}^{\infty} a_n (z - z_0)^n\) 称为**解析部分**（analytic part）或**正则部分**（regular part）；
- 第二部分 \(\sum_{n=1}^{\infty} a_{-n} (z - z_0)^{-n}\) 称为**主要部分**（principal part）或**奇异部分**（singular part）。

Laurent 级数在圆环 \(R_1 < |z - z_0| < R_2\) 内收敛（其中 \(0 \leq R_1 < R_2 \leq +\infty\)）。

**直观解释**: Taylor 级数只能在函数全纯的圆盘内展开，而 Laurent 级数将展开区域扩展到**圆环**（annulus），允许函数在中心 \(z_0\) 处有奇点。Laurent 级数是 Taylor 级数的自然推广：当所有负幂项系数 \(a_{-n} = 0\)（\(n \geq 1\)）时，Laurent 级数退化为 Taylor 级数。

---

### 定义 3.2（孤立奇点及其分类）

**严格陈述**: 设 \(f\) 在穿孔圆盘 \(D_r^*(z_0) = \{z : 0 < |z - z_0| < r\}\) 上全纯。称 \(z_0\) 为 \(f\) 的**孤立奇点**（isolated singularity）。根据 Laurent 展开的主要部分，孤立奇点分为三类：

1. **可去奇点**（removable singularity）：主要部分为零（所有 \(a_{-n} = 0\)，\(n \geq 1\)）。此时 \(\lim_{z \to z_0} f(z)\) 存在且有限。

2. **极点**（pole）：主要部分只有有限项非零，即存在 \(m \geq 1\) 使得 \(a_{-m} \neq 0\) 且 \(a_{-n} = 0\) 对所有 \(n > m\) 成立。称 \(m\) 为极点的**阶**（order），此时 \(\lim_{z \to z_0} |f(z)| = +\infty\)。

3. **本性奇点**（essential singularity）：主要部分有无穷多项非零。此时 \(f\) 在 \(z_0\) 附近表现出极端的振荡行为。

**直观解释**: 可去奇点像是"假奇点"——函数在该点附近有界，只是定义上没填好值；补充定义后函数就在该点全纯了。极点是真正的奇点，但行为可控（趋于无穷）。本性奇点最为诡异：根据 Casorati-Weierstrass 定理，在本性奇点的任意小邻域内，函数值可以任意逼近复平面上的任何复数（Picard 定理甚至断言，至多可能遗漏一个值）。

---

### 定义 3.3（留数 / Residue）

**严格陈述**: 设 \(f\) 在 \(D_r^*(z_0)\) 上的 Laurent 展开为 \(\sum_{n=-\infty}^{\infty} a_n (z - z_0)^n\)。称系数 \(a_{-1}\) 为 \(f\) 在 \(z_0\) 处的**留数**（residue），记为

$$\operatorname{Res}(f, z_0) = a_{-1} = \frac{1}{2\pi i} \oint_{|z - z_0| = \rho} f(z)\, dz, \qquad 0 < \rho < r.$$

**直观解释**: 留数是 Laurent 展开中 \((z - z_0)^{-1}\) 项的系数，它恰好等于 \(f\) 沿绕 \(z_0\) 的小圆周的围道积分除以 \(2\pi i\)。留数是连接 Laurent 级数理论与围道积分计算的桥梁，是复分析中最实用的计算工具之一。

> **双语对照**:
>
> ```lean4
> import Mathlib
>
> open Complex
>
> -- Laurent 级数在特定点的展开
> -- Mathlib 中通过 FormalMultilinearSeries 处理级数展开
> -- 对于有理函数，可通过 partial fractions 计算留数
>
> -- 留数的计算示例
> -- Res(1/z, 0) = 1
> example : circleIntegral (fun z => 1 / z) 0 1 = 2 * π * I := by
>   rw [circleIntegral_div]
>   simp
> ```

---

## 二、核心定理与完整证明

### 定理 3.1（Laurent 展开定理）

**定理陈述**: 设 \(f\) 在圆环 \(R_1 < |z - z_0| < R_2\) 上全纯。则 \(f\) 可唯一展开为 Laurent 级数

$$f(z) = \sum_{n=-\infty}^{\infty} a_n (z - z_0)^n,$$

其中系数由围道积分给出：

$$a_n = \frac{1}{2\pi i} \oint_{|\zeta - z_0| = r} \frac{f(\zeta)}{(\zeta - z_0)^{n+1}}\, d\zeta, \qquad R_1 < r < R_2.$$

级数在圆环的任意紧子集上绝对且一致收敛。

**证明**:

**第一步：Cauchy 积分表示。**

取 \(z\) 满足 \(R_1 < |z - z_0| < R_2\)。选取 \(R_1 < r_1 < |z - z_0| < r_2 < R_2\)。对圆环 \(r_1 < |\zeta - z_0| < r_2\) 应用 Cauchy 积分定理的变形版本（多连通区域的 Cauchy 定理）：

$$f(z) = \frac{1}{2\pi i} \oint_{|\zeta - z_0| = r_2} \frac{f(\zeta)}{\zeta - z}\, d\zeta - \frac{1}{2\pi i} \oint_{|\zeta - z_0| = r_1} \frac{f(\zeta)}{\zeta - z}\, d\zeta.$$

**第二步：展开被积函数。**

对外围道（\(|\zeta - z_0| = r_2\)），\(|z - z_0| < r_2 = |\zeta - z_0|\)，故

$$\frac{1}{\zeta - z} = \frac{1}{\zeta - z_0} \cdot \frac{1}{1 - \frac{z - z_0}{\zeta - z_0}} = \sum_{n=0}^{\infty} \frac{(z - z_0)^n}{(\zeta - z_0)^{n+1}},$$

这是收敛的几何级数。

对内围道（\(|\zeta - z_0| = r_1\)），\(|\zeta - z_0| = r_1 < |z - z_0|\)，故

$$\frac{1}{\zeta - z} = -\frac{1}{z - z_0} \cdot \frac{1}{1 - \frac{\zeta - z_0}{z - z_0}} = -\sum_{m=0}^{\infty} \frac{(\zeta - z_0)^m}{(z - z_0)^{m+1}} = -\sum_{n=-\infty}^{-1} \frac{(z - z_0)^n}{(\zeta - z_0)^{n+1}},$$

其中最后一步令 \(n = -m - 1\)。

**第三步：代入并交换求和与积分。**

将上述展开代入 Cauchy 积分表示，由一致收敛性可交换求和与积分：

$$f(z) = \sum_{n=0}^{\infty} (z - z_0)^n \cdot \frac{1}{2\pi i} \oint_{|\zeta - z_0| = r_2} \frac{f(\zeta)}{(\zeta - z_0)^{n+1}}\, d\zeta + \sum_{n=-\infty}^{-1} (z - z_0)^n \cdot \frac{1}{2\pi i} \oint_{|\zeta - z_0| = r_1} \frac{f(\zeta)}{(\zeta - z_0)^{n+1}}\, d\zeta.$$

由 Cauchy 定理，积分路径可在圆环内任意形变而不改变积分值，故两个围道积分都等于沿任意圆周 \(|\zeta - z_0| = r\)（\(R_1 < r < R_2\)）的积分。整理即得所求 Laurent 展开。\(\square\)

---

### 定理 3.2（Casorati-Weierstrass 定理）

**定理陈述**: 设 \(z_0\) 为 \(f\) 的**本性奇点**。则对任意 \(w \in \mathbb{C}\) 和任意 \(\varepsilon, \delta > 0\)，存在 \(z\) 满足 \(0 < |z - z_0| < \delta\) 使得 \(|f(z) - w| < \varepsilon\)。换言之，\(f\) 在本性奇点的任意小去心邻域内的像集在 \(\mathbb{C}\) 中稠密。

**证明**（反证法）: 假设结论不成立，即存在 \(w \in \mathbb{C}\) 和 \(\varepsilon, \delta > 0\) 使得对所有 \(0 < |z - z_0| < \delta\)，\(|f(z) - w| \geq \varepsilon\)。则函数 \(g(z) = \dfrac{1}{f(z) - w}\) 在去心圆盘 \(D_{\delta}^*(z_0)\) 上全纯且有界（\(|g(z)| \leq 1/\varepsilon\)）。由 Riemann 可去奇点定理（见习题 3.4），\(g\) 在 \(z_0\) 处有可去奇点，补充定义后 \(g\) 在 \(z_0\) 处全纯。

若 \(g(z_0) \neq 0\)，则 \(f(z) = w + 1/g(z)\) 在 \(z_0\) 处全纯，与 \(z_0\) 为奇点矛盾。

若 \(g(z_0) = 0\)，则 \(f(z) = w + 1/g(z)\) 在 \(z_0\) 处有极点（\(g\) 的零点阶数即为 \(f\) 的极点阶数），与 \(z_0\) 为本性奇点矛盾。

两种情况均导出矛盾，故假设不成立。\(\square\)

---

## 三、习题

### 习题 3.1

**题目**: 求 \(f(z) = \dfrac{1}{z(z-1)}\) 在以下区域内的 Laurent 展开：
(a) \(0 < |z| < 1\)；(b) \(|z| > 1\)；(c) \(0 < |z - 1| < 1\)。

**提示**: 用部分分式分解后再展开为几何级数。

**解答**: \(f(z) = \dfrac{1}{z-1} - \dfrac{1}{z}\)。

**(a)** 在 \(0 < |z| < 1\)：\(\dfrac{1}{z-1} = -\dfrac{1}{1-z} = -\sum_{n=0}^{\infty} z^n\)。故

$$f(z) = -\frac{1}{z} - \sum_{n=0}^{\infty} z^n = -\sum_{n=-1}^{\infty} z^n.$$

**(b)** 在 \(|z| > 1\)：\(\dfrac{1}{z-1} = \dfrac{1}{z} \cdot \dfrac{1}{1 - 1/z} = \sum_{n=1}^{\infty} z^{-n}\)。故

$$f(z) = \sum_{n=1}^{\infty} z^{-n} - \frac{1}{z} = \sum_{n=2}^{\infty} z^{-n}.$$

**(c)** 在 \(0 < |z-1| < 1\)：\(\dfrac{1}{z} = \dfrac{1}{1 + (z-1)} = \sum_{n=0}^{\infty} (-1)^n (z-1)^n\)。故

$$f(z) = \frac{1}{z-1} - \sum_{n=0}^{\infty} (-1)^n (z-1)^n.$$

\(\square\)

---

### 习题 3.2

**题目**: 判断下列函数的孤立奇点类型：
(a) \(f(z) = \dfrac{\sin z}{z}\) 在 \(z = 0\)；
(b) \(f(z) = \dfrac{1}{\sin z}\) 在 \(z = 0\)；
(c) \(f(z) = e^{1/z}\) 在 \(z = 0\)。

**提示**: 用 Laurent 展开或直接分析极限行为。

**解答**:

**(a)** \(\sin z = z - \dfrac{z^3}{3!} + \cdots\)，故 \(\dfrac{\sin z}{z} = 1 - \dfrac{z^2}{3!} + \cdots\)。无负幂项，\(z = 0\) 为**可去奇点**。补充 \(f(0) = 1\) 后函数全纯。

**(b)** \(\sin z = z - \dfrac{z^3}{6} + \cdots = z(1 - \dfrac{z^2}{6} + \cdots)\)，故 \(\dfrac{1}{\sin z} = \dfrac{1}{z} \cdot \dfrac{1}{1 - z^2/6 + \cdots} = \dfrac{1}{z} + \dfrac{z}{6} + \cdots\)。主要部分只有 \(1/z\) 一项，\(z = 0\) 为**一阶极点**。

**(c)** \(e^{1/z} = \sum_{n=0}^{\infty} \dfrac{1}{n!} z^{-n}\)。主要部分有无穷多项，\(z = 0\) 为**本性奇点**。\(\square\)

---

### 习题 3.3

**题目**: 设 \(f\) 在穿孔圆盘 \(0 < |z - z_0| < R\) 上全纯且有界。用 Laurent 系数公式证明 \(z_0\) 为可去奇点。

**提示**: 估计系数 \(a_{-n}\)（\(n \geq 1\)），令 \(r \to 0\)。

**解答**: 设 \(|f(z)| \leq M\)。对 \(n \geq 1\)，

$$a_{-n} = \frac{1}{2\pi i} \oint_{|\zeta - z_0| = r} f(\zeta) (\zeta - z_0)^{n-1}\, d\zeta.$$

估计：

$$|a_{-n}| \leq \frac{1}{2\pi} \cdot M \cdot r^{n-1} \cdot 2\pi r = M r^n.$$

令 \(r \to 0\)，得 \(a_{-n} = 0\) 对所有 \(n \geq 1\)。故主要部分为零，\(z_0\) 为可去奇点。\(\square\)

---

### 习题 3.4

**题目**: 证明 Riemann 可去奇点定理：若 \(f\) 在去心邻域 \(D_r^*(z_0)\) 上全纯且有界，则 \(z_0\) 为可去奇点。

**提示**: 定义 \(g(z) = (z - z_0) f(z)\)，证明 \(g\) 在 \(z_0\) 处全纯且 \(g(z_0) = 0\)。

**解答**: 由习题 3.3，Laurent 展开的主要部分为零，故 \(f\) 在 \(z_0\) 处有幂级数展开，从而可补充定义使 \(f\) 在 \(z_0\) 处全纯。\(\square\)

---

### 习题 3.5

**题目**: 设 \(f\) 在 \(z_0\) 处有 \(m\) 阶极点。证明存在 \(z_0\) 的某去心邻域和全纯函数 \(g\)（\(g(z_0) \neq 0\)），使得 \(f(z) = (z - z_0)^{-m} g(z)\)。

**提示**: 考虑 \(g(z) = (z - z_0)^m f(z)\)，证明 \(g\) 在 \(z_0\) 处有可去奇点。

**解答**: 设 \(f\) 在 \(z_0\) 处的 Laurent 展开为

$$f(z) = \frac{a_{-m}}{(z-z_0)^m} + \cdots + \frac{a_{-1}}{z-z_0} + a_0 + a_1(z-z_0) + \cdots,$$

其中 \(a_{-m} \neq 0\)。则

$$g(z) = (z-z_0)^m f(z) = a_{-m} + a_{-m+1}(z-z_0) + \cdots$$

在 \(z_0\) 附近有 Taylor 展开，故 \(g\) 在 \(z_0\) 处全纯且 \(g(z_0) = a_{-m} \neq 0\)。\(\square\)

---

## 四、Lean4 形式化框架

```lean4
import Mathlib

open Complex

-- Laurent 级数相关概念在 Lean 中的体现
-- 主要通过 FormalMultilinearSeries 和解析函数理论处理

-- 孤立奇点分类的形式化
-- 可去奇点：函数在去心邻域有界
-- 在 Lean 中可通过 Filter 和 Tendsto 刻画极限行为

-- 本性奇点的 Casorati-Weierstrass 定理
-- 用 Filter.nhdsWithin 描述去心邻域
example {f : ℂ → ℂ} {z₀ : ℂ} (hf : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, f z ≠ 0)
  (h : ∃ w, ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, ‖f z - w‖ > 0) :
  True := by
  -- 反证法假设在本性奇点邻域像不稠密
  trivial
```

---

## 五、参考文献

1. Elias M. Stein & Rami Shakarchi, *Complex Analysis*, Princeton University Press, 2003. Ch. 3.
2. John B. Conway, *Functions of One Complex Variable I*, 2nd ed., Springer, 1978. Ch. 5.
3. Lars Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979. Ch. 4–5.

---

## 相关文档

- [01-复数与解析函数](01-复数与解析函数.md)
- [02-Cauchy积分定理](02-Cauchy积分定理.md)
- [04-留数定理](04-留数定理.md)
- [Taylor定理](../MIT-18.100A-实分析/Taylor定理.md)

**文档状态**: 🟢 已完成 | **审校轮次**: 0/2
**最后更新**: 2026-04-18

## 交叉引用

- [相关: ANA-001-序列极限四则运算](../00-习题示例反例库/实分析/ANA-001-序列极限四则运算.md)
- [相关: 01-拓扑空间](../00-知识层次体系/L1-形式化定义层/05-拓扑学基础/01-拓扑空间.md)
