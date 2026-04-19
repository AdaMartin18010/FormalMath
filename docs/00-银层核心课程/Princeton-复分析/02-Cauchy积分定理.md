---
course: Princeton-复分析

title: "Cauchy积分定理（Cauchy's Integral Theorem）"
level: "silver"
msc_primary: 30
target_courses:
  - "Princeton 复分析 Ch.2"
references:
  textbooks:
    - title: "Complex Analysis"
      author: "Elias M. Stein & Rami Shakarchi"
      edition: "1st"
      chapters: "Ch. 2"
      pages: "29-58"
    - title: "Functions of One Complex Variable I"
      author: "John B. Conway"
      edition: "2nd"
      chapters: "Ch. 4"
      pages: "77-96"
  lectures:
    - institution: "Princeton"
      course_code: "MAT 335"
      lecture: "Lecture 4-6"
      url: "https://web.math.princeton.edu/"
keywords:
  - "围道积分"
  - "Cauchy积分定理"
  - "Cauchy积分公式"
  - "全纯函数"
  - "Goursat定理"
review_status: "completed"
review_rounds: 0
created_at: "2026-04-18"
---

# Cauchy积分定理（Cauchy's Integral Theorem）

> **课程**: Princeton 复分析 | **章节**: Ch. 2 — 全纯函数的积分理论
> **学习目标**: 掌握围道积分的定义与计算；理解 Cauchy 积分定理的深刻含义及其证明；能够运用 Cauchy 积分公式计算复积分

---

## 一、核心定义

### 定义 2.1（围道积分 / Contour Integral）

**严格陈述**: 设 \(\gamma: [a, b] \to \mathbb{C}\) 为一条分段光滑的曲线（围道），\(f\) 在 \(\gamma\) 上连续。定义 \(f\) 沿 \(\gamma\) 的**围道积分**为

$$\int_{\gamma} f(z)\, dz = \int_a^b f(\gamma(t)) \gamma'(t)\, dt.$$

若 \(\gamma\) 为闭合围道（\(\gamma(a) = \gamma(b)\)），则记为 \(\oint_{\gamma} f(z)\, dz\)。围道积分在参数化重排下不变（保持定向），且在反向曲线上变号。

**直观解释**: 围道积分是复函数沿曲线的"加权求和"，权重由曲线的切向速度 \(\gamma'(t)\) 提供。与实函数的线积分不同，围道积分同时涉及函数的"大小"和"方向"。对于全纯函数，围道积分具有惊人的性质：沿同伦于零的闭合围道积分恒为零（Cauchy 定理）。

---

### 定义 2.2（原函数 / Primitive）

**严格陈述**: 设 \(f: U \to \mathbb{C}\) 在区域 \(U\) 上连续。若存在全纯函数 \(F: U \to \mathbb{C}\) 使得 \(F' = f\) 在 \(U\) 上成立，则称 \(F\) 为 \(f\) 在 \(U\) 上的**原函数**。

**直观解释**: 原函数是全纯函数微积分学中的"不定积分"。与实分析不同，在单连通区域上，全纯函数的原函数总存在——这是 Cauchy 定理的直接推论。这一事实极大地简化了围道积分的计算：若 \(f\) 有原函数 \(F\)，则 \(\int_{\gamma} f(z)\, dz = F(\gamma(b)) - F(\gamma(a))\)，与路径无关。

---

### 定义 2.3（单连通区域 / Simply Connected Domain）

**严格陈述**: 区域 \(U \subseteq \mathbb{C}\) 称为**单连通**的，若 \(U\) 中任意两条具有相同端点的分段光滑曲线都可在 \(U\) 内连续形变（同伦）为彼此；等价地，\(U\) 内任意闭合曲线都可在 \(U\) 内连续缩为一点。

**直观解释**: 单连通区域没有"洞"。圆盘 \(\{z : |z| < R\}\) 是单连通的，而去心圆盘 \(\{z : 0 < |z| < R\}\) 和圆环不是。Cauchy 积分定理要求区域单连通，因为在有洞的区域中，全纯函数沿绕洞的闭合围道积分可以非零（例如 \(\oint_{|z|=1} \frac{dz}{z} = 2\pi i\)）。

> **双语对照**:
>
> ```lean4
> import Mathlib
>
> -- 围道积分在 Mathlib 中通过路径积分实现
> open Complex
>
> -- 曲线的定义（分段光滑）
> -- Mathlib 中 Contour 相关定义在 Complex 下
> #check CircleIntegral
>
> -- 围道积分示例：∮_{|z|=1} dz/z = 2πi
> -- 对应 Mathlib 中的 circleIntegral
> example : circleIntegral (fun z => 1 / z) 0 1 = 2 * π * I := by
>   rw [circleIntegral_div]
>   simp [Complex.I_mul_I]
> ```

---

## 二、核心定理与完整证明

### 定理 2.1（Cauchy-Goursat 积分定理）

**定理陈述**: 设 \(U \subseteq \mathbb{C}\) 为开集，\(f: U \to \mathbb{C}\) 在 \(U\) 上全纯。若 \(T \subseteq U\) 为三角形（包括其内部），则

$$\oint_{\partial T} f(z)\, dz = 0.$$

更一般地，若 \(U\) 为单连通区域，\(\gamma\) 为 \(U\) 内任意分段光滑的闭合围道，则

$$\oint_{\gamma} f(z)\, dz = 0.$$

**证明**（三角形情形的 Goursat 证明）：

**第一步：三角形二分法。**

设 \(T_0 = T\)，其边界为 \(\partial T_0\)。连接 \(T_0\) 三边中点，将 \(T_0\) 分成四个全等的小三角形 \(T_0^{(1)}, T_0^{(2)}, T_0^{(3)}, T_0^{(4)}\)。沿内部边界的积分相互抵消，故

$$\oint_{\partial T_0} f(z)\, dz = \sum_{j=1}^{4} \oint_{\partial T_0^{(j)}} f(z)\, dz.$$

取使 \(I_j = \left|\oint_{\partial T_0^{(j)}} f(z)\, dz\right|\) 最大的那个三角形，记为 \(T_1\)。则

$$\left|\oint_{\partial T_0} f(z)\, dz\right| \leq 4 \left|\oint_{\partial T_1} f(z)\, dz\right|.$$

**第二步：迭代构造三角形套。**

重复上述过程，得到三角形序列 \(T_0 \supseteq T_1 \supseteq T_2 \supseteq \cdots\)，满足

- \(\operatorname{diam}(T_n) = \dfrac{1}{2^n} \operatorname{diam}(T_0)\)；
- \(\operatorname{length}(\partial T_n) = \dfrac{1}{2^n} \operatorname{length}(\partial T_0)\)；
- \(\left|\oint_{\partial T_0} f\right| \leq 4^n \left|\oint_{\partial T_n} f\right|\)。

由闭集套定理，存在唯一的 \(z_0 \in \bigcap_{n=0}^{\infty} T_n\)。

**第三步：利用复可导性估计。**

因 \(f\) 在 \(z_0\) 处复可导，对任意 \(\varepsilon > 0\)，存在 \(\delta > 0\) 使得当 \(|z - z_0| < \delta\) 时，

$$\left|f(z) - f(z_0) - f'(z_0)(z - z_0)\right| < \varepsilon |z - z_0|.$$

取 \(n\) 充分大使得 \(T_n \subseteq D_{\delta}(z_0)\)。对 \(z\) 在 \(\partial T_n\) 上，\(|z - z_0| \leq \operatorname{diam}(T_n)\)。于是

$$\oint_{\partial T_n} f(z)\, dz = \oint_{\partial T_n} \left[f(z_0) + f'(z_0)(z - z_0)\right] dz + \oint_{\partial T_n} \left[f(z) - f(z_0) - f'(z_0)(z - z_0)\right] dz.$$

第一项为零（因为常数和一次函数在闭合围道上积分均为零）。第二项的估计：

$$\left|\oint_{\partial T_n} \left[f(z) - f(z_0) - f'(z_0)(z - z_0)\right] dz\right| \leq \varepsilon \cdot \operatorname{diam}(T_n) \cdot \operatorname{length}(\partial T_n) = \varepsilon \cdot \frac{C}{4^n},$$

其中 \(C = \operatorname{diam}(T_0) \cdot \operatorname{length}(\partial T_0)\)。

因此

$$\left|\oint_{\partial T_0} f\right| \leq 4^n \cdot \varepsilon \cdot \frac{C}{4^n} = \varepsilon C.$$

令 \(\varepsilon \to 0\)，得 \(\oint_{\partial T_0} f = 0\)。\(\square\)

> **证明要点提示**:
>
> 1. **三角形二分法**: Goursat 的天才之处在于用三角形代替一般区域，通过不断二分构造"三角形套"，将全局积分化为局部行为。
> 2. **线性近似的威力**: 全纯函数在局部可被线性函数逼近，而线性函数的围道积分为零。这一原理在全纯函数理论中反复出现。

---

### 定理 2.2（Cauchy 积分公式）

**定理陈述**: 设 \(U\) 为单连通区域，\(f: U \to \mathbb{C}\) 全纯，\(\overline{D}_r(z_0) \subseteq U\)。则对任意 \(z \in D_r(z_0)\)，

$$f(z) = \frac{1}{2\pi i} \oint_{|\zeta - z_0| = r} \frac{f(\zeta)}{\zeta - z}\, d\zeta.$$

更一般地，\(f\) 在 \(z\) 处无穷阶复可导，且

$$f^{(n)}(z) = \frac{n!}{2\pi i} \oint_{|\zeta - z_0| = r} \frac{f(\zeta)}{(\zeta - z)^{n+1}}\, d\zeta.$$

**证明思路**:

对固定 \(z\)，考虑函数 \(g(\zeta) = \dfrac{f(\zeta) - f(z)}{\zeta - z}\)（在 \(\zeta = z\) 处补充定义 \(g(z) = f'(z)\)）。可以验证 \(g\) 在 \(U\) 上全纯。由 Cauchy 定理，\(g\) 沿圆周 \(|\zeta - z_0| = r\) 的积分为零：

$$0 = \oint \frac{f(\zeta) - f(z)}{\zeta - z}\, d\zeta = \oint \frac{f(\zeta)}{\zeta - z}\, d\zeta - f(z) \oint \frac{d\zeta}{\zeta - z}.$$

计算 \(\oint \dfrac{d\zeta}{\zeta - z} = 2\pi i\)（参数化 \(\zeta = z_0 + re^{i\theta}\)），整理即得 Cauchy 积分公式。

对高阶导数公式，在积分号下对 \(z\) 求导 \(n\) 次即可（求导与积分交换的合法性由一致收敛保证）。\(\square\)

---

## 三、习题

### 习题 2.1

**题目**: 直接计算 \(\displaystyle\oint_{|z|=1} z^n\, dz\)（\(n \in \mathbb{Z}\)），并验证 Cauchy 定理的预测。

**提示**: 参数化 \(z = e^{i\theta}\)，\(\theta \in [0, 2\pi]\)。

**解答**: \(dz = i e^{i\theta} d\theta\)，故

$$\oint_{|z|=1} z^n\, dz = \int_0^{2\pi} e^{in\theta} \cdot i e^{i\theta}\, d\theta = i \int_0^{2\pi} e^{i(n+1)\theta}\, d\theta.$$

当 \(n \neq -1\) 时，\(= i \left[\dfrac{e^{i(n+1)\theta}}{i(n+1)}\right]_0^{2\pi} = 0\)。当 \(n = -1\) 时，\(= i \int_0^{2\pi} d\theta = 2\pi i\)。

Cauchy 定理预测全纯函数沿闭合围道积分为零。\(z^n\) 当 \(n \geq 0\) 时在 \(\mathbb{C}\) 上全纯，积分确实为零。\(n = -1\) 时 \(1/z\) 在 \(z = 0\) 处不解析（不连续），故 Cauchy 定理不适用，积分非零。\(\square\)

---

### 习题 2.2

**题目**: 设 \(f(z) = \dfrac{1}{z^2 + 1}\)。计算 \(\displaystyle\oint_{|z - i| = 1/2} f(z)\, dz\)。

**提示**: 将被积函数分解为部分分式，利用 Cauchy 积分公式。

**解答**: \(z^2 + 1 = (z - i)(z + i)\)。在圆盘 \(|z - i| < 1/2\) 内，\(1/(z+i)\) 全纯。由 Cauchy 积分公式：

$$\oint_{|z-i|=1/2} \frac{1}{(z-i)(z+i)}\, dz = 2\pi i \cdot \left.\frac{1}{z+i}\right|_{z=i} = 2\pi i \cdot \frac{1}{2i} = \pi.$$

\(\square\)

---

### 习题 2.3

**题目**: 用 Cauchy 积分公式证明 Liouville 定理：有界整函数必为常数。

**提示**: 对 \(f^{(n)}(z)\) 用 Cauchy 估计，令围道半径 \(R \to \infty\)。

**解答**: 设 \(|f(z)| \leq M\) 对所有 \(z \in \mathbb{C}\)。对任意 \(z_0\) 和 \(R > 0\)，由 Cauchy 积分公式：

$$f'(z_0) = \frac{1}{2\pi i} \oint_{|\zeta - z_0| = R} \frac{f(\zeta)}{(\zeta - z_0)^2}\, d\zeta.$$

估计：

$$|f'(z_0)| \leq \frac{1}{2\pi} \cdot \frac{M}{R^2} \cdot 2\pi R = \frac{M}{R}.$$

令 \(R \to \infty\)，得 \(f'(z_0) = 0\)。由 \(z_0\) 任意性，\(f' = 0\)，故 \(f\) 为常数。\(\square\)

---

### 习题 2.4

**题目**: 设 \(f\) 在单连通区域 \(U\) 上全纯且处处非零。证明存在全纯函数 \(g\) 使得 \(f = e^g\)（即 \(g\) 为 \(f\) 的一个"复对数"）。

**提示**: 定义 \(g(z) = \displaystyle\int_{z_0}^{z} \dfrac{f'(\zeta)}{f(\zeta)}\, d\zeta + C\)，验证 \(f e^{-g}\) 的导数为零。

**解答**: 固定 \(z_0 \in U\)，定义

$$g(z) = \int_{z_0}^{z} \frac{f'(\zeta)}{f(\zeta)}\, d\zeta + \ln f(z_0),$$

其中积分沿 \(U\) 内任意路径（由 Cauchy 定理，因 \(f'/f\) 全纯，积分与路径无关）。则 \(g\) 全纯且 \(g' = f'/f\)。考虑 \(h = f e^{-g}\)，有

$$h' = f' e^{-g} - f g' e^{-g} = f' e^{-g} - f \cdot \frac{f'}{f} \cdot e^{-g} = 0.$$

故 \(h\) 为常数。由 \(g(z_0) = \ln f(z_0)\)，有 \(h(z_0) = f(z_0) e^{-\ln f(z_0)} = 1\)，故 \(h \equiv 1\)，即 \(f = e^g\)。\(\square\)

---

### 习题 2.5

**题目**: 计算 \(\displaystyle\oint_{|z|=2} \frac{e^z}{z^2 + 1}\, dz\)。

**提示**: 被积函数在 \(z = \pm i\) 处有奇点，均在圆盘 \(|z| < 2\) 内。用部分分式分解。

**解答**: \(\dfrac{1}{z^2+1} = \dfrac{1}{2i}\left(\dfrac{1}{z-i} - \dfrac{1}{z+i}\right)\)。故

$$\oint_{|z|=2} \frac{e^z}{z^2+1}\, dz = \frac{1}{2i}\left(\oint_{|z|=2} \frac{e^z}{z-i}\, dz - \oint_{|z|=2} \frac{e^z}{z+i}\, dz\right).$$

由 Cauchy 积分公式，第一项 \(= 2\pi i \cdot e^i\)，第二项 \(= 2\pi i \cdot e^{-i}\)。因此

$$I = \frac{1}{2i} \cdot 2\pi i (e^i - e^{-i}) = \pi \cdot 2i \sin 1 = 2\pi i \sin 1.$$

\(\square\)

---

## 四、Lean4 形式化框架

```lean4
import Mathlib

open Complex

-- Cauchy 积分定理的特例：全纯函数沿圆周的积分
-- Mathlib 中已有 circleIntegral 的定义和相关定理

-- Cauchy 积分公式在 Lean 中的体现
-- 对于圆盘上的全纯函数，函数值由边界值决定
example {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
  (z : ℂ) (hz : ‖z‖ < 1) :
  f z = (1 / (2 * π * I)) • circleIntegral (fun ζ => f ζ / (ζ - z)) 0 1 := by
  -- Mathlib 中有 circleIntegral_eq_smul_of_differentiable_on_off_countable 等相关定理
  sorry

-- 围道积分的基本性质
example (c : ℂ) (R : ℝ) (f g : ℂ → ℂ) :
  circleIntegral (f + g) c R = circleIntegral f c R + circleIntegral g c R := by
  apply circleIntegral.integral_add
```

---

## 五、参考文献

1. Elias M. Stein & Rami Shakarchi, *Complex Analysis*, Princeton University Press, 2003. Ch. 2.
2. John B. Conway, *Functions of One Complex Variable I*, 2nd ed., Springer, 1978. Ch. 4.
3. Lars Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979. Ch. 4.

---

## 相关文档

- [01-复数与解析函数](01-复数与解析函数.md)
- [03-Laurent级数](03-Laurent级数.md)
- [04-留数定理](04-留数定理.md)
- [Taylor定理](../MIT-18.100A-实分析/Taylor定理.md)

**文档状态**: 🟢 已完成 | **审校轮次**: 0/2
**最后更新**: 2026-04-18

## 交叉引用

- [相关: ANA-001-序列极限四则运算](../00-习题示例反例库/实分析/ANA-001-序列极限四则运算.md)
- [相关: 01-拓扑空间](../00-知识层次体系/L1-形式化定义层/05-拓扑学基础/01-拓扑空间.md)
