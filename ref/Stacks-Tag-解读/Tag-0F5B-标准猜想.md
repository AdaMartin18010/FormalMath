# Stacks Project Tag 0F5B - 标准猜想

## 1. 基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 0F5B |
| **英文名称** | Standard Conjectures on Algebraic Cycles |
| **所属章节** | Motives |
| **主题分类** | 代数几何 - 代数循环 |
| **创建日期** | 2026-04-10 |
| **版本** | v1.0 |

---

## 2. 核心概念与定义

### 2.1 历史背景与重要性

**标准猜想**（Standard Conjectures）由Grothendieck在1960年代末提出，是代数几何中最重要的未解决问题之一。它们是建立**纯动机**范畴的公理基础，也是证明**Hodge猜想**等深层问题的关键。

> "Alongside the conjecture of Hodge and Tate, the standard conjectures are the most pressing needs of algebraic geometry."
> — Alexander Grothendieck

**核心问题**：

1. 代数循环是否「足够多」以解释所有上同调现象？
2. Lefschetz算子是否由代数循环给出？

### 2.2 Lefschetz算子

**定义 2.2.1**（超平面截面）
设 $X \subset \mathbb{P}^N$ 是光滑射影簇，$L = c_1(\mathcal{O}(1)|_X)$ 是超平面类的上同调类。

**定义 2.2.2**（Lefschetz算子）
**Lefschetz算子**定义为杯积：
$$L: H^i(X) \to H^{i+2}(X), \quad \alpha \mapsto L \cup \alpha$$

**定义 2.2.3**（Hard Lefschetz定理）
对于光滑射影簇 $X$，$\dim X = d$：
$$L^{d-i}: H^i(X) \xrightarrow{\sim} H^{2d-i}(X)$$
对所有 $i \leq d$ 是同构。

**定义 2.2.4**（原始上同调）
**原始上同调**定义为：
$$P^i(X) := \ker(L^{d-i+1}: H^i(X) \to H^{2d-i+2}(X))$$

### 2.3 Lefschetz型标准猜想

**猜想 2.3.1**（标准猜想B：Lefschetz型）
**B(X)**：存在代数循环 $\Lambda \in \text{CH}^{d-1}(X \times X)$ 诱导的**Lefschetz逆算子**：
$$\Lambda: H^i(X) \to H^{i-2}(X)$$
是 $L$ 的逆（在原始部分）。

等价表述：算子
$$*_L: H^i(X) \to H^{2d-i}(X)$$
由代数循环给出。

**猜想 2.3.2**（标准猜想C：Lefschetz分解）
**C(X)**：Hard Lefschetz同构由代数循环给出，且Lefschetz分解：
$$H^i(X) = \bigoplus_{j \geq 0} L^j P^{i-2j}(X)$$
是「 motivic 」的。

### 2.4 Hodge型标准猜想

**猜想 2.4.1**（标准猜想I：Künneth型）
**I(X)**：Künneth分解：
$$[\Delta_X] = \sum_{i=0}^{2d} \pi_i \in H^{2d}(X \times X)$$
其中 $\pi_i$ 是**代数循环**（在有理等价下）。

等价地，投影到第 $i$ 个上同调：
$$H^*(X) \to H^i(X)$$
由代数对应给出。

**猜想 2.4.2**（标准猜想D：同调与数值等价的等价）
**D(X)**：在代数循环上，**同调等价**与**数值等价**一致：
$$\alpha \sim_{\text{hom}} 0 \Leftrightarrow \alpha \sim_{\text{num}} 0$$

**定义 2.4.3**（数值等价）
循环 $\alpha \in \text{CH}^r(X)$ **数值等价**于零，如果对任意 $\beta \in \text{CH}^{d-r}(X)$：
$$\deg(\alpha \cdot \beta) = 0$$

### 2.5 正性猜想

**猜想 2.5.1**（标准猜想H：Hodge型正性）
**H(X)**：在原始上同调 $P^i(X)$ 上，形式：
$$(\alpha, \beta) := (-1)^{\frac{i(i-1)}{2}} \int_X L^{d-i}(\alpha) \cup \beta$$
是正定的。

**注**：这蕴含Weil猜想的Riemann假设部分。

---

## 3. 主要结果与定理

### 3.1 已知情形

**定理 3.1.1**（Tag 0F5B - 标准猜想）
标准猜想在以下情形已知：

**(a) 曲线**
对任意光滑射影曲线 $C$，所有标准猜想成立。

**(b) 曲面**
对光滑射影曲面 $S$，猜想I、B、D成立（Mumford, Kleiman）。
猜想H在 $\text{char} = 0$ 成立。

**(c) 阿贝尔簇**
对阿贝尔簇 $A$，所有标准猜想成立（Lieberman）。

**(d) 完全交**
对完全交，猜想I成立（Deligne）。

### 3.2 推论与等价形式

**定理 3.2.1**（Grothendieck）
若标准猜想成立，则：

**(a) 动机范畴的半单性**
纯动机范畴 $\mathcal{M}$ 是半单阿贝尔范畴。

**(b) 独立的实现**
所有实现函子（Betti、de Rham、étale）是忠实的。

**(c) Tannaka结构**
动机范畴是 neutrale Tannaka范畴。

**定理 3.2.2**（Kleiman）
猜想B（Lefschetz型）蕴含猜想C（分解）。

### 3.3 与其他猜想的联系

**定理 3.3.1**（标准猜想 $\Rightarrow$ Weil猜想）
标准猜想H蕴含Weil猜想的Riemann假设部分。

**定理 3.3.2**（标准猜想 $\Rightarrow$ Hodge猜想的弱形式）
标准猜想提供Hodge猜想的「 motivic 」框架。

### 3.4 l进版本

**定理 3.4.1**（l进标准猜想）
对l进上同调，类似的标准猜想可表述，且与经典版本通过比较同构联系。

---

## 4. 证明思路

### 4.1 曲线的情形

**步骤1**：Jacobian的利用
对于曲线 $C$，利用Jacobian $J(C)$：
$$H^1(C) \cong H^1(J(C))$$

**步骤2**：Theta除子的Lefschetz算子
由经典结果，曲线的Lefschetz理论完全由Jacobian结构决定。

**步骤3**：代数性的验证
验证所有相关算子都是代数的。

### 4.2 阿贝尔簇的证明

**关键观察**：Poincaré除子的幂给出所有需要的对应。

**步骤**：

1. Fourier-Mukai变换
2. Poincaré丛的性质
3. 对偶阿贝尔簇的利用

### 4.3 曲面的部分结果

**策略**：利用Noether-Lefschetz理论和曲面分类。

**关键结果**（Mumford）：
曲面的 $\text{CH}^2$ 的结构控制大部分猜想。

---

## 5. 应用与例子

### 5.1 曲线的标准猜想

**例子 5.1.1**
对椭圆曲线 $E$，对角线分解：
$$[\Delta_E] = [E \times \{0\}] + [\{0\} \times E] - [E \times E] + \text{（对应 } H^1\text{）}$$
所有分量都是代数的。

### 5.2 阿贝尔簇的对角线分解

**例子 5.1.2**
对阿贝尔簇 $A$，对角线：
$$[\Delta_A] = \sum_{i=0}^{2d} \pi_i$$
其中 $\pi_i$ 由Fourier-Mukai核给出。

### 5.3 曲面的困难

**例子 5.1.3**
对一般型曲面，猜想H的未知性反映了：

- 代数循环计算的困难
- transcendental 上同调的控制

### 5.4 与Bloch猜想的联系

**应用 5.3.1**
标准猜想与**Bloch猜想**密切相关：
$$\text{CH}^2(X) \otimes \mathbb{Q} \cong \mathbb{Q} \text{（对 } p_g = 0\text{ 曲面）}$$

### 5.5 特殊簇类的验证

**应用 5.3.2**
标准猜想在以下情形验证：

- 有理齐性簇
- 某些Calabi-Yau簇
- 低维完全交

---

## 6. 与其他概念的关系

### 6.1 与Hodge猜想的对比

| 猜想 | 陈述 | 状态 |
|-----|------|------|
| **Hodge猜想** | Hodge类是代数的 | 除少数情形外开放 |
| **标准猜想I** | Künneth投影是代数的 | 一般开放 |
| **标准猜想B** | Lefschetz逆是代数的 | 一般开放 |
| **标准猜想D** | 同调=数值等价 | 开放（特征p）|
| **标准猜想H** | 正定性 | 开放 |

**关系**：标准猜想B + Hodge猜想 $\Rightarrow$ 更强结果

### 6.2 与动机理论

```
    标准猜想
        │
        │ 蕴含
        ▼
    动机范畴的半单性
        │
        │ 实现
        ▼
    各种上同调的统一
```

### 6.3 与Weil猜想

**关键联系**：标准猜想H $\Rightarrow$ Weil-Riemann假设

Grothendieck的原始动机：通过代数循环理论证明Weil猜想。

### 6.4 与算术几何

**现代发展**：

- l进标准猜想与Tate猜想
- p进标准猜想与p进Hodge理论
- 导出标准猜想

---

## 7. 参考文献

### 7.1 原始文献

1. **Grothendieck, A.** (1969). *Standard conjectures on algebraic cycles*
   - Algebraic Geometry (Bombay Colloquium)
   - 原始陈述

2. **Kleiman, S.L.** (1968). *Algebraic cycles and the Weil conjectures*
   - Dix exposés sur la cohomologie des schémas

### 7.2 已知结果

1. **Lieberman, D.I.** (1968). *Numerical and homological equivalence of algebraic cycles on Hodge manifolds*
   - Amer. J. Math.
   - 阿贝尔簇情形

2. **Mumford, D.** (1969). *Rational equivalence of 0-cycles on surfaces*
   - J. Math. Kyoto Univ.

3. **Deligne, P.** (1968). *Théorème de Lefschetz et critères de dégénérescence de suites spectrales*
   - Publ. Math. IHÉS

### 7.3 综述文献

1. **Kleiman, S.L.** (1994). *The standard conjectures*
   - Motives (Seattle)
   - 全面综述

2. **André, Y.** (2004). *Une introduction aux motifs*
   - SMF Panoramas et Synthèses

3. **Murre, J.P.** (1993). *On a conjectural filtration on the Chow groups of an algebraic variety*
   - Indag. Math.

### 7.4 在线资源

1. **Stacks Project**: [Tag 0F5B](https://stacks.math.columbia.edu/tag/0F5B)
2. **Grothendieck Circle**: 原始手稿

---

## 8. 相关Tags

### 8.1 直接相关

| Tag | 主题 | 关系 |
|-----|------|------|
| [0F5A](#tag-0f5a) | 混合动机 | 应用目标 |
| [0F5C](#tag-0f5c) | Hodge猜想 | 姐妹问题 |
| [0F5D](#tag-0f5d) | Tate猜想 | l进类比 |

### 8.2 代数循环

| Tag | 主题 | 说明 |
|-----|------|------|
| [0F5E](#tag-0f5e) | 周群 | 基础 |
| [0F5F](#tag-0f5f) | 数值等价 | 猜想D |
| [0F5G](#tag-0f5g) | 同调等价 | 猜想D |

### 8.3 Lefschetz理论

| Tag | 主题 | 说明 |
|-----|------|------|
| [0F5H](#tag-0f5h) | Hard Lefschetz | 定理 |
| [0F5I](#tag-0f5i) | Lefschetz分解 | 结构 |

---

## 附录：前沿性与形式化

### A.1 前沿性说明

**为什么这是前沿？**

1. **Grothendieck遗留问题**：50多年未解决的核心问题

2. **动机理论的基础**：决定了动机范畴的结构

3. **与千禧年难题的联系**：Hodge猜想、Tate猜想

4. **持续研究**：每年仍有大量相关论文发表

### A.2 待解决问题

- **一般曲面的猜想B和H**
- **三维簇的猜想I**
- **特征p中的猜想D**
- **非射影簇的推广**

### A.3 Lean4形式化现状

| 组件 | 状态 | 难度 |
|------|------|------|
| 标准猜想陈述 | ❌ 待建设 | ★★★☆☆ |
| 曲线情形证明 | ❌ 待建设 | ★★★★☆ |
| 阿贝尔簇证明 | ❌ 待建设 | ★★★★★ |
| 曲面部分结果 | ❌ 待建设 | ★★★★★ |
| 一般情形 | ❌ 待建设 | ★★★★★ |

---

*本文档由FormalMath项目生成，最后更新：2026-04-10*
