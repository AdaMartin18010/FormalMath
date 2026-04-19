---
msc_primary: 00

  - 00A99
title: Lp空间 (Lp Spaces)
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# Lp空间 (Lp Spaces)

## 中心概念精确定义

**Lp空间**是可测函数构成的Banach空间，是现代分析、偏微分方程和概率论的核心函数空间。

> **Lp范数**：设 $(X, \mathcal{M}, \mu)$ 是测度空间，$1 \leq p < \infty$，定义：
> $$\|f\|_{L^p} = \left(\int_X |f|^p\,d\mu\right)^{1/p}$$

> 
> 对 $p = \infty$：
> $$\|f\|_{L^\infty} = \text{ess sup}|f| = \inf\{M : |f| \leq M \text{ a.e.}\}$$

> **Lp空间**：$L^p(X) = \{f : \|f\|_{L^p} < \infty\}$（模去几乎处处相等的函数）

---

## Mermaid 思维导图

```mermaid
mindmap
  root((Lp空间<br/>Lp Spaces))
    范数与空间
      p范数

        ||f||ₚ=(∫|f|ᵖ)^{1/p}

        三角不等式
      L∞范数
        ess sup|f|

        本性上确界
      等价类
        几乎处处相等
        商空间
    完备性
      Banach空间
        Cauchy列收敛
        Riesz-Fischer
      证明
        逐点收敛
        Fatou引理
        控制收敛
    重要不等式
      Hölder不等式
        1/p+1/q=1

        ||fg||₁≤||f||ₚ||g||_q

      Minkowski
        三角不等式
      Jensen不等式
        凸函数
        积分形式
    对偶空间
      (Lp)*=Lq
        1/p+1/q=1
        Riesz表示
      L¹和L∞
        (L¹)*=L∞
        (L∞)*≠L¹
      自反性
        1<p<∞
        Lᵖ≅(Lᵖ)**
    收敛性
      强收敛

        ||fₙ-f||ₚ→0

      弱收敛
        ∫fₙg→∫fg
      分布收敛
        更弱的形式
    插值理论
      Riesz-Thorin
        复插值
      Marcinkiewicz
        实插值
      应用
        算子有界性

```

---

## 核心要素详解

### 1. Lp范数的性质

**范数公理验证**（$1 \leq p \leq \infty$）：
1. **正定性**：$\|f\|_p \geq 0$，且 $= 0$ $\Leftrightarrow$ $f = 0$ a.e.
2. **齐次性**：$\|\alpha f\|_p = |\alpha| \|f\|_p$
3. **三角不等式**（Minkowski不等式）：$\|f + g\|_p \leq \|f\|_p + \|g\|_p$

**p的取值范围**：
- $p = 1$：可积函数空间，积分范数
- $p = 2$：Hilbert空间，内积 $(f,g) = \int f\bar{g}$
- $p = \infty$：本性有界函数

**范数随p的变化**：在有限测度空间上，$p_1 < p_2$ $\Rightarrow$ $L^{p_2} \subset L^{p_1}$

### 2. Hölder不等式

**定理**：设 $1 \leq p, q \leq \infty$，$\frac{1}{p} + \frac{1}{q} = 1$（共轭指数），则：
$$\|fg\|_{L^1} \leq \|f\|_{L^p} \|g\|_{L^q}$$

即：$\displaystyle\int |fg| \leq \left(\int |f|^p\right)^{1/p} \left(\int |g|^q\right)^{1/q}$

**证明要点**：利用Young不等式 $ab \leq \frac{a^p}{p} + \frac{b^q}{q}$

**特例**：
- $p = q = 2$：Cauchy-Schwarz不等式
- $p = 1, q = \infty$：$\int |fg| \leq \|g\|_\infty \int |f|$

### 3. Riesz-Fischer 定理（完备性）

**定理**：$L^p(X)$ 是Banach空间（$1 \leq p \leq \infty$），即完备的赋范空间。

**证明概要**（$1 \leq p < \infty$）：
1. 取Cauchy列 $\{f_n\}$
2. 选子列使 $\|f_{n_{k+1}} - f_{n_k}\|_p < 2^{-k}$
3. 定义 $g = \sum |f_{n_{k+1}} - f_{n_k}|$，由Minkowski $\|g\|_p < \infty$

4. 故 $g < \infty$ a.e.，级数几乎处处绝对收敛
5. $f_{n_k} \to f$ a.e.，由Fatou引理证明 $f_n \to f$ 在 $L^p$

### 4. 对偶空间与Riesz表示

**定理**（Riesz表示）：对 $1 \leq p < \infty$，$\frac{1}{p} + \frac{1}{q} = 1$：
$$(L^p)^* \cong L^q$$

同构映射：$g \in L^q$ 对应泛函 $\phi_g(f) = \int fg$

**范数等式**：$\|\phi_g\|_{(L^p)^*} = \|g\|_{L^q}$

**重要例外**：$(L^\infty)^* \neq L^1$，$L^\infty$ 上有更复杂的线性泛函。

**自反性**：$L^p$ 自反当且仅当 $1 < p < \infty$。

### 5. L²空间的特殊性

**内积结构**：
$$(f, g) = \int_X f \bar{g}\,d\mu$$

**Hilbert空间性质**：
- 正交分解：$M$ 闭子空间，$H = M \oplus M^\perp$
- 正交投影：存在唯一的最近点投影
- Riesz表示：$H^* \cong H$（通过内积）

**Fourier级数**：$L^2[0,2\pi]$ 中，$\{e^{inx}\}$ 是标准正交基：
$$f = \sum_{n=-\infty}^{\infty} c_n e^{inx}, \quad c_n = \frac{1}{2\pi}\int_0^{2\pi} f(x) e^{-inx}dx$$

---

## 关键性质与定理

### 定理1：稠密子空间

**定理**：在 $L^p(\mathbb{R}^n)$（$1 \leq p < \infty$）中，以下子空间稠密：
- 简单函数
- 具有紧支集的连续函数 $C_c(\mathbb{R}^n)$
- 光滑函数 $C_c^\infty(\mathbb{R}^n)$

**意义**：可以用光滑函数逼近 $L^p$ 函数。

### 定理2：Lusin定理

**定理**：设 $f$ 在有限测度集 $E$ 上可测，则对任意 $\varepsilon > 0$，存在紧集 $K \subset E$ 使得：
- $m(E \setminus K) < \varepsilon$
- $f|_K$ 连续

即：可测函数"几乎连续"。

### 定理3：Egorov定理

**定理**：设 $m(E) < \infty$，$f_n \to f$ a.e.，则对任意 $\varepsilon > 0$，存在 $A \subset E$ 使得：
- $m(E \setminus A) < \varepsilon$
- $f_n \rightrightarrows f$ 在 $A$ 上

即：几乎处处收敛可提升为"几乎一致收敛"。

### 定理4：插值定理

**Riesz-Thorin插值**：设 $T$ 是线性算子，满足：
$$\|T\|_{L^{p_0} \to L^{q_0}} \leq M_0, \quad \|T\|_{L^{p_1} \to L^{q_1}} \leq M_1$$

则对 $0 < \theta < 1$，$\frac{1}{p} = \frac{1-\theta}{p_0} + \frac{\theta}{p_1}$，$\frac{1}{q} = \frac{1-\theta}{q_0} + \frac{\theta}{q_1}$：
$$\|T\|_{L^p \to L^q} \leq M_0^{1-\theta} M_1^\theta$$

---

## 典型例子

### 例子1：Lᵖ包含关系

在 $[0,1]$ 上（有限测度）：
$$L^\infty \subset L^2 \subset L^1$$

**反例**：在 $\mathbb{R}$ 上（无限测度），无包含关系：
- $f(x) = \frac{1}{\sqrt{x}}\chi_{(0,1)} \in L^1$ 但 $\notin L^2$
- $f(x) = \frac{1}{x}\chi_{[1,\infty)} \in L^2$ 但 $\notin L^1$

### 例子2：Riesz表示的应用

**问题**：求 $L^2[0,1]$ 上的线性泛函 $\phi(f) = f(1/2)$ 的表示。

**分析**：$\phi$ 不是 $L^2$ 上的连续泛函（点值不连续），故不能表示为积分形式。这说明了 $(L^p)^* \cong L^q$ 中，泛函必须是"平均"形式。

### 例子3：弱收敛但不强收敛

在 $L^2[0,2\pi]$ 中，$f_n(x) = \sin(nx)$。

- **弱收敛**：对任意 $g \in L^2$，$\int f_n g \to 0$（Riemann-Lebesgue引理）
- **不强收敛**：$\|f_n - f_m\|_2 = \sqrt{\pi}$ 对 $n \neq m$

---

## 关联概念网络

### 相似概念

| 概念 | 关系 | 说明 |
|------|------|------|
| **Sobolev空间 $W^{k,p}$** | 推广 | 含弱导数的 $L^p$ 空间 |
| **Besov空间** | 细化 | 插值尺度更精细的函数空间 |
| **Orlicz空间** | 推广 | $L^p$ 的凸函数推广 |

### 对偶概念

| 概念 | 对偶关系 | 说明 |
|------|----------|------|
| **$L^p \leftrightarrow L^q$** | 共轭对偶 | Hölder对，$1/p+1/q=1$ |
| **强收敛 ↔ 弱收敛** | 拓扑对偶 | 弱拓扑更粗 |

### 推广概念

```

Lp空间 → 向量值Lp空间
      ↓
   加权Lp空间
      ↓
   变指数Lp(x)
      ↓
   非交换Lp(算子代数)

```

---

## 课程对齐

### MIT 18.125
- **Topic**: Real analysis, Lp spaces
- **Text**: Stein & Shakarchi, *Real Analysis*, Ch. 1-2
- **Key topics**: Hölder, Minkowski, duality, convergence

### Princeton MAT 218
- **Topic**: Functional analysis
- **Text**: Folland, *Real Analysis*, Ch. 6
- **Emphasis**: Banach space structure, Riesz representation, applications to PDEs

---

## 总结

Lp空间是现代分析的骨架，它统一了多种函数空间（可积函数、平方可积函数、有界函数）并具有丰富的结构：范数、对偶、完备性。Hölder不等式和Minkowski不等式是分析的基本工具，而Riesz-Fischer定理保证了分析的完备性。理解Lp空间的结构，是掌握泛函分析、调和分析和偏微分方程的关键。

---

*创建日期：2026年4月*  
*相关概念：[Lebesgue测度](Lebesgue测度.md)、[Sobolev空间](Sobolev空间.md)、[Hilbert空间](./../../../../00-未解决问题/02-Hilbert问题.md)*
