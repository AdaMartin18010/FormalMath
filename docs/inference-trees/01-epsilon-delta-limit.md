---
msc_primary: 00A99
msc_secondary:
- 00A99
title: ε-δ定义 → 极限性质 → 连续性推理树
processed_at: '2026-04-05'
---
# ε-δ定义 → 极限性质 → 连续性推理树

## 概述

本推理树展示从极限的 ε-δ 定义出发，推导极限的基本性质，最终建立函数连续性的完整推理链。这是数学分析的基石理论。

### 前提条件
- 实数完备性公理（确界原理、区间套定理等）
- 绝对值不等式与基本运算
- 集合论基础

---

## 完整推理树

```mermaid
graph TD
    subgraph 基础定义
        A1[实数完备性公理<br/>确界原理/区间套定理] --> A2[绝对值不等式<br/>|x-a|<δ, |y-b|<ε]
        A2 --> A3[ε-δ极限定义<br/>∀ε>0, ∃δ>0, 0<|x-a|<δ⇒|f(x)-L|<ε]
        A3 --> A3a[严格定义要素<br/>去心邻域, 任意精度]
    end
    
    subgraph 极限唯一性
        A3 --> B1[极限唯一性定理<br/>若极限存在则唯一]
        B1 --> B2[反证法假设<br/>lim f(x)=L₁=L₂]
        B2 --> B3[取ε=|L₁-L₂|/2>0<br/>导出矛盾]
        B3 --> B4[三角不等式应用<br/>|L₁-L₂|≤|L₁-f(x)|+|f(x)-L₂|<2ε=|L₁-L₂|]
    end
    
    subgraph 极限运算性质
        A3 --> C1[极限代数运算<br/>和差积商法则]
        C1 --> C2[和差法则<br/>lim(f±g)=limf±limg]
        C2 --> C2a[三角不等式<br/>|(f±g)-(L±M)|≤|f-L|+|g-M|]
        
        C1 --> C3[积法则<br/>lim(f·g)=limf·limg]
        C3 --> C3a[分解技巧<br/>|fg-LM|≤|f||g-M|+|M||f-L|]
        C3a --> C3b[局部有界性引理<br/>f在a附近有界]
        
        C1 --> C4[商法则<br/>lim(f/g)=L/M, M≠0]
        C4 --> C4a[保号性引理<br/>g在a附近≠0]
        
        C2 --> D1[夹逼定理<br/>Squeeze Theorem]
        C3 --> D1
        D1 --> D1a[h(x)≤f(x)≤g(x)<br/>lim h=lim g=L⇒lim f=L]
    end
    
    subgraph 单侧极限
        A3 --> E1[左极限<br/>x→a⁻, x<a]
        A3 --> E2[右极限<br/>x→a⁺, x>a]
        E1 --> E3[双侧极限存在<br/>⇔ 左右极限存在且相等]
        E2 --> E3
        E3 --> E3a[应用: 分段函数<br/>连续性判定]
    end
    
    subgraph 连续性定义
        E3 --> F1[连续性定义<br/>limₓ→ₐ f(x)=f(a)]
        F1 --> F1a[等价表述<br/>∀ε>0, ∃δ>0, |x-a|<δ⇒|f(x)-f(a)|<ε]
        F1 --> F2[点连续<br/>Continuity at a Point]
        F2 --> F3[区间连续<br/>Continuity on Interval]
        F3 --> F3a[一致连续<br/>δ与x无关]
    end
    
    subgraph 连续函数性质
        F3 --> G1[连续函数运算<br/>和差积商仍连续]
        F3 --> G2[复合函数连续性<br/>g∘f continuous]
        G2 --> G2a[ε-δ传递<br/>δ₁(ε)和δ₂(δ₁)]
        
        G1 --> H1[极值定理<br/>Extreme Value Theorem]
        H1 --> H1a[有界性+确界可达<br/>闭区间[a,b]]
        H1 --> H1b[依赖: 区间套定理<br/>+ 连续性]
        
        G2 --> H2[介值定理<br/>Intermediate Value Theorem]
        H2 --> H2a[零点定理<br/>f(a)f(b)<0⇒∃c:f(c)=0]
        H2 --> H2b[证明: 区间套二分法<br/>完备性公理]
        
        H1 --> I1[一致连续性<br/>Uniform Continuity]
        H2 --> I1
        I1 --> I1a[Cantor定理<br/>闭区间上连续⇒一致连续]
    end
    
    style A3 fill:#e1f5ff,stroke:#01579b,stroke-width:3px
    style F1 fill:#fff8e1,stroke:#ff6f00,stroke-width:3px
    style I1 fill:#e8f5e9,stroke:#2e7d32,stroke-width:3px
    style B1 fill:#bfb,stroke:#333,stroke-width:2px
    style D1 fill:#bbf,stroke:#333,stroke-width:2px
```

---

## 推理步骤详解

### 第一步：ε-δ极限定义

**定义（函数极限）**：设函数 $f$ 在点 $a$ 的某个去心邻域有定义，若存在实数 $L$ 使得：

$$\forall \varepsilon > 0, \exists \delta > 0, \text{当 } 0 < |x - a| < \delta \text{ 时，有 } |f(x) - L| < \varepsilon$$

则称当 $x \to a$ 时，$f(x)$ 的极限为 $L$，记作 $\displaystyle\lim_{x \to a} f(x) = L$。

**关键理解**：
- **ε (epsilon)**：控制函数值与极限值的接近程度，任意小但为正
- **δ (delta)**：控制自变量与目标点的接近程度，依赖于 ε
- **∀ε**：无论多精确的要求都能找到相应的 δ
- **去心邻域** $0 < |x - a|$：极限不关心 $f$ 在 $a$ 点的值

**否定形式**：$\displaystyle\lim_{x \to a} f(x) \neq L$ 当且仅当
$$\exists \varepsilon_0 > 0, \forall \delta > 0, \exists x: 0 < |x-a| < \delta \text{ 但 } |f(x)-L| \geq \varepsilon_0$$

---

### 第二步：极限唯一性证明

**定理**：若极限存在，则必唯一。

**证明**：

假设 $\displaystyle\lim_{x \to a} f(x) = L_1$ 且 $\displaystyle\lim_{x \to a} f(x) = L_2$，且 $L_1 \neq L_2$。

取 $\varepsilon = \dfrac{|L_1 - L_2|}{2} > 0$

由定义，存在 $\delta_1 > 0$，当 $0 < |x - a| < \delta_1$ 时：$|f(x) - L_1| < \varepsilon$

存在 $\delta_2 > 0$，当 $0 < |x - a| < \delta_2$ 时：$|f(x) - L_2| < \varepsilon$

取 $\delta = \min(\delta_1, \delta_2)$，则当 $0 < |x - a| < \delta$ 时，两式同时成立。

由三角不等式：
$$|L_1 - L_2| \leq |L_1 - f(x)| + |f(x) - L_2| < \varepsilon + \varepsilon = |L_1 - L_2|$$

即 $|L_1 - L_2| < |L_1 - L_2|$，矛盾！

故 $L_1 = L_2$。∎

**依赖**：三角不等式、反证法

---

### 第三步：极限运算性质

**定理**：设 $\displaystyle\lim_{x \to a} f(x) = L$，$\displaystyle\lim_{x \to a} g(x) = M$，则：

| 性质 | 公式 | 关键引理 |
|------|------|----------|
| **和差法则** | $\displaystyle\lim_{x \to a}(f \pm g) = L \pm M$ | 三角不等式 |
| **积法则** | $\displaystyle\lim_{x \to a}(f \cdot g) = L \cdot M$ | 有界性 + 分解技巧 |
| **商法则** | $\displaystyle\lim_{x \to a}\frac{f}{g} = \frac{L}{M}$ ($M \neq 0$) | 保号性 + 下界估计 |

**积法则证明详解**：

关键分解：
$$|f(x)g(x) - LM| = |f(x)g(x) - f(x)M + f(x)M - LM|$$
$$\leq |f(x)||g(x) - M| + |M||f(x) - L|$$

**步骤**：
1. 由 $\displaystyle\lim_{x \to a} f(x) = L$，$f$ 在 $a$ 的某去心邻域有界（**局部有界性引理**）
2. 设 $|f(x)| \leq K$
3. 对 $\varepsilon > 0$，取 $\delta$ 使得 $|f(x) - L| < \frac{\varepsilon}{2|M|+1}$ 和 $|g(x) - M| < \frac{\varepsilon}{2K}$
4. 则 $|f(x)g(x) - LM| < K \cdot \frac{\varepsilon}{2K} + |M| \cdot \frac{\varepsilon}{2|M|+1} < \varepsilon$ ∎

---

### 第四步：夹逼定理

**定理**：设 $h(x) \leq f(x) \leq g(x)$ 在 $a$ 的某去心邻域成立，且
$$\lim_{x \to a} h(x) = \lim_{x \to a} g(x) = L$$
则 $\displaystyle\lim_{x \to a} f(x) = L$。

**证明**：

对 $\varepsilon > 0$，存在 $\delta_1, \delta_2 > 0$ 使得：
- 当 $0 < |x-a| < \delta_1$：$L - \varepsilon < h(x) < L + \varepsilon$
- 当 $0 < |x-a| < \delta_2$：$L - \varepsilon < g(x) < L + \varepsilon$

取 $\delta = \min(\delta_1, \delta_2, \delta_0)$（其中 $\delta_0$ 保证不等式 $h \leq f \leq g$ 成立）。

则当 $0 < |x-a| < \delta$：
$$L - \varepsilon < h(x) \leq f(x) \leq g(x) < L + \varepsilon$$

故 $|f(x) - L| < \varepsilon$。∎

---

### 第五步：连续性定义

**定义**：函数 $f$ 在点 $a$ 连续当且仅当：

$$\lim_{x \to a} f(x) = f(a)$$

即满足三个条件：
1. $f(a)$ 有定义（$a \in \text{dom}(f)$）
2. $\displaystyle\lim_{x \to a} f(x)$ 存在
3. 极限值等于函数值

**等价表述（ε-δ语言）**：
$$\forall \varepsilon > 0, \exists \delta > 0, |x - a| < \delta \Rightarrow |f(x) - f(a)| < \varepsilon$$

注意：此处 $|x - a| < \delta$（**包含 $x = a$**，与极限定义不同）

**单侧连续**：
- **左连续**：$\displaystyle\lim_{x \to a^-} f(x) = f(a)$
- **右连续**：$\displaystyle\lim_{x \to a^+} f(x) = f(a)$
- **连续**：左连续 + 右连续

---

### 第六步：连续函数的重要性质

#### 6.1 极值定理

**定理**：设 $f$ 在闭区间 $[a, b]$ 上连续，则 $f$ 在 $[a, b]$ 上必有最大值和最小值。

**证明依赖链**：
```
有界性定理 ← 区间套定理 ← 完备性公理
     ↓
确界存在 ← 完备性公理
     ↓
连续性保证极限可达
     ↓
极值存在
```

#### 6.2 介值定理

**定理**：设 $f$ 在 $[a, b]$ 连续，$f(a) < c < f(b)$（或 $f(a) > c > f(b)$），则存在 $\xi \in (a, b)$ 使 $f(\xi) = c$。

**证明方法（区间套二分法）**：

1. 设 $[a_1, b_1] = [a, b]$，$f(a_1) < c < f(b_1)$
2. 取中点 $m = \frac{a_1 + b_1}{2}$
   - 若 $f(m) = c$，得证
   - 若 $f(m) < c$，令 $[a_2, b_2] = [m, b_1]$
   - 若 $f(m) > c$，令 $[a_2, b_2] = [a_1, m]$
3. 归纳构造区间套 $[a_n, b_n]$，满足 $f(a_n) < c < f(b_n)$，长度 $\to 0$
4. 由区间套定理，$\exists! \xi \in \bigcap [a_n, b_n]$，且 $a_n, b_n \to \xi$
5. 由连续性，$f(\xi) = \lim f(a_n) \leq c \leq \lim f(b_n) = f(\xi)$
6. 故 $f(\xi) = c$ ∎

#### 6.3 一致连续性

**定义**：$f$ 在区间 $I$ 上**一致连续**当且仅当：
$$\forall \varepsilon > 0, \exists \delta > 0, \forall x_1, x_2 \in I: |x_1 - x_2| < \delta \Rightarrow |f(x_1) - f(x_2)| < \varepsilon$$

关键点：**δ 仅依赖于 ε，与点的位置无关**。

**Cantor定理**：闭区间 $[a, b]$ 上的连续函数必一致连续。

---

## 依赖关系图

```
                    实数完备性公理
                         │
        ┌────────────────┼────────────────┐
        ↓                ↓                ↓
   确界原理         区间套定理         Bolzano-Weierstrass
        │                │                │
        └────────────────┼────────────────┘
                         ↓
               ε-δ极限定义 ← 绝对值不等式
                         │
         ┌───────────────┼───────────────┐
         ↓               ↓               ↓
    极限唯一性      极限运算性质      单侧极限
         │               │               │
         │               ↓               │
         │          夹逼定理             │
         │               │               │
         └───────────────┼───────────────┘
                         ↓
                    连续性定义
                         │
         ┌───────────────┼───────────────┐
         ↓               ↓               ↓
    连续函数运算    极值定理+介值定理   一致连续性
         │               │               │
         │               ↓               │
         │         反函数连续性          │
         │               │               │
         └───────────────┴───────────────┘
                         ↓
                    微积分基本理论
```

---

## 关键引理汇总

| 引理名称 | 陈述 | 证明复杂度 |
|----------|------|------------|
| **三角不等式** | $|a + b| \leq |a| + |b|$ | ★☆☆ |
| **局部有界性** | 极限存在 ⇒ 函数在a附近有界 | ★★☆ |
| **保号性** | $L \neq 0$ ⇒ $f$ 在 $a$ 附近与 $L$ 同号 | ★★☆ |
| **区间套定理** | 闭区间套有唯一公共点 | ★★☆ |
| **Bolzano-Weierstrass** | 有界序列有收敛子列 | ★★★ |

---

## 应用示例

### 示例1: 证明 $\displaystyle\lim_{x \to 2} x^2 = 4$

**分析**：$|x^2 - 4| = |x+2||x-2|$

**步骤**：
1. 限制 $|x - 2| < 1$，则 $1 < x < 3$，即 $3 < x + 2 < 5$
2. 于是 $|x^2 - 4| = |x+2||x-2| < 5|x-2|$

**取 δ**：对任意 $\varepsilon > 0$，令 $\delta = \min\left(1, \dfrac{\varepsilon}{5}\right)$

**验证**：当 $0 < |x - 2| < \delta$ 时：
- $|x - 2| < 1$ 保证 $|x + 2| < 5$
- $|x - 2| < \varepsilon/5$ 保证 $5|x - 2| < \varepsilon$

故 $|x^2 - 4| < \varepsilon$。∎

---

### 示例2: 证明 $\sin x$ 在 $\mathbb{R}$ 上连续

**证明**：利用 $|\sin x - \sin a| = 2\left|\cos\dfrac{x+a}{2}\right|\left|\sin\dfrac{x-a}{2}\right| \leq 2 \cdot 1 \cdot \dfrac{|x-a|}{2} = |x-a|$

对 $\varepsilon > 0$，取 $\delta = \varepsilon$，则 $|x - a| < \delta \Rightarrow |\sin x - \sin a| < \varepsilon$。∎

---

## 常见误区与澄清

| 误区 | 澄清 |
|------|------|
| 连续 = 图像不间断 | 不完全准确。Cantor函数连续但图像"奇怪" |
| 极限存在 ⇒ 函数在该点有定义 | **错误**。极限是去心邻域的概念 |
| 连续函数序列的极限连续 | **错误**。一致收敛才保证极限连续 |
| 开区间连续 ⇒ 有极值 | **错误**。如 $f(x) = x$ 在 $(0,1)$ |

---

## 参考

### 经典教材
- 《数学分析》陈纪修，第一章
- 《Principles of Mathematical Analysis》Walter Rudin, Chapter 4
- 《Understanding Analysis》Stephen Abbott, Chapter 4
- 《Introduction to Real Analysis》Bartle & Sherbert, Chapter 5

### 历史文献
- Cauchy, A. L. (1821). *Cours d'Analyse de l'École Royale Polytechnique*
- Weierstrass, K. (1872). 严格 ε-δ 定义的引入

---

*最后更新: 2026年4月4日*  
*数学精确性版本: 1.1*  
*验证状态: ✓ 已验证*
