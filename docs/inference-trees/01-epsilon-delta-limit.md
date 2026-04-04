# ε-δ定义 → 极限性质 → 连续性推理树

## 概述
本推理树展示从极限的ε-δ定义出发，推导极限的基本性质，最终建立函数连续性的完整推理链。

```mermaid
graph TD
    subgraph 基础定义
        A1[实数完备性公理<br/>Completeness Axiom] --> A2[绝对值不等式<br/>|x-a|<δ]
        A2 --> A3[ε-δ极限定义<br/>∀ε>0, ∃δ>0, |f(x)-L|<ε]
    end
    
    subgraph 极限唯一性
        A3 --> B1[极限唯一性引理<br/>Lemma: Uniqueness]
        B1 --> B2[反证法: 设lim f(x)=L₁=L₂]
        B2 --> B3[取ε=|L₁-L₂|/2导出矛盾]
    end
    
    subgraph 极限运算性质
        A3 --> C1[极限的代数运算<br/>Algebraic Properties]
        C1 --> C2[和差法则<br/>lim(f±g)=limf±limg]
        C1 --> C3[积法则<br/>lim(f·g)=limf·limg]
        C1 --> C4[商法则<br/>lim(f/g)=limf/limg, limg≠0]
        
        C2 --> D1[夹逼定理<br/>Squeeze Theorem]
        C3 --> D1
    end
    
    subgraph 单侧极限
        A3 --> E1[左极限定义<br/>x→a⁻]
        A3 --> E2[右极限定义<br/>x→a⁺]
        E1 --> E3[双侧极限存在<br/>⇔ 左右极限存在且相等]
        E2 --> E3
    end
    
    subgraph 连续性定义
        E3 --> F1[连续性定义<br/>limₓ→ₐ f(x)=f(a)]
        F1 --> F2[点连续<br/>Continuity at a Point]
        F2 --> F3[区间连续<br/>Continuity on Interval]
    end
    
    subgraph 连续函数性质
        F3 --> G1[连续函数和差积商<br/>仍连续]
        F3 --> G2[复合函数连续性<br/>g∘f continuous]
        G1 --> H1[极值定理<br/>Extreme Value Theorem]
        G2 --> H2[介值定理<br/>Intermediate Value Theorem]
        H1 --> I1[一致连续性<br/>Uniform Continuity]
        H2 --> I1
    end
    
    style A3 fill:#e1f5ff,stroke:#01579b,stroke-width:3px
    style F1 fill:#fff8e1,stroke:#ff6f00,stroke-width:2px
    style I1 fill:#e8f5e9,stroke:#2e7d32,stroke-width:2px
```

## 推理步骤详解

### 第一步：ε-δ极限定义

**定义（函数极限）**：设函数 $f$ 在点 $a$ 的某个去心邻域有定义，若存在实数 $L$ 使得：

$$\forall \varepsilon > 0, \exists \delta > 0, \text{当 } 0 < |x - a| < \delta \text{ 时，有 } |f(x) - L| < \varepsilon$$

则称当 $x \to a$ 时，$f(x)$ 的极限为 $L$，记作 $\lim_{x \to a} f(x) = L$。

**关键理解**：
- ε 控制函数值与极限值的接近程度
- δ 控制自变量与目标点的接近程度
- ∀ε 表示无论多精确的要求都能满足

### 第二步：极限唯一性证明

**引理**：若极限存在，则必唯一。

**证明**：
假设 $\lim_{x \to a} f(x) = L_1$ 且 $\lim_{x \to a} f(x) = L_2$，且 $L_1 \neq L_2$。

取 $\varepsilon = \frac{|L_1 - L_2|}{2} > 0$

由定义，存在 $\delta_1 > 0$，当 $0 < |x - a| < \delta_1$ 时：
$$|f(x) - L_1| < \varepsilon$$

存在 $\delta_2 > 0$，当 $0 < |x - a| < \delta_2$ 时：
$$|f(x) - L_2| < \varepsilon$$

取 $\delta = \min(\delta_1, \delta_2)$，则当 $0 < |x - a| < \delta$ 时：
$$|L_1 - L_2| \leq |L_1 - f(x)| + |f(x) - L_2| < 2\varepsilon = |L_1 - L_2|$$

矛盾！故 $L_1 = L_2$。 ∎

**依赖**：三角不等式、反证法

### 第三步：极限运算性质

**定理**：设 $\lim_{x \to a} f(x) = L$，$\lim_{x \to a} g(x) = M$，则：

| 性质 | 公式 | 关键引理 |
|------|------|----------|
| 和差法则 | $\lim(f \pm g) = L \pm M$ | 三角不等式 |
| 积法则 | $\lim(f \cdot g) = L \cdot M$ | 有界性 + 分解技巧 |
| 商法则 | $\lim(f/g) = L/M$ ($M \neq 0$) | 保号性 + 下界估计 |

**积法则证明要点**：
$$|fg - LM| = |f(g-M) + M(f-L)| \leq |f||g-M| + |M||f-L|$$

利用 $f$ 在 $a$ 附近有界（局部有界性引理）控制第一项。

### 第四步：连续性定义

**定义**：函数 $f$ 在点 $a$ 连续当且仅当：

$$\lim_{x \to a} f(x) = f(a)$$

即满足三个条件：
1. $f(a)$ 有定义
2. $\lim_{x \to a} f(x)$ 存在
3. 两者相等

**等价表述**：
$$\forall \varepsilon > 0, \exists \delta > 0, |x - a| < \delta \Rightarrow |f(x) - f(a)| < \varepsilon$$

注意：此处 $|x - a| < \delta$（包含 $x = a$）

### 第五步：连续函数的重要性质

**极值定理**：闭区间 $[a, b]$ 上的连续函数必有最大值和最小值。

**证明依赖链**：
- 有界性定理 ← 区间套定理 ← 完备性公理
- 确界存在 ← 完备性公理
- 连续性保证极限可达

**介值定理**：设 $f$ 在 $[a, b]$ 连续，$f(a) < c < f(b)$，则存在 $\xi \in (a, b)$ 使 $f(\xi) = c$。

**证明方法**：区间套二分法

## 依赖关系图

```
实数完备性公理
    ↓
ε-δ极限定义 ← 绝对值不等式
    ↓
极限唯一性 ← 三角不等式 + 反证法
    ↓
极限运算性质
    ↓          ↓
夹逼定理  单侧极限
    ↓          ↓
    连续性定义
         ↓
    连续函数性质
         ↓
    极值定理 + 介值定理
         ↓
    一致连续性
```

## 关键引理汇总

| 引理名称 | 作用 | 证明复杂度 |
|----------|------|------------|
| 三角不等式 | 距离估计的基础 | ★☆☆ |
| 局部有界性 | 极限存在的必要条件 | ★★☆ |
| 保号性 | 商的极限存在性 | ★★☆ |
| 区间套定理 | 存在性证明的核心 | ★★★ |

## 应用示例

### 证明 $\lim_{x \to 2} x^2 = 4$

**分析**：$|x^2 - 4| = |x+2||x-2|$

限制 $|x - 2| < 1$，则 $3 < x + 2 < 5$，即 $|x + 2| < 5$

于是 $|x^2 - 4| < 5|x - 2|$

**取 $\delta$**：令 $\delta = \min(1, \varepsilon/5)$

则当 $0 < |x - 2| < \delta$ 时：
$$|x^2 - 4| < 5 \cdot \frac{\varepsilon}{5} = \varepsilon$$ ∎

## 参考

- 《数学分析》陈纪修，第一章
- 《Principles of Mathematical Analysis》Rudin, Chapter 4
- 《Understanding Analysis》Abbott, Chapter 4
