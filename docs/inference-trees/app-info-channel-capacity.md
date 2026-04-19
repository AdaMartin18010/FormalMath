---
msc_primary: 00

  - 00A99
title: 信道容量推导链
processed_at: '2026-04-05'
---
# 信道容量推导链

## 概述
本推理树展示Shannon信道容量定理的完整数学推导，包括互信息、信道编码定理、典型序列、可达速率等核心内容。

---

## 推理树

```mermaid
graph TD
    subgraph 信息度量
        A1[熵<br/>HX = -Σpx log px] --> A2[联合熵<br/>HX,Y]
        A2 --> A3[条件熵<br/>HXY = HX,Y - HY]
        A3 --> A4[互信息<br/>IX;Y = HX - HXY]
    end
    
    subgraph 信道模型
        A4 --> B1[离散信道<br/>py|x]

        B1 --> B2[信道容量<br/>C = max_p I(X;Y)]
        B2 --> B3[无记忆信道<br/>pyn|xn = ∏p(yi|xi)]
        B3 --> B4[对称信道<br/>C = log|Y| - Hrow]

    end
    
    subgraph 典型序列
        B3 --> C1[弱典型性<br/>A_ε^n]
        C1 --> C2[典型集大小<br/>≈ 2^{nH}]
        C2 --> C3[联合典型性<br/>A_ε^nX,Y]
        C3 --> C4[译码规则<br/>联合典型译码]
    end
    
    subgraph 信道编码定理
        C4 --> D1[码率R<br/>M = 2^{nR}个码字]
        D1 --> D2[随机编码<br/>iid生成码字]
        D2 --> D3[错误概率<br/>P_e → 0 if R < C]
        D3 --> D4[可达性<br/>存在R可达码]
    end
    
    subgraph 逆定理
        B2 --> E1[Fano不等式<br/>HXY ≤ HPe + Pe log|X|]

        E1 --> E2[逆定理<br/>P_e ↛ 0 if R > C]
        E2 --> E3[信道容量<br/>C是可达速率上界]
    end
    
    subgraph 连续信道
        B2 --> F1[微分熵<br/>hX = -∫fx log fx dx]
        F1 --> F2[高斯信道<br/>Y = X + Z, Z ~ N0,σ²]
        F2 --> F3[功率约束<br/>EX² ≤ P]
        F3 --> F4[AWGN容量<br/>C = ½ log1 + P/σ²]
    end
    
    style B2 fill:#e8f5e9,stroke:#2e7d32,stroke-width:3px
    style D4 fill:#fff8e1,stroke:#ff6f00,stroke-width:2px
    style E3 fill:#e1f5ff,stroke:#01579b,stroke-width:2px
    style F4 fill:#fce4ec,stroke:#c2185b,stroke-width:2px

```

---

## 核心推导详解

### 第一步：信息度量基础

**熵（Entropy）**：
$$H(X) = -\sum_{x \in \mathcal{X}} p(x) \log p(x)$$

**联合熵**：
$$H(X, Y) = -\sum_{x,y} p(x,y) \log p(x,y)$$

**条件熵**：
$$H(Y|X) = \sum_{x} p(x) H(Y|X=x) = H(X, Y) - H(X)$$

**互信息**：
$$I(X; Y) = H(X) - H(X|Y) = H(Y) - H(Y|X) = \sum_{x,y} p(x,y) \log \frac{p(x,y)}{p(x)p(y)}$$

**性质**：
- $I(X; Y) \geq 0$（非负性）
- $I(X; Y) = 0 \Leftrightarrow X \perp Y$（独立性）
- $I(X; Y) = I(Y; X)$（对称性）

### 第二步：离散无记忆信道（DMC）

**信道模型**：$(\mathcal{X}, p(y|x), \mathcal{Y})$

**信道容量定义**：
$$C = \max_{p(x)} I(X; Y)$$

**计算**：
- 对给定信道转移概率 $p(y|x)$

- 对输入分布 $p(x)$ 优化互信息
- 通常使用Blahut-Arimoto算法数值求解

**对称信道**：
- 若信道转移矩阵行排列相同：$C = \log|\mathcal{Y}| - H(\text{row})$

- 二元对称信道（BSC）：$C = 1 - H(p)$

### 第三步：典型序列理论

**弱典型序列**：序列 $x^n$ 是 $\epsilon$-典型的，如果：
$$\left|-\frac{1}{n}\log p(x^n) - H(X)\right| \leq \epsilon$$

**典型集**：$A_\epsilon^{(n)} = \{x^n : \text{弱典型}\}$

**渐近等分割性（AEP）**：
1. $P(X^n \in A_\epsilon^{(n)}) \to 1$（当 $n \to \infty$）
2. $|A_\epsilon^{(n)}| \approx 2^{nH(X)}$

3. 对 $x^n \in A_\epsilon^{(n)}$：$p(x^n) \approx 2^{-nH(X)}$

**联合典型性**：
$$(x^n, y^n) \in A_\epsilon^{(n)}(X, Y) \text{ 如果：}$$
$$\left|-\frac{1}{n}\log p(x^n, y^n) - H(X,Y)\right| \leq \epsilon$$

### 第四步：信道编码定理（可达性）

**编码设置**：
- 码本 $\mathcal{C} = \{X^n(1), \ldots, X^n(2^{nR})\}$
- 速率 $R = \frac{\log M}{n}$（比特/信道使用）
- 译码器：联合典型译码

**随机编码证明**：

1. 生成码本：每个 $X^n(i)$ 独立 $\sim p(x)$ i.i.d.
2. 发送消息 $W$，接收 $Y^n$
3. 译码：找到唯一的 $\hat{W}$ 使得 $(X^n(\hat{W}), Y^n)$ 联合典型

**错误概率分析**：

$$P_e^{(n)} = P(\hat{W} \neq W)$$

由联合界：
$$P_e^{(n)} \leq P(\text{发送码字非典型}) + \sum_{j \neq W} P(\text{码字}j\text{与}Y^n\text{联合典型})$$

$$\leq \epsilon + 2^{nR} \cdot 2^{-n(I(X;Y) - 3\epsilon)}$$

当 $R < I(X;Y) - 3\epsilon$ 时，$P_e^{(n)} \to 0$。

**结论**：对任意 $R < C$，存在码使得 $P_e^{(n)} \to 0$。

### 第五步：信道编码逆定理

**Fano不等式**：
设 $P_e = P(\hat{W} \neq W)$，则：
$$H(W | \hat{W}) \leq H(P_e) + P_e \log |\mathcal{W}|$$

**逆定理证明**：

$$nR = H(W) = I(W; \hat{W}) + H(W | \hat{W})$$

$$\leq I(X^n; Y^n) + H(P_e) + P_e \cdot nR$$
$$\leq \sum_{i=1}^n I(X_i; Y_i) + 1 + P_e \cdot nR$$
$$\leq nC + 1 + P_e \cdot nR$$

若 $P_e \to 0$，则 $R \leq C$。

### 第六步：高斯信道（AWGN）

**信道模型**：
$$Y = X + Z, \quad Z \sim \mathcal{N}(0, \sigma^2)$$

**功率约束**：$\frac{1}{n}\sum_{i=1}^n X_i^2 \leq P$

**容量推导**：

$$I(X; Y) = h(Y) - h(Y|X) = h(Y) - h(Z)$$

在功率约束下，$Y$ 方差最大为 $P + \sigma^2$，当 $X \sim \mathcal{N}(0, P)$ 时达到：

$$C = \frac{1}{2}\log\left(1 + \frac{P}{\sigma^2}\right) \text{ bits/channel use}$$

**信噪比**：$SNR = \frac{P}{\sigma^2}$

---

## 常见信道容量

| 信道类型 | 容量公式 | 条件 |
|----------|----------|------|
| BSC | $C = 1 - H(p)$ | 交叉概率 $p$ |
| BEC | $C = 1 - \epsilon$ | 擦除概率 $\epsilon$ |
| AWGN | $C = \frac{1}{2}\log(1 + SNR)$ | 功率约束 $P$ |
| MIMO | $C = \log\det(I + \frac{P}{n_t}HH^*)$ | 信道矩阵 $H$ |

---

## 依赖关系图

```

概率论基础
    ↓
信息度量 ← 熵理论
    ↓
互信息 ← 统计依赖
    ↓
信道模型
    ↓
典型序列理论 ← 大数定律
    ↓
信道编码定理 ← 随机编码
    ↓
逆定理 ← Fano不等式
    ↓
信道容量 = 可达速率上确界

```

---

## 关键公式汇总

| 名称 | 公式 | 意义 |
|------|------|------|
| 互信息 | $I(X;Y) = H(X) - H(X|Y)$ | 信息传输 |
| 信道容量 | $C = \max_{p(x)} I(X;Y)$ | 最大可达速率 |
| AEP | $P(X^n \in A_\epsilon^{(n)}) \to 1$ | 典型性基础 |
| AWGN容量 | $C = \frac{1}{2}\log(1+P/\sigma^2)$ | 加性高斯噪声 |

---

## 参考

- Shannon, C. E. (1948). "A Mathematical Theory of Communication"
- Cover, T. M. & Thomas, J. A. (2006). *Elements of Information Theory*
- Gallager, R. G. (1968). *Information Theory and Reliable Communication*
- MacKay, D. J. C. (2003). *Information Theory, Inference, and Learning Algorithms*
- Yeung, R. W. (2008). *Information Theory and Network Coding*

---

*生成时间：2026年4月*
