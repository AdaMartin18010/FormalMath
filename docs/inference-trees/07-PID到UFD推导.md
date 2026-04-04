---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# PID → UFD 推导

## 核心定理陈述

**定理**：每个主理想整环 (PID) 都是唯一分解整环 (UFD)。

---

## 推理树

```mermaid
graph TD
    A[PID R<br/>主理想整环] --> B[整环<br/>无零因子]
    B --> C[主理想条件<br/>任意理想 = (a)]
    
    C --> D[诺特性<br/>ACC满足]
    D --> E[因子链有限<br/>a₁R ⊇ a₂R ⊇ ... 终止]
    
    F[不可约元p] --> G[pR极大理想?]
    G -->|PID中| H[pR极大<br/>⇔ p不可约]

    H --> I[极大理想素<br/>⇒ p是素元]
    
    E --> J[存在性<br/>任意a = p₁...pₙ]
    I --> K[唯一性<br/>分解本质唯一]
    
    J --> L[PID是UFD<br/>唯一分解整环]
    K --> L
    
    L --> M[应用<br/>ℤ是UFD]
    L --> N[应用<br/>k[x]是UFD]
    L --> O[应用<br/>ℤ₍ₚ₎是UFD]
    
    style L fill:#f9f,stroke:#333,stroke-width:2px
    style D fill:#bbf,stroke:#333,stroke-width:1px
    style I fill:#bbf,stroke:#333,stroke-width:1px

```

---

## 关键定义

### 整环相关概念

| 概念 | 定义 | 等价表述 |
|-----|------|---------|
| **整环** | 交换环，$1 \neq 0$，无零因子 | $ab = 0 \Rightarrow a=0$ 或 $b=0$ |
| **单位** | $u \in R^\times$ | 存在 $v$ 使 $uv = 1$ |
| **相伴** | $a \sim b$ | $a = ub$，$u$ 是单位 |
| **不可约** | $p$ 非零非单位 | $p = ab \Rightarrow a$ 或 $b$ 是单位 |
| **素元** | $p$ 非零非单位 | $p \mid ab \Rightarrow p \mid a$ 或 $p \mid b$ |
| **主理想** | $(a) = aR$ | 由一个元素生成 |
| **PID** | 主理想整环 | 整环，所有理想主 |

---

## 证明详解

### 步骤1：PID是诺特环

**命题**：PID满足升链条件 (ACC)。

**证明**：
- 设 $I_1 \subseteq I_2 \subseteq \cdots$ 是理想升链
- 令 $I = \bigcup I_n$，验证 $I$ 是理想
- PID中 $I = (a)$ 对某个 $a$
- $a \in I_N$ 对某个 $N$，则 $I \subseteq I_N \subseteq I_{N+1} \subseteq \cdots \subseteq I$
- 故链稳定于 $I_N$ ∎

**推论**：任意非零非单位元可分解为不可约元之积。

### 步骤2：不可约元 = 素元

**命题**：在PID中，$p$ 不可约 $\Leftrightarrow$ $p$ 是素元。

**证明**（$\Rightarrow$）：
- 设 $p$ 不可约，考虑理想 $(p)$
- 若 $(a) \supseteq (p)$，则 $p = ab$
- $p$ 不可约 $\Rightarrow$ $a$ 单位 或 $b$ 单位
- 若 $b$ 单位，$(a) = (p)$；若 $a$ 单位，$(a) = R$
- 故 $(p)$ 是极大理想，从而是素理想
- 因此 $p$ 是素元 ∎

**证明**（$\Leftarrow$）：
- 设 $p$ 是素元，$p = ab$
- $p \mid ab$ 且 $p$ 素，故 $p \mid a$ 或 $p \mid b$
- 若 $p \mid a$，设 $a = pc$，则 $p = pcb$，即 $cb = 1$
- 故 $b$ 是单位，$p$ 不可约 ∎

### 步骤3：分解的存在性

**命题**：PID中任意非零非单位可分解为不可约元之积。

**证明**（反证法）：
- 假设存在不能分解的元素集合 $S \neq \emptyset$
- 考虑理想族 $\{(a) : a \in S\}$
- 由ACC，存在极大元 $(m)$，$m \in S$
- $m$ 非不可约（否则已分解）
- 故 $m = ab$，$a, b$ 非单位
- $(m) \subsetneq (a), (m) \subsetneq (b)$
- 由极大性，$a, b \notin S$，即可分解
- 故 $m = ab$ 也可分解，矛盾 ∎

### 步骤4：分解的唯一性

**命题**：若 $a = p_1 \cdots p_m = q_1 \cdots q_n$（不可约元），则 $m = n$ 且（重排后）$p_i \sim q_i$。

**证明**：
- 对 $m$ 归纳
- $p_1 \mid q_1 \cdots q_n$，$p_1$ 素元（步骤2）
- 故 $p_1 \mid q_j$ 对某个 $j$
- 不妨设 $p_1 \mid q_1$，$q_1 = p_1 u$
- $q_1$ 不可约，$p_1$ 非单位，故 $u$ 是单位
- $p_1 \sim q_1$，消去得 $p_2 \cdots p_m = u q_2 \cdots q_n$
- 由归纳法即得 ∎

---

## UFD的等价刻画

```mermaid
graph TD
    A[整环R] --> B{等价条件}
    B --> C[1. UFD定义<br/>分解存在且唯一]
    B --> D[2. 不可约=素<br/>且ACC满足]
    B --> E[3. 主理想升链<br/>且不可约素]
    B --> F[4. 分数理想群<br/>Cl(R) = 1]
    
    C --> G[ℤ是UFD]
    D --> H[k[x]是UFD]
    E --> I[ℤ[x,y]是UFD<br/>非PID]
    
    style C fill:#f9f,stroke:#333,stroke-width:2px

```

---

## 例子与反例

### PID的例子

| 环 | 类型 | 证明关键 |
|-----|------|---------|
| $\mathbb{Z}$ | PID | 欧几里得算法 |
| $k[x]$（$k$ 域） | PID | 多项式除法 |
| $\mathbb{Z}_{(p)}$ | PID | 局部化保持PID |
| $\mathbb{Z}[i]$ | PID | 欧几里得范数 |
| $\mathbb{Z}[\omega]$ ($\omega = e^{2\pi i/3}$) | PID | 欧几里得域 |

### 非PID的UFD

**例子**：$\mathbb{Z}[x]$ 是UFD但不是PID

**证明**：
- 理想 $(2, x)$ 不是主理想
- 若 $(2, x) = (f(x))$，则 $f \mid 2$ 且 $f \mid x$
- $f = \pm 1$，但 $(2, x) \neq (1)$（代入 $x=0$）

**定理**：若 $R$ 是UFD，则 $R[x]$ 是UFD（Gauss引理）

### 非UFD的整环

**例子**：$\mathbb{Z}[\sqrt{-5}]$

$$6 = 2 \cdot 3 = (1+\sqrt{-5})(1-\sqrt{-sqrt{-5}})$$

两种分解本质不同，$2$ 不可约但非素元。

---

## 类群与UFD

```mermaid
graph TD
    A[戴德金整环R] --> B[分式理想<br/>Inv(R)]
    B --> C[主分式理想<br/>P(R)]
    C --> D[类群<br/>Cl(R) = Inv(R)/P(R)]
    
    D --> E[Cl(R) = 1<br/>⇔ PID]
    D --> F[|Cl(R)| < ∞<br/>类数有限]
    
    G[数域K] --> H[整数环O_K]
    H --> I[Cl(O_K) = 1<br/>⇔ UFD]
    
    style D fill:#f9f,stroke:#333,stroke-width:2px

```

---

## 参考

- Dummit & Foote, Chapter 8
- Hungerford, *Algebra*, Chapter III.3
- Neukirch, *Algebraic Number Theory*, Chapter I
