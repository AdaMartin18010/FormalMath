---
msc_primary: 00

  - 00A99
title: 傅里叶级数收敛性推理树
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# 傅里叶级数收敛性推理树

## 概述
本推理树展示从Fourier系数定义出发，经Dirichlet核和核函数理论，最终建立Fourier级数收敛定理的完整推理链。

```mermaid
graph TD
    subgraph Fourier系数
        A1[正交函数系] --> A2[e^{inx}正交性]
        A2 --> A3[Fourier系数]
        A3 --> A4[aₙ,bₙ定义]
        A4 --> A5[最佳逼近]
    end
    
    subgraph 核函数理论
        B1[Dirichlet核Dₙ] --> B2[Dₙ=sin((n+1/2)x)/sin(x/2)]
        B2 --> B3[部分和表示]
        B3 --> B4[Sₙ=f*Dₙ]
    end
    
    subgraph 点态收敛
        B3 --> C1[Riemann-Lebesgue引理]
        C1 --> C2[Dini判别法]
        C1 --> C3[Dirichlet判别法]
        C2 --> C4[分段光滑收敛]
    end
    
    subgraph 一致收敛
        A5 --> D1[Weierstrass逼近]
        D1 --> D2[Fejer核]
        D2 --> D3[Cesaro求和]
        D3 --> D4[一致逼近]
    end
    
    subgraph L²理论
        A3 --> E1[Bessel不等式]
        E1 --> E2[Parseval等式]
        E2 --> E3[完备性]
        E2 --> E4[L²收敛]
    end
    
    subgraph 应用
        C4 --> F1[热方程]
        C4 --> F2[波动方程]
        E4 --> F3[信号处理]
        E4 --> F4[量子力学]
    end
    
    style C4 fill:#e1f5ff,stroke:#01579b,stroke-width:3px
    style E2 fill:#fff8e1,stroke:#ff6f00,stroke-width:2px

```

## 核心定理

### Dirichlet核

**定义**：$D_n(x) = \sum_{k=-n}^n e^{ikx} = \frac{\sin((n+1/2)x)}{\sin(x/2)}$

**部分和表示**：
$$S_n(f, x) = \frac{1}{2\pi} \int_{-\pi}^{\pi} f(x-t) D_n(t) dt$$

### Riemann-Lebesgue引理

**引理**：若 $f \in L^1([a,b])$，则：
$$\lim_{n \to \infty} \int_a^b f(x) \sin(nx) dx = 0$$

**作用**：Fourier系数趋于零：$a_n, b_n \to 0$

### Dini判别法

**定理**：若 $\int_0^\delta \frac{|\varphi_x(t)|}{t} dt < \infty$，其中 $\varphi_x(t) = f(x+t) + f(x-t) - 2f(x)$，则Fourier级数在 $x$ 收敛到 $f(x)$。

### Parseval等式

**定理**：若 $f \in L^2([-\pi, \pi])$，则：
$$\frac{1}{\pi} \int_{-\pi}^{\pi} |f(x)|^2 dx = \frac{a_0^2}{2} + \sum_{n=1}^{\infty} (a_n^2 + b_n^2)$$

## 依赖关系

```

正交函数系
    ↓
Fourier系数定义
    ↓
Dirichlet核
    ↓
Riemann-Lebesgue
    ↓
各种收敛判别法
    ↓
Parseval等式 ← L²理论

```
