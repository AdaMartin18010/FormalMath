# Fubini定理证明链

## 概述
本推理树展示从单调类定理出发，经乘积测度构造，最终建立Fubini定理（积分换序）和Tonelli定理的完整推理链。

```mermaid
graph TD
    subgraph 乘积测度
        A1[可测空间乘积] --> A2[乘积σ-代数]
        A2 --> A3[乘积测度定义]
        A3 --> A4[唯一性证明]
    end
    
    subgraph 截口性质
        B1[x-截口定义] --> B2[截口可测性]
        B2 --> B3[截口测度函数]
    end
    
    subgraph 单调类定理
        C1[单调类定义] --> C2[单调类定理]
        C2 --> C3[σ-代数生成]
    end
    
    subgraph Tonelli定理
        A3 --> D1[非负可测函数]
        D1 --> D2[累次积分相等]
        D2 --> D3[∫∫f dxdy = ∫[∫f dy]dx]
    end
    
    subgraph Fubini定理
        D2 --> E1[可积函数条件]
        E1 --> E2[绝对可积]
        E2 --> E3[积分次序可交换]
    end
    
    subgraph 应用
        E3 --> F1[重积分计算]
        E3 --> F2[卷积定义]
        E3 --> F3[Fourier变换]
    end
    
    style E3 fill:#e1f5ff,stroke:#01579b,stroke-width:3px
    style D2 fill:#fff8e1,stroke:#ff6f00,stroke-width:2px
```

## 核心定理

### Tonelli定理

**定理**：设 $(X, \mathcal{A}, \mu)$ 和 $(Y, \mathcal{B}, \nu)$ 是σ-有限测度空间，$f: X \times Y \to [0, +\infty]$ 可测，则：

$$\int_{X \times Y} f d(\mu \times \nu) = \int_X \left(\int_Y f(x,y) d\nu\right) d\mu = \int_Y \left(\int_X f(x,y) d\mu\right) d\nu$$

### Fubini定理

**定理**：设 $f \in L^1(X \times Y)$，则：

1. 对几乎处处 $x$，$f(x, \cdot) \in L^1(Y)$
2. 对几乎处处 $y$，$f(\cdot, y) \in L^1(X)$
3. 累次积分相等且等于重积分

**依赖关系**：
```
乘积测度构造
    ↓
截口可测性
    ↓
单调类定理
    ↓
指示函数→简单函数→非负可测
    ↓
Tonelli定理
    ↓
Fubini定理(可积情形)
```
