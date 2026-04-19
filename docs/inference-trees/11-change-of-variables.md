---
msc_primary: 00

  - 00A99
title: 变量替换公式推导
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# 变量替换公式推导

## 概述
本推理树展示从线性变换的面积变化出发，经Jacobi行列式的几何意义，最终建立一般变量替换公式的完整推理链。

```mermaid
graph TD
    subgraph 线性变换
        A1[线性映射] --> A2[体积变化率]
        A2 --> A3[|det T|几何意义]

        A3 --> A4[平行多面体体积]
    end
    
    subgraph 可微映射局部线性
        B1[可微映射] --> B2[局部线性逼近]
        B2 --> B3[Jacobi矩阵]
        B3 --> B4[|det Df|局部体积比]

    end
    
    subgraph 简单情形
        A4 --> C1[线性变量替换]
        C1 --> C2[∫f(Ax)|det A|dx]

    end
    
    subgraph 一般公式
        B4 --> D1[非线性变量替换]
        D1 --> D2[∫f(φx)|det Dφ|dx]

        C2 --> D2
    end
    
    subgraph 证明框架
        D2 --> E1[简单函数逼近]
        E1 --> E2[开集上成立]
        E2 --> E3[一般可测集]
    end
    
    subgraph 应用
        D2 --> F1[极坐标变换]
        D2 --> F2[球坐标变换]
        D2 --> F3[一般曲线坐标]
    end
    
    style D2 fill:#e1f5ff,stroke:#01579b,stroke-width:3px
    style F1 fill:#fff8e1,stroke:#ff6f00,stroke-width:2px

```

## 核心定理

### 变量替换公式

**定理**：设 $U, V \subset \mathbb{R}^n$ 是开集，$\varphi: U \to V$ 是 $C^1$ 微分同胚，$f \in L^1(V)$，则：

$$\int_V f(y) dy = \int_U f(\varphi(x)) |\det D\varphi(x)| dx$$

### 证明思路

**步骤1**：线性情形由Riemann积分定义直接验证

**步骤2**：局部到整体通过可数可加性

**步骤3**：利用可微映射的局部线性性质

### 常用坐标变换

| 坐标系 | 变换公式 | Jacobi行列式 |
|--------|----------|--------------|
| 极坐标 | $x = r\cos\theta, y = r\sin\theta$ | $r$ |
| 柱坐标 | 同上+$z = z$ | $r$ |
| 球坐标 | $x = r\sin\phi\cos\theta$ 等 | $r^2\sin\phi$ |

## 依赖关系

```

行列式几何意义
    ↓
线性变换积分公式
    ↓
可微映射局部线性
    ↓
简单函数逼近
    ↓
一般变量替换公式

```
