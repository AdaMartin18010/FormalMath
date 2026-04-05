---
msc_primary: 00A99
msc_secondary:
- 00A99
title: 谱方法 - 思维导图
processed_at: '2026-04-05'
---
# 谱方法 - 思维导图

## 概述

谱方法是利用全局光滑函数(如三角函数、正交多项式)逼近解的数值方法，具有指数收敛的精度。与有限差分、有限元等局部方法不同，谱方法利用整个计算域的信息，特别适合光滑问题的计算，在流体力学、量子力学、气候模拟等领域有重要应用。

---

## 核心思维导图

```mermaid
mindmap
  root((谱方法<br/>Spectral Methods))
    基础概念
      逼近理论
        最佳逼近
        Weierstrass定理
        收敛阶
      正交多项式
        Legendre
        Chebyshev
        Fourier
      谱精度
        指数收敛
        光滑性要求
    方法分类
      Galerkin
        投影到试探空间
        弱形式
      Tau方法
        强形式+边界处理
      配置法
        伪谱方法
        配点求值
    Fourier谱方法
      周期问题
        FFT高效实现
        O(N log N)
      导数计算
        频域微分
        物理空间
      非线性项
        乘积-变换
        混叠误差
    多项式谱方法
      Legendre
        Gauss-Lobatto点
        正交性
      Chebyshev
        cos分布
        FFT可用
      极值点
        边界包含
        插值稳定
    高维与复杂域
      谱元法
        区域分解
        块谱方法
      球谐函数
        球面问题
        大气/海洋

```

---

## 谱方法流程

```mermaid
graph TD
    subgraph 连续问题
        A[PDE] --> B[选择基函数]
    end
    
    subgraph 离散化
        B --> C[Fourier: 周期]
        B --> D[Chebyshev: 有界]
        C --> E[求展开系数]
        D --> E
    end
    
    subgraph 微分方程
        E --> F[导数: û'ₖ = ik ûₖ]
        F --> G[代入方程]
        G --> H[代数方程组]
    end
    
    subgraph 求解
        H --> I[FFT求解]
        I --> J[物理解]
    end
    
    style B fill:#e3f2fd
    style F fill:#fff3e0
    style I fill:#e8f5e9

```

---

## 方法对比

| 方法 | 基函数 | 适用问题 | 收敛阶 | 计算成本 | 边界处理 |
|------|--------|----------|--------|----------|----------|
| Fourier | e^{ikx} | 周期 | 指数 | O(N log N) | 自然 |
| Chebyshev | T_n(x) | 有界域 | 指数 | O(N log N) | 配点 |
| Legendre | P_n(x) | 有界域 | 指数 | O(N²) | 配点 |
| 有限差分 | δ(x-x_i) | 通用 | 代数 | O(N) | 方便 |
| 有限元 | 分片多项式 | 复杂几何 | 代数 | O(N) | 灵活 |

---

## Fourier与Chebyshev

```mermaid
mindmap
  root((基函数选择))
    Fourier级数
      性质
        正交: ∫e^{ikx}e^{-ilx} = δ_{kl}
        周期: φ(x+2π) = φ(x)
      导数
        d/dx e^{ikx} = ik e^{ikx}
        频域对角化
      FFT
        O(N log N)
        快速变换
      混叠
        非线性项
        3/2规则
    Chebyshev
      定义
        T_n(cos θ) = cos(nθ)
        x ∈ [-1,1]
      极值点
        x_j = cos(jπ/N)
        CGL点
      优势
        非周期可用
        边界精度
        FFT适用
      权重
        (1-x²)^{-1/2}
        积分公式

```

---

## 伪谱方法

```mermaid
graph TD
    subgraph 配置法
        A[选择配点{x_j}] --> B[插值: u(x) ≈ ∑u_j l_j(x)]
        B --> C[微分矩阵D]
        C --> D[u' = Du]
    end
    
    subgraph 微分矩阵
        E[D_{ij} = l'_j(x_i)] --> F[稠密矩阵]
        F --> G[非局部]
    end
    
    subgraph 计算
        H[矩阵-向量乘] --> I[直接O(N²)]
        J[FFT] --> K[快速O(N log N)]
    end
    
    style D fill:#e3f2fd
    style G fill:#fff3e0

```

---

## 学习路径

```mermaid
flowchart LR
    subgraph L1[基础]
        A[Fourier级数] --> B[正交多项式]
        B --> C[逼近理论]
    end
    
    subgraph L2[方法]
        C --> D[Galerkin谱]
        D --> E[配置法/伪谱]
    end
    
    subgraph L3[实现]
        E --> F[FFT算法]
        F --> G[微分矩阵]
    end
    
    subgraph L4[高级]
        G --> H[谱元法]
        H --> I[复杂几何]
        I --> J[非光滑问题]
    end
    
    style D fill:#e3f2fd
    style F fill:#fff3e0

```

---

## 关键公式速查

| 公式 | 说明 |
|------|------|
| $u(x) = \sum_{k=-N/2}^{N/2} \hat{u}_k e^{ikx}$ | Fourier展开 |
| $\hat{u}_k = \frac{1}{2\pi}\int_0^{2\pi} u(x)e^{-ikx}dx$ | Fourier系数 |
| $T_n(x) = \cos(n \arccos x)$ | Chebyshev多项式 |
| $u'_j = \sum_k D_{jk} u_k$ | 伪谱微分 |
| $||u-u_N|| \leq C e^{-cN}$ | 指数收敛 |

---

## 应用领域

- **湍流模拟**: DNS大涡模拟
- **气候模式**: 球谐函数展开
- **量子力学**: 电子结构计算
- **计算电磁学**: 麦克斯韦方程组
- **金融工程**: 快速期权定价

---

*文档版本：1.0*
*创建时间：2026年4月*
*分类：应用数学 / 计算数学 / 思维导图*
