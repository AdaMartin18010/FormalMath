---
msc_primary: 00

  - 00A99
title: 有限元方法 - 思维导图
processed_at: '2026-04-05'
---
# 有限元方法 - 思维导图

## 概述

有限元方法(FEM)是求解偏微分方程的数值方法，通过将连续区域离散为有限个单元，用分片多项式逼近未知函数。FEM在结构力学、流体力学、电磁学等工程领域有广泛应用，是现代工程仿真的核心技术。

---

## 核心思维导图

```mermaid
mindmap
  root((有限元方法<br/>Finite Element Method))
    基本框架
      变分形式
        弱形式
        Galerkin方法
        试函数/检验函数
      离散化
        区域剖分
          三角形/四边形
          四面体/六面体
        单元构造
          Lagrange元
          Hermite元
      刚度矩阵
        单元刚度
        组装
        边界处理
    数学理论
      Sobolev空间
        H¹, H²
        范数/内积
        嵌入定理
      适定性
        Lax-Milgram
        存在唯一性
      误差分析
        Céa引理
        插值误差
        收敛阶
    单元类型
      一维
        线性元
        二次元
        三次元
      二维
        P1/P2三角形
        Q1/Q2四边形
      高阶元
        hp-FEM
        谱元法
    时间依赖
      半离散
        空间FEM
        ODE系统
      全离散
        隐式/显式
        Crank-Nicolson

```

---

## FEM流程

```mermaid
graph TD
    subgraph 连续问题
        A[强形式<br/>-Δu = f] --> B[弱形式<br/>∫∇u·∇v = ∫fv]
    end
    
    subgraph 离散化
        C[区域剖分<br/>Ω = ∪K] --> D[有限元空间<br/>V_h ⊂ V]
        D --> E[离散问题<br/>求u_h ∈ V_h]
    end
    
    subgraph 代数系统
        E --> F[刚度矩阵K] 
        F --> G[载荷向量F]
        G --> H[KU = F]
    end
    
    subgraph 求解
        H --> I[线性求解器]
        I --> J[后处理<br/>误差估计/可视化]
    end
    
    style B fill:#e3f2fd
    style E fill:#fff3e0
    style H fill:#e8f5e9

```

---

## 单元对比

| 单元 | 维数 | 节点数 | 多项式次数 | 连续性 | 应用 |
|------|------|--------|------------|--------|------|
| P1 | 2D | 3 | 1 | C⁰ | 泊松方程 |
| P2 | 2D | 6 | 2 | C⁰ | 高精度解 |
| Q1 | 2D | 4 | 双线性 | C⁰ | 四边形网格 |
| Q2 | 2D | 9 | 双二次 | C⁰ | 曲面边界 |
| P1-P0 | 2D | - | - | - | Stokes混合元 |
| MINI | 2D | - | - | inf-sup | Stokes稳定 |

---

## 误差分析

```mermaid
mindmap
  root((误差理论))
    误差类型
      截断误差
        离散化误差
        有限维逼近
      舍入误差
        浮点运算
        条件数影响
    a priori估计
      Céa引理

        ||u-u_h|| ≤ C inf||u-v_h||

      插值误差

        ||u-I_hu||_m ≤ Ch^{k+1-m}|u|_{k+1}

      收敛阶
        网格细化
        多项式提升
    a posteriori估计
      残差型
        η_K = h_K||f+Δu_h|| + ...

      对偶加权
        目标导向
        自适应
    自适应FEM
      标记策略
        最大策略
        等分布
      细化
        红绿细化
        悬挂节点

```

---

## 混合与稳定方法

```mermaid
graph TD
    subgraph 约束问题
        A[Stokes方程] --> B[速度-压力耦合]
        C[inf-sup条件] --> D[LBB条件]
    end
    
    subgraph 稳定化方法
        E[Galerkin Least Squares] --> F[稳定项]
        G[Pressure Stabilization] --> H[PSPG]
    end
    
    subgraph 混合元
        I[Taylor-Hood<br/>P2-P1] --> J[inf-sup稳定]
        K[MINI元] --> L[气泡函数]
    end
    
    style D fill:#e3f2fd
    style J fill:#e8f5e9

```

---

## 学习路径

```mermaid
flowchart LR
    subgraph L1[基础]
        A[变分法] --> B[Sobolev空间]
        B --> C[Galerkin方法]
    end
    
    subgraph L2[实现]
        C --> D[网格生成]
        D --> E[单元计算]
        E --> F[矩阵组装]
    end
    
    subgraph L3[理论]
        F --> G[误差估计]
        G --> H[收敛分析]
    end
    
    subgraph L4[高级]
        H --> I[自适应FEM]
        I --> J[混合方法]
        J --> K[非线性问题]
    end
    
    style C fill:#e3f2fd
    style G fill:#fff3e0

```

---

## 关键公式速查

| 公式 | 说明 |
|------|------|
| $a(u,v) = \int_\Omega \nabla u \cdot \nabla v$ | 双线性形式 |
| $||u-u_h||_1 \leq C h |u|_2$ | H¹误差估计 |
| $K_{ij} = \int_\Omega \nabla \phi_i \cdot \nabla \phi_j$ | 刚度矩阵元 |
| $\inf_{q_h} \sup_{v_h} \frac{b(v_h,q_h)}{||v_h||\,||q_h||} \geq \beta$ | inf-sup条件 |
| $\eta_K^2 = h_K^2||f+\Delta u_h||_{L^2(K)}^2$ | 后验误差指示子 |

---

## 应用领域

- **结构力学**: 应力分析、振动模态
- **流体力学**: CFD、多相流
- **热传导**: 温度场分布
- **电磁学**: 电磁场仿真
- **地球科学**: 地下水流动、地震波传播

---

*文档版本：1.0*
*创建时间：2026年4月*
*分类：应用数学 / 计算数学 / 思维导图*
