---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 场论 - 思维导图

## 概述

场论研究物理场的数学结构和动力学方程，从经典电磁场到规范场论，是理论物理的核心理论框架。拉格朗日场论提供了统一描述各种场的方法，而规范对称性原理则揭示了相互作用的基本结构，成为粒子物理标准模型的理论基础。

---

## 核心思维导图

```mermaid
mindmap
  root((场论<br/>Field Theory))
    经典场论
      拉格朗日形式
        作用量S = ∫L d⁴x
        场变分
        Euler-Lagrange方程
      正则形式
        共轭动量
        哈密顿密度
        泊松括号
      Noether定理
        对称性→守恒流
        能量-动量张量
    相对论场论
      Lorentz群
        洛伦兹变换
        旋量表示
      标量场
        Klein-Gordon方程
        实/复标量场
      矢量场
        Proca方程
        电磁场A_μ
      旋量场
        Dirac方程
        γ矩阵
        旋量双线性
    规范场论
      Abel规范
        U(1)
        电磁学
        规范不变性
      非Abel规范
        SU(N)
        杨-Mills理论
        自相互作用
      标准模型
        SU(3)×SU(2)×U(1)
        三代费米子
        Higgs机制
    路径积分
      生成泛函
        Z[J] = ∫Dφ e^{i(S+∫Jφ)}
        关联函数
      微扰论
        Feynman图
        重整化
      非微扰
        瞬子
        格点场论

```

---

## 场论构造

```mermaid
graph TD
    subgraph 拉格朗日场论
        A[场φ(x)] --> B[拉格朗日密度ℒ(φ,∂φ)]
        B --> C[作用量S = ∫d⁴x ℒ]
        C --> D[δS = 0 → Euler-Lagrange]
        D --> E[∂_μ(∂ℒ/∂(∂_μφ)) = ∂ℒ/∂φ]
    end
    
    subgraph 守恒定律
        F[对称变换] --> G[Noether流j^μ]
        G --> H[∂_μj^μ = 0]
        H --> I[守恒荷Q = ∫j⁰d³x]
    end
    
    style B fill:#e3f2fd
    style E fill:#fff3e0
    style I fill:#e8f5e9

```

---

## 自由场方程

```mermaid
mindmap
  root((自由场))
    标量场
      Klein-Gordon
        (∂² + m²)φ = 0
        自旋0
        玻色子
      解
        平面波
        产生湮灭算符
    旋量场
      Dirac方程
        (iγ^μ∂_μ - m)ψ = 0
        自旋1/2
        费米子
      性质
        正负能量解
        手征性
        电荷共轭
    矢量场
      Maxwell
        ∂_μF^μν = 0
        自旋1
        无质量
      Proca
        (∂² + m²)A^ν = 0
        有质量
    传播子
      费曼传播子
        时序格林函数
        虚部贡献

```

---

## 场类型对比

| 场 | 方程 | 自旋 | 统计 | 粒子例子 |
|----|------|------|------|----------|
| 实标量 | (∂²+m²)φ = 0 | 0 | 玻色子 | Higgs |
| 复标量 | (∂²+m²)φ = 0 | 0 | 玻色子 | π介子 |
| Dirac | (i∂̸-m)ψ = 0 | 1/2 | 费米子 | 电子、夸克 |
| Weyl | σ^μ∂_μχ = 0 | 1/2 | 费米子 | 中微子 |
| Maxwell | ∂_μF^μν = 0 | 1 | 玻色子 | 光子 |
| Proca | (∂²+m²)A^ν = 0 | 1 | 玻色子 | W/Z玻色子 |
| Rarita-Schwinger | - | 3/2 | 费米子 | 引力微子 |

---

## 规范场论

```mermaid
graph TD
    subgraph U(1)电磁
        A[规范变换<br/>ψ → e^{iα(x)}ψ] --> B[协变导数D_μ = ∂_μ + ieA_μ]
        B --> C[场强F_μν = ∂_μA_ν - ∂_νA_μ]
        C --> D[Maxwell方程]
    end
    
    subgraph SU(N)杨-Mills
        E[规范变换<br/>ψ → Uψ] --> F[协变导数D_μ = ∂_μ - igA_μ^aT^a]
        F --> G[场强F_μν = ∂_μA_ν - ∂_νA_μ + g[A_μ,A_ν]]
        G --> H[三胶子/四胶子顶点]
    end
    
    subgraph 标准模型
        I[SU(3)_c × SU(2)_L × U(1)_Y] --> J[Higgs机制]
        J --> K[质量产生]
    end
    
    style B fill:#e3f2fd
    style F fill:#fff3e0
    style I fill:#e8f5e9

```

---

## 路径积分量子化

```mermaid
mindmap
  root((路径积分))
    定义
      Z = ∫Dφ exp(iS[φ])
        所有场构型
        经典极限ℏ→0
      生成泛函
        Z[J] = ∫Dφ exp(i(S+∫Jφ))
        W[J] = -i ln Z
    微扰展开
      自由理论
        高斯积分
        传播子
      相互作用
        微扰级数
        Feynman图
    重整化
      发散
        圈图积分
        正规化
      抵消项
        重整化常数
        跑动耦合
    非微扰
      瞬子
        经典解
        隧穿效应
      格点
        离散化
        蒙特卡洛

```

---

## 学习路径

```mermaid
flowchart LR
    subgraph L1[经典场]
        A[拉格朗日力学] --> B[连续系统]
        B --> C[相对论场论]
    end
    
    subgraph L2[量子场]
        C --> D[自由场量子化]
        D --> E[相互作用]
        E --> F[微扰论]
    end
    
    subgraph L3[规范场]
        F --> G[U(1)规范]
        G --> H[杨-Mills理论]
        H --> I[标准模型]
    end
    
    subgraph L4[高级]
        I --> J[重整化群]
        J --> K[非微扰方法]
        K --> L[超对称/弦论]
    end
    
    style D fill:#e3f2fd
    style H fill:#fff3e0

```

---

## 关键公式速查

| 公式 | 说明 |
|------|------|
| $S = \int d^4x \mathcal{L}$ | 作用量 |
| $\partial_\mu\left(\frac{\partial \mathcal{L}}{\partial(\partial_\mu \phi)}\right) = \frac{\partial \mathcal{L}}{\partial \phi}$ | Euler-Lagrange |
| $j^\mu = \frac{\partial \mathcal{L}}{\partial(\partial_\mu \phi)}\delta\phi$ | Noether流 |
| $(\partial^2 + m^2)\phi = 0$ | Klein-Gordon |
| $(i\gamma^\mu\partial_\mu - m)\psi = 0$ | Dirac方程 |
| $\mathcal{L}_{YM} = -\frac{1}{4}F^a_{\mu\nu}F^{a\mu\nu}$ | Yang-Mills拉氏量 |

---

## 应用领域

- **粒子物理**: 标准模型计算
- **凝聚态**: 有效场论、拓扑序
- **宇宙学**: 暴胀模型、暗物质
- **引力**: 引力量子化尝试
- **数学**: 拓扑不变量、表示论

---

*文档版本：1.0*
*创建时间：2026年4月*
*分类：应用数学 / 物理数学 / 思维导图*
