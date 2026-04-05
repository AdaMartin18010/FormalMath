---
msc_primary: 00A99
msc_secondary:
- 00A99
title: 统计力学 - 思维导图
processed_at: '2026-04-05'
---
# 统计力学 - 思维导图

## 概述

统计力学架起了微观力学与宏观热力学之间的桥梁，用概率统计方法研究大量粒子系统的集体行为。从Boltzmann的分子运动论到Gibbs的系综理论，再到现代的重正化群和随机矩阵理论，统计力学不仅解释了热现象的本质，也成为理解复杂系统相变和临界现象的有力工具。

---

## 核心思维导图

```mermaid
mindmap
  root((统计力学<br/>Statistical Mechanics))
    基础概念
      系综
        微正则
          E,V,N固定
          等概率原理
        正则
          T,V,N固定
          Boltzmann分布
        巨正则
          T,V,μ固定
          Fermi-Dirac/Bose-Einstein
      配分函数
        Z = ∑e^{-βEᵢ}
        热力学联系
        自由能F = -kT ln Z
      熵
        Boltzmann S = k ln W
        Gibbs S = -k ∑pᵢ ln pᵢ
    经典统计
      相空间
        6N维
        Liouville定理
      Maxwell-Boltzmann
        速度分布
        能量均分
      理想气体
        状态方程
        热容
    量子统计
      Fermi-Dirac
        费米子
        泡利不相容
        费米能
      Bose-Einstein
        玻色子
        玻色-爱因斯坦凝聚
      黑体辐射
        Planck公式
        量子起源
    相变与临界
      分类
        一级/连续
        序参量
      Ising模型
        二维精确解
        自发磁化
      重正化群
        标度变换
        不动点
        临界指数

```

---

## 系综理论框架

```mermaid
graph TD
    subgraph 微正则
        A[(E,V,N)] --> B[等概率: pᵢ = 1/Ω(E)]
        B --> C[S = k ln Ω]
    end
    
    subgraph 正则
        D[(T,V,N)] --> E[Boltzmann: pᵢ = e^{-βEᵢ}/Z]
        E --> F[Z = ∑e^{-βEᵢ}]
        F --> G[F = -kT ln Z]
    end
    
    subgraph 巨正则
        H[(T,V,μ)] --> I[p(N,i) = e^{-β(Eᵢ-μN)}/Ξ]
        I --> J[Ξ = ∑e^{βμN}Z_N]
        J --> K[Ω = -kT ln Ξ]
    end
    
    style C fill:#e3f2fd
    style G fill:#fff3e0
    style K fill:#e8f5e9

```

---

## 量子统计分布

```mermaid
mindmap
  root((量子统计))
    Fermi-Dirac
      分布函数
        f_FD(ε) = 1/(e^{β(ε-μ)}+1)
      性质
        0 ≤ f ≤ 1
        T=0:阶跃函数
      费米能
        ε_F = μ(T=0)
        费米面
      应用
        金属电子
        白矮星
    Bose-Einstein
      分布函数
        f_BE(ε) = 1/(e^{β(ε-μ)}-1)
      性质
        f > 0要求ε > μ
        μ ≤ 0
      凝聚
        T < T_c时
        宏观占据基态
      应用
        光子
        声子
        玻色-爱因斯坦凝聚
    经典极限
      高温低密度
        e^{β(ε-μ)} >> 1
        f ≈ e^{-β(ε-μ)}
      Maxwell-Boltzmann
        可区分粒子

```

---

## 分布函数对比

| 统计 | 粒子 | 波函数 | 分布函数 | 典型系统 |
|------|------|--------|----------|----------|
| Maxwell-Boltzmann | 经典 | 可区分 | e^{-β(ε-μ)} | 高温稀薄气体 |
| Fermi-Dirac | 费米子 | 反对称 | 1/(e^{β(ε-μ)}+1) | 金属电子 |
| Bose-Einstein | 玻色子 | 对称 | 1/(e^{β(ε-μ)}-1) | 光子、声子 |

---

## 相变与临界现象

```mermaid
graph TD
    subgraph Ising模型
        A[H = -J∑sᵢsⱼ - h∑sᵢ] --> B[铁磁J>0]
        B --> C[相变T_c]
        C --> D[序参量: 磁化m]
    end
    
    subgraph Landau理论
        E[F(m) = a(T-T_c)m² + bm⁴ - hm] --> F[平均场临界指数]
    end
    
    subgraph 重正化群
        G[标度变换<br/>块自旋] --> H[耦合常数流]
        H --> I[不动点: 临界行为]
        I --> J[普适类]
    end
    
    style D fill:#e3f2fd
    style F fill:#fff3e0
    style I fill:#e8f5e9

```

---

## 涨落与输运

```mermaid
mindmap
  root((涨落与输运))
    涨落-耗散
      Einstein关系
        D = μkT
        扩散与迁移率
      Nyquist定理
        噪声功率
        电阻温度
    线性响应
      Kubo公式
        响应 = ∫⟨[A(t),B(0)]⟩dt
      关联函数
        涨落-响应关系
    输运系数
      Onsager关系
        倒易关系
        Lᵢⱼ = Lⱼᵢ
      熵产生
        非平衡态

```

---

## 学习路径

```mermaid
flowchart LR
    subgraph L1[基础]
        A[热力学] --> B[概率论]
        B --> C[系综理论]
    end
    
    subgraph L2[平衡态]
        C --> D[经典统计]
        D --> E[量子统计]
    end
    
    subgraph L3[相变]
        E --> F[Ising模型]
        F --> G[临界现象]
        G --> H[重正化群]
    end
    
    subgraph L4[非平衡]
        H --> I[动力学理论]
        I --> J[涨落理论]
        J --> K[随机热力学]
    end
    
    style E fill:#e3f2fd
    style G fill:#fff3e0

```

---

## 关键公式速查

| 公式 | 说明 |
|------|------|
| $Z = \sum_i e^{-\beta E_i}$ | 正则配分函数 |
| $F = -kT \ln Z$ | Helmholtz自由能 |
| $p_i = \frac{e^{-\beta E_i}}{Z}$ | Boltzmann分布 |
| $S = -k \sum_i p_i \ln p_i$ | Gibbs熵 |
| $f_{FD}(\epsilon) = \frac{1}{e^{\beta(\epsilon-\mu)}+1}$ | Fermi-Dirac |
| $f_{BE}(\epsilon) = \frac{1}{e^{\beta(\epsilon-\mu)}-1}$ | Bose-Einstein |
| $\langle A \rangle = \frac{1}{Z}\text{Tr}(Ae^{-\beta H})$ | 热平均 |

---

## 应用领域

- **凝聚态物理**: 超导、超流、磁性
- **天体物理**: 恒星结构、白矮星
- **生物物理**: 生物分子统计、神经编码
- **信息理论**: 量子信息、Maxwell妖
- **复杂系统**: 网络、经济系统建模

---

*文档版本：1.0*
*创建时间：2026年4月*
*分类：应用数学 / 物理数学 / 思维导图*
