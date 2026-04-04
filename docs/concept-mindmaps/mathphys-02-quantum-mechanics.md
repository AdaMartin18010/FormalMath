---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 量子力学数学 - 思维导图

## 概述

量子力学的数学基础建立在泛函分析和算子理论之上。Hilbert空间、自伴算子和谱理论构成了量子力学的数学框架，为描述微观世界提供了严格的数学语言。

---

## 核心思维导图

```mermaid
mindmap
  root((量子力学数学<br/>Mathematical Quantum Mechanics))
    Hilbert空间
      态空间
        复可分Hilbert空间
        L²(Rⁿ)空间
      内积结构
        ⟨φ|ψ⟩
        共轭对称
        正定性
      范数与距离
        ‖ψ‖ = √⟨ψ|ψ⟩
        完备性
      标准正交基
        可数基存在
        展开定理
    算子理论
      可观测量
        自伴算子<br/>A=A†
        有界/无界
      位置算子
        x̂ψ = xψ
        本质自伴
      动量算子
        p̂ = -iℏ∇
        Fourier变换联系
      哈密顿量
        Ĥ = p̂²/2m + V(x̂)
        薛定谔方程
    谱理论
      谱分解
        投影值测度
        谱定理
      离散谱
        束缚态
        本征函数
      连续谱
        散射态
        广义本征函数
      物理诠释
        测量结果
        概率分布
    量子动力学
      薛定谔方程
        iℏ∂ψ/∂t = Ĥψ
        含时演化
      酉演化
        U(t) = exp(-iĤt/ℏ)
        保内积
      Heisenberg绘景
        算子随时间变
      相互作用绘景
    不确定性原理
      标准差定义
      Robertson不等式
        ΔAΔB ≥ |⟨[A,B]⟩|/2
      位置-动量
        ΔxΔp ≥ ℏ/2
    复合系统
      张量积
        H₁⊗H₂
      纠缠态
        不可分离态
      测量公设
        投影公设
```

---

## 量子力学公理体系

```mermaid
graph TD
    subgraph 公理I: 态空间
        A[物理态] --> B[Hilbert空间H中的射线]
    end
    
    subgraph 公理II: 可观测量
        C[物理量] --> D[自伴算子A]
        D --> E[谱=可能测量值]
    end
    
    subgraph 公理III: 测量
        F[测量A得aₙ] --> G[概率|⟨φₙ|ψ⟩|²]
        G --> H[态坍缩到φₙ]
    end
    
    subgraph 公理IV: 演化
        I[含时演化] --> J[薛定谔方程<br/>iℏ∂ψ/∂t = Ĥψ]
    end
    
    B --> C
    E --> F
    H --> I
```

---

## 重要算子

| 算子 | 定义 | 谱性质 | 物理意义 |
|------|------|--------|----------|
| **位置** $\hat{x}$ | $\hat{x}\psi(x) = x\psi(x)$ | 连续谱 $\mathbb{R}$ | 位置测量 |
| **动量** $\hat{p}$ | $\hat{p} = -i\hbar\frac{d}{dx}$ | 连续谱 $\mathbb{R}$ | 动量测量 |
| **哈密顿** $\hat{H}$ | $\hat{H} = \frac{\hat{p}^2}{2m} + V(\hat{x})$ | 离散+连续 | 能量测量 |
| **角动量** $\hat{L}$ | $\hat{L} = \hat{x} \times \hat{p}$ | 离散 $|l(l+1)\hbar^2|$ | 角动量测量 |
| **自旋** $\hat{S}$ | 有限维矩阵 | 离散 | 内禀角动量 |

---

## 谱定理与物理解释

```mermaid
graph LR
    subgraph 谱分解
        A[自伴算子A] --> B[谱测度E(λ)]
        B --> C[A = ∫λdE(λ)]
    end
    
    subgraph 物理诠释
        D[测量A] --> E[结果∈谱σ(A)]
        E --> F[概率测度<br/>⟨ψ|E(·)|ψ⟩]
    end
    
    G[离散谱] --> H[束缚态<br/>本征函数可归一化]
    G --> I[本征值可数]
    
    J[连续谱] --> K[散射态<br/>广义本征函数]
    
    A --> D
```

---

## 量子动力学绘景

```mermaid
graph TD
    subgraph Schrödinger绘景
        A[态随时间变<br/>ψ(t) = U(t)ψ(0)]
        B[算子不变]
    end
    
    subgraph Heisenberg绘景
        C[态不变<br/>ψ_H = ψ(0)]
        D[算子随时间变<br/>A(t) = U†(t)AU(t)]
    end
    
    subgraph 相互作用绘景
        E[自由演化分离<br/>ψ_I(t) = U₀†(t)ψ(t)]
        F[相互作用算子]
    end
    
    A <--> C
    B <--> D
```

---

## 不确定性原理

```mermaid
mindmap
  root((不确定性原理))
    数学形式
      Robertson不等式
        ΔAΔB ≥ |⟨[A,B]⟩|/2
      标准差定义
        ΔA = √(⟨A²⟩-⟨A⟩²)
    典型例子
      位置-动量
        ΔxΔp ≥ ℏ/2
      能量-时间
        ΔEΔt ≥ ℏ/2
      角动量
        [Lᵢ,Lⱼ] = iℏεᵢⱼₖLₖ
    物理意义
      非对易量
        不能同时精确测量
      量子涨落
        内禀性质
      与经典区别
        非测量干扰
```

---

## 纠缠与复合系统

```mermaid
graph TD
    A[复合系统] --> B[Hilbert空间张量积<br/>H₁⊗H₂]
    
    B --> C[可分态<br/>|ψ⟩ = |φ₁⟩⊗|φ₂⟩]
    B --> D[纠缠态<br/>不可写成张量积]
    
    D --> E[Bell态<br/>最大纠缠]
    D --> F[量子关联<br/>非经典]
    
    G[测量纠缠粒子] --> H[非定域关联]
    H --> I[EPR佯谬]
    H --> J[Bell不等式违背]
    
    style C fill:#e3f2fd
    style D fill:#ffcdd2
    style E fill:#fce4ec
```

---

## 学习路径

```mermaid
flowchart LR
    subgraph L1[数学基础]
        A[线性代数] --> B[Hilbert空间]
        B --> C[泛函分析]
    end
    
    subgraph L2[量子力学]
        C --> D[算子理论]
        D --> E[谱理论]
    end
    
    subgraph L3[物理应用]
        E --> F[薛定谔方程]
        F --> G[测量理论]
    end
    
    subgraph L4[高级]
        G --> H[纠缠理论]
        H --> I[量子信息]
    end
    
    style A fill:#e3f2fd
    style B fill:#e3f2fd
    style C fill:#e3f2fd
    style D fill:#fff3e0
    style E fill:#fff3e0
    style F fill:#e8f5e9
    style G fill:#e8f5e9
    style H fill:#fce4ec
    style I fill:#fce4ec
```

---

## 与其他概念的联系

- **泛函分析**: 无界算子理论、谱分析
- **偏微分方程**: 薛定谔方程的解
- **概率论**: 测量结果的统计诠释
- **李群李代数**: 对称性与守恒量
- **量子场论**: 无穷自由度推广
- **量子信息**: 纠缠、量子计算

---

## 参考

- 《量子力学的数学基础》von Neumann
- 《Mathematical Methods in Quantum Mechanics》Teschl
- 《Quantum Theory for Mathematicians》Hall

---

*文档版本：1.1（质量提升版）*
*最后更新：2026年4月*
*分类：数学物理 / 量子力学 / 思维导图*
