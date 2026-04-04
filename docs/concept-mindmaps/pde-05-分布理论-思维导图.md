# 分布理论 - 思维导图

## 概述

分布理论（广义函数论）由Schwartz系统建立，推广了经典函数概念，使得微分运算对所有广义对象都有定义。它是现代偏微分方程、调和分析和数学物理的理论基础。

---

## 核心思维导图

```mermaid
mindmap
  root((分布理论<br/>Distribution Theory))
    测试函数空间
      D(Ω)空间
        C_c^∞(Ω)函数
        紧支撑集
        收敛性定义
      S空间
        速降函数
        导数衰减条件
        Fourier变换友好
      E(Ω)空间
        C^∞(Ω)函数
        局部凸拓扑
        无支撑限制
      空间关系
        D ⊂ S ⊂ E
        稠密嵌入
        对偶关系
    分布空间
      D'(Ω): 分布
        D上的连续线性泛函
        局部可积函数嵌入
        广义函数
      S'(ℝⁿ): 缓增分布
        多项式增长控制
        Fourier变换封闭
        物理应用
      E'(Ω): 紧支分布
        紧支撑
        阶数有限
        整体表示
      结构定理
        局部表示
        有限阶分布
        紧支分布表示
    分布运算
      线性运算
        加法与数乘
        连续性保持
        线性结构
      乘法（限制）
        光滑函数乘分布
        对偶定义
        Leibniz法则
      平移与伸缩
        τ_aT, T_λ
        变量替换
        链式法则
      张量积
        乘积分布
        Fubini性质
        核定理
    分布微分
      弱导数定义
        ⟨∂^αT, φ⟩ = (-1)^{|α|}⟨T, ∂^αφ⟩
        任意阶可微
        分部积分形式
      微分性质
        微分连续性
        无穷可微性
        交换性
      例子
        Heaviside函数的导数 = δ
        log|x|的导数 = p.v.(1/x)
        分段光滑函数
    收敛与极限
      弱收敛
        D'拓扑
        逐点收敛
        一致有界原理
      完备性
        D'(Ω)完备
        Cauchy序列收敛
        逐项微分定理
      逼近定理
        D在D'中稠密
        磨光算子
        正则化序列
    支撑与局部化
      支撑集
        定义与性质
        支集与局部行为
        紧支分布
      局部分布
        限制与粘合
        单位分解
        全局延拓
      奇异支集
        正则性集合
        波前集
        奇性传播
    Fourier分析
      缓增分布的Fourier变换
        F: S' → S'
        定义延拓
        反演公式
      基本性质
        平移与调制
        微分与乘法
        卷积定理
      Paley-Wiener定理
        紧支分布
        整函数延拓
        增长性刻画
      应用
        微分方程求解
        符号演算
        拟微分算子
    基本解
      定义
        LE = δ
        基本解存在性
        非唯一性
      构造方法
        Fourier变换法
        齐次性方法
        参数变易
      例子
        Laplace方程
        热方程
        波动方程
      正则性
        椭圆算子
        亚椭圆性
        奇性传播
```

---

## 测试函数与分布空间关系

```mermaid
graph TD
    A[测试函数空间] --> B[D(Ω) = C_c^∞(Ω)]
    A --> C[S(ℝⁿ) = 速降函数]
    A --> D[E(Ω) = C^∞(Ω)]
    
    B --> B1[最小: 紧支]
    C --> C1[中等: 快速衰减]
    D --> D1[最大: 无限制]
    
    E[对偶分布空间] --> F[D'(Ω)]
    E --> G[S'(ℝⁿ)]
    E --> H[E'(Ω)]
    
    F --> F1[最大: 所有连续线性泛函]
    G --> G1[中等: 缓增]
    H --> H1[最小: 紧支分布]
    
    B -.->|对偶| F
    C -.->|对偶| G
    D -.->|对偶| H
    
    style B fill:#e8f5e9
    style C fill:#fff3e0
    style D fill:#fce4ec
    style F fill:#fce4ec
    style G fill:#fff3e0
    style H fill:#e8f5e9
```

---

## 分布微分理论

```mermaid
graph TD
    A[经典函数f] -->|不连续| B[经典导数不存在]
    B --> C[分布导数存在]
    
    C --> D[Heaviside函数H]
    D --> E[H' = δ]
    
    C --> F[|x|]
    F --> G[d/dx|x| = sgn(x)]
    
    C --> H[log|x|]
    H --> I[(log|x|)' = p.v.(1/x)]
    
    J[分布微分性质] --> K[任意阶可微]
    J --> L[连续性: T_n → T ⟹ ∂T_n → ∂T]
    J --> M[与光滑函数乘法兼容]
    
    style A fill:#ffcdd2
    style C fill:#e8f5e9
    style D fill:#e3f2fd
    style K fill:#fff3e0
```

---

## Fourier变换框架

```mermaid
graph TD
    subgraph 经典Fourier变换
        A1[L¹(ℝⁿ)] --> B1[定义: Ff(ξ) = ∫f(x)e^{-ix·ξ}dx]
        A2[L²(ℝⁿ)] --> B2[Plancherel定理: ‖Ff‖₂ = ‖f‖₂]
    end
    
    subgraph 缓增分布的Fourier变换
        A3[S(ℝⁿ)] --> B3[S(ℝⁿ)同构]
        A4[S'(ℝⁿ)] --> B4[S'(ℝⁿ)同构]
        B3 -.->|延拓| B4
    end
    
    subgraph 对偶定义
        C1[⟨F̂T, φ⟩ = ⟨T, F̂φ⟩] --> D1[对所有φ ∈ S]
    end
    
    B4 --> C1
    
    style A3 fill:#e3f2fd
    style A4 fill:#e8f5e9
    style B4 fill:#fff3e0
```

---

## 基本解理论

```mermaid
graph TD
    A[线性微分算子L] --> B[基本解E]
    B --> C[LE = δ]
    
    C --> D[存在性定理]
    D --> E[Malgrange-Ehrenpreis<br/>常系数算子总有基本解]
    
    C --> F[非唯一性]
    F --> G[齐次解+特解]
    G --> H[E + u_h也是基本解]
    
    C --> I[应用]
    I --> J[Lu = f的解: u = E*f]
    I --> K[椭圆正则性]
    I --> L[奇性传播]
    
    M[例子] --> N[ΔE = δ: E = c_n|x|^{2-n}]
    M --> O[∂_tE - ΔE = δ: E = 热核]
    M --> P[∂_t²E - ΔE = δ: E = 波动核]
    
    style A fill:#e3f2fd
    style C fill:#e8f5e9
    style E fill:#fff3e0
    style J fill:#fce4ec
```

---

## 正则化与逼近

```mermaid
mindmap
  root((正则化理论))
    磨光核
      定义
        η ∈ C_c^∞, ∫η = 1
        η_ε(x) = ε^{-n}η(x/ε)
      性质
        支集收缩
        质量守恒
        一致有界
    卷积正则化
      定义
        T_ε = T * η_ε
        光滑化分布
      收敛性
        T_ε → T in D'
        一致有界原理
      应用
        稠密性证明
        导数逼近
        方程正则化
    Sobolev嵌入
      动机
        分布的局部可积性
        正则性提升
      结果
        W^{k,p} ↪ C^m
        磨光与嵌入联系
```

---

## 关键公式速查

| 公式 | 名称 | 说明 |
|------|------|------|
| $\langle \partial^\alpha T, \varphi \rangle = (-1)^{|\alpha|}\langle T, \partial^\alpha \varphi \rangle$ | 分布导数 | 分部积分的对偶形式 |
| $H' = \delta$ | Heaviside导数 | 跳跃与Dirac分布 |
| $\langle \hat{T}, \varphi \rangle = \langle T, \hat{\varphi} \rangle$ | Fourier变换 | 对偶定义 |
| $\widehat{\partial^\alpha T} = (i\xi)^\alpha \hat{T}$ | Fourier微分 | 微分变乘法 |
| $LE = \delta$ | 基本解 | Green函数推广 |

---

## Paley-Wiener理论

```mermaid
graph TD
    A[紧支分布T ∈ E'] --> B[Fourier变换整函数延拓]
    B --> C[增长性条件]
    C --> D[|T̂(ζ)| ≤ C(1+|ζ|)^N e^{A|Im ζ|}]
    
    E[逆定理] --> F[满足增长条件的整函数]
    F --> G[对应紧支分布]
    
    H[应用] --> I[唯一性延拓]
    H --> J[边值问题]
    H --> K[波前集刻画]
    
    style A fill:#e3f2fd
    style D fill:#e8f5e9
    style F fill:#fff3e0
```

---

## 与其他概念的联系

- **Sobolev空间**: 分布是Sobolev空间的自然推广
- **弱解理论**: PDE弱解基于分布导数定义
- **Fourier分析**: 缓增分布与Fourier变换
- **偏微分方程**: 基本解、亚椭圆性、奇性传播
- **复分析**: 整函数延拓、边值问题
- **微局部分析**: 波前集、奇性分析
- **拟微分算子**: 符号演算、伪微分算子理论

---

## 应用领域

- **偏微分方程**: 弱解理论、基本解、正则性
- **调和分析**: Fourier变换、奇异积分
- **数学物理**: 量子场论、格林函数
- **信号处理**: 广义函数、脉冲响应
- **控制理论**: 脉冲控制、分布参数系统
- **概率论**: 随机过程、白噪声分析

---

*文档版本：1.0*
*创建时间：2026年4月*
*分类：偏微分方程 / 分布理论 / 思维导图*
*MSC 2020: 46Fxx*
