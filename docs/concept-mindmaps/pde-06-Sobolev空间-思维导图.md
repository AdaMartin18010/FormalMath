---
msc_primary: 00A99
msc_secondary:
- 00A99
title: Sobolev空间 - 思维导图
processed_at: '2026-04-05'
---
# Sobolev空间 - 思维导图

## 概述

Sobolev空间是装备了弱导数L^p可积性的函数空间，为偏微分方程的弱解理论提供了自然的函数空间框架。由Sergei Sobolev在1930年代系统建立，是现代分析学的核心工具。

---

## 核心思维导图

```mermaid
mindmap
  root((Sobolev空间<br/>Sobolev Spaces))
    基本定义
      W^{k,p}(Ω)空间
        范数定义
        ‖u‖_{W^{k,p}} = (Σ_{|α|≤k}‖D^αu‖_{L^p}^p)^{1/p}

        弱导数可积性
        Banach空间结构
      H^k(Ω)空间
        p = 2情形
        Hilbert空间结构
        内积结构
        能量范数
      W_0^{k,p}(Ω)空间
        C_c^∞(Ω)完备化
        零边界条件
        Poincaré不等式
        对偶空间H^{-k}
    弱导数理论
      定义
        分布意义导数
        局部可积性
        唯一性
      存在性
        ACL刻画
        绝对连续性
        经典导数推广
      性质
        线性性
        Leibniz法则
        链式法则限制
    逼近定理
      Meyers-Serrin
        H = W定理
        C^∞在W^{k,p}稠密
        p < ∞情形
      Friedrichs磨光
        局部逼近
        紧子集上收敛
        磨光算子
      全局逼近
        边界光滑性要求
        延拓定理
        单位分解
    嵌入定理
      Sobolev嵌入
        W^{k,p} ↪ L^{p*}
        p* = np/(n-kp)
        临界指数
      紧嵌入
        Rellich-Kondrachov
        W^{k,p} ↪↪ L^q
        q < p*
      连续性嵌入
        Morrey定理
        W^{k,p} ↪ C^{m,α}
        kp > n情形
      临界情形
        Sobolev不等式极限
        Trudinger不等式
        Orlicz空间
    迹定理
      迹算子
        γ: W^{1,p}(Ω) → L^p(∂Ω)
        连续性
        满射性
      迹空间
        W^{1-1/p,p}(∂Ω)
        Besov空间
        分数阶空间
      应用
        边值问题
        Green公式
        边界条件解释
    Poincaré不等式
      经典形式
        ‖u‖_{L^p} ≤ C‖∇u‖_{L^p}
        u ∈ W_0^{1,p}
        有界区域
      推广形式
        Poincaré-Wirtinger
        平均值为零
        加权形式
      最佳常数
        Faber-Krahn
        特征值联系
        几何形状影响
    延拓定理
      整体延拓
        W^{k,p}(Ω) → W^{k,p}(ℝⁿ)
        边界光滑性要求
        线性延拓算子
      限制定理
        ℝⁿ到超平面
        迹定理联系
        逆定理
    对偶空间
      W^{-k,p'}(Ω)
        分布表示
        对偶配对
        H^{-k} = (H_0^k)*
      负范数
        范数定义
        估计方法
        应用
    分数阶空间
      H^s(ℝⁿ)
        Fourier定义
        (1+|ξ|²)^{s/2}û ∈ L²

        插值空间
      W^{s,p}定义
        Slobodeckij范数
        实插值方法
        复插值方法
      迹刻画
        边界正则性
        非整数阶
        精细分析

```

---

## Sobolev空间层级结构

```mermaid
graph TD
    A[函数空间层级] --> B[C^∞(Ω̄)]
    B --> C[W^{k+1,p}(Ω)]
    C --> D[W^{k,p}(Ω)]
    D --> E[L^p(Ω)]
    
    F[Hilbert空间特例<br/>p=2] --> G[H^{k+1}(Ω)]
    G --> H[H^k(Ω)]
    H --> I[L²(Ω)]
    
    J[零边界条件] --> K[H_0^1(Ω)]
    K --> L[H_0^k(Ω)]
    L --> M[H^{-k}(Ω) = 对偶]
    
    style A fill:#e3f2fd
    style C fill:#e8f5e9
    style F fill:#fff3e0
    style K fill:#fce4ec

```

---

## 嵌入定理体系

```mermaid
graph TD
    A[Sobolev嵌入] --> B[连续嵌入]
    A --> C[紧嵌入]
    
    B --> D[kp < n: W^{k,p} ↪ L^{p*}]
    D --> E[p* = np/(n-kp)]
    
    B --> F[kp = n: W^{k,p} ↪ L^q ∀q < ∞]
    F --> G[Trudinger: ↪ Exp L^{n'}]
    
    B --> H[kp > n: W^{k,p} ↪ C^{m,α}]
    H --> I[m = k - ⌊n/p⌋ - 1]
    
    C --> J[Rellich-Kondrachov]
    J --> K[W^{k,p} ↪↪ L^q, q < p*]
    J --> L[kp > n: W^{k,p} ↪↪ C^{m}]
    
    style A fill:#e3f2fd
    style D fill:#fff3e0
    style H fill:#e8f5e9
    style J fill:#fce4ec

```

---

## 范数与内积结构

```mermaid
graph LR
    A[W^{k,p}范数] --> B[‖u‖_{W^{k,p}}^p = Σ_{|α|≤k}‖D^αu‖_{L^p}^p]
    
    C[H^k内积] --> D[(u,v)_{H^k} = Σ_{|α|≤k}(D^αu, D^αv)_{L²}]
    
    E[等价范数] --> F[‖u‖ = ‖u‖_{L^p} + ‖∇^ku‖_{L^p}]
    
    G[Gagliardo半范数] --> H[|u|_{W^{k,p}} = ‖∇^ku‖_{L^p}]
    
    style A fill:#e3f2fd
    style C fill:#fff3e0
    style G fill:#e8f5e9

```

---

## Poincaré不等式体系

```mermaid
mindmap
  root((Poincaré不等式))
    经典形式
      有界区域
        ‖u‖_{L^p} ≤ C‖∇u‖_{L^p}
        u ∈ W_0^{1,p}(Ω)
        最佳常数与特征值
      几何意义
        零边值控制函数值
        梯度控制函数大小
        刚性估计
    Poincaré-Wirtinger
      平均值为零
        ∫_Ω u = 0
        ‖u - ū‖_{L^p} ≤ C‖∇u‖_{L^p}
      连通区域
        区域连通性要求
        Poincaré常数
        谱间隙
    加权形式
      退化权重
        与距离函数
        Muckenhoupt类
        变分问题
      Hardy不等式
        奇异权重
        最佳常数
        高维推广
    应用
      强制性验证
        变分问题
        Lax-Milgram引理
        能量估计
      特征值估计
        Faber-Krahn
        等周不等式
        几何极值

```

---

## 迹定理详解

```mermaid
graph TD
    A[W^{1,p}(Ω)] --> B[迹算子γ]
    B --> C[γ(u) = u|_{∂Ω}]
    
    D[迹性质] --> E[连续性: ‖γu‖_{L^p(∂Ω)} ≤ C‖u‖_{W^{1,p}}]
    D --> F[满射性: 存在延拓]
    D --> G[核: ker γ = W_0^{1,p}(Ω)]
    
    H[迹空间] --> I[W^{1-1/p,p}(∂Ω)]
    I --> J[Besov空间B^{1-1/p}_{p,p}]
    
    K[Green公式] --> L[∫_Ω u∂_iv = -∫_Ω ∂_iu v + ∫_{∂Ω} γ(u)γ(v)n_i]
    
    style A fill:#e3f2fd
    style B fill:#fff3e0
    style I fill:#e8f5e9

```

---

## 关键不等式速查

| 不等式 | 形式 | 条件 | 应用 |
|--------|------|------|------|
| Poincaré | $\|u\|_{L^p} \leq C\|\nabla u\|_{L^p}$ | $u \in W_0^{1,p}$ | 强制性 |
| Sobolev | $\|u\|_{L^{p^*}} \leq C\|\nabla u\|_{L^p}$ | $p < n, p^* = np/(n-p)$ | 嵌入 |
| Morrey | $\|u\|_{C^{0,\alpha}} \leq C\|u\|_{W^{1,p}}$ | $p > n, \alpha = 1-n/p$ | 连续性 |
| Gagliardo-Nirenberg | $\|D^ju\|_{L^r} \leq C\|u\|_{L^q}^a\|D^ku\|_{L^p}^{1-a}$ | 插值 | 非线性估计 |
| Hardy | $\|u/|x|\|_{L^p} \leq C\|\nabla u\|_{L^p}$ | $u \in W_0^{1,p}, p < n$ | 奇异问题 |

---

## 延拓与限制

```mermaid
graph LR
    A[延拓定理] --> B[W^{k,p}(Ω) → W^{k,p}(ℝⁿ)]
    B --> C[要求: ∂Ω ∈ C^k]
    C --> D[线性有界延拓算子]
    
    E[限制定理] --> F[W^{k,p}(ℝⁿ) → W^{k,p}(Ω)]
    F --> G[平凡限制]
    
    H[应用] --> I[整体化论证]
    H --> J[正则性传递]
    H --> K[差商方法]
    
    style A fill:#e3f2fd
    style B fill:#e8f5e9
    style E fill:#fff3e0

```

---

## 分数阶Sobolev空间

```mermaid
graph TD
    A[分数阶空间H^s] --> B[Fourier定义]
    B --> C[H^s = {u: (1+|ξ|²)^{s/2}û ∈ L²}]
    
    D[等价刻画] --> E[Slobodeckij范数]
    E --> F[‖u‖²_{W^{s,p}} = ‖u‖_{L^p}^p + ∫∫|u(x)-u(y)|^p/|x-y|^{n+sp}]
    
    G[插值空间] --> H[(H^{k_1}, H^{k_2})_{θ,2} = H^s]
    H --> I[s = (1-θ)k_1 + θk_2]
    
    J[应用] --> K[迹定理: H^1(ℝ⁺) → H^{1/2}(ℝ)]
    J --> L[边值问题正则性]
    
    style A fill:#e3f2fd
    style B fill:#fff3e0
    style G fill:#e8f5e9

```

---

## 与其他概念的联系

- **偏微分方程**: 弱解理论、正则性分析
- **变分方法**: 能量空间、极小化问题
- **Fourier分析**: H^s空间、迹定理
- **插值理论**: 复插值、实插值方法
- **调和分析**: 奇异积分、乘子理论
- **几何测度论**: 有界变差函数BV
- **非线性分析**: 紧性、集中现象

---

## 应用领域

- **椭圆型方程**: Dirichlet问题、Neumann问题、正则性
- **抛物型方程**: 发展方程、半群理论
- **变分问题**: 能量极小、特征值问题
- **流体力学**: Navier-Stokes方程、Sobolev空间框架
- **材料科学**: 相变、自由边界问题
- **几何分析**: 调和映射、曲率流
- **控制理论**: 分布参数系统、最优控制

---

*文档版本：1.0*
*创建时间：2026年4月*
*分类：偏微分方程 / Sobolev空间 / 思维导图*
*MSC 2020: 46E35*
