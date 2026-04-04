---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 数学×工程学：信号处理的调和分析

## 概述

信号处理研究信号的获取、表示、变换、滤波和解释，其数学基础根植于调和分析、线性代数和概率论。从傅里叶分析到小波变换，从滤波器设计到压缩感知，数学工具使现代数字通信和多媒体技术成为可能。

---

## 核心思维导图

```mermaid
mindmap
  root((信号处理<br/>Signal Processing))
    连续时间分析
      Fourier级数
        周期信号
        正交基
        频谱
      Fourier变换
        非周期信号
        频域表示
        卷积定理
      Laplace变换
        因果信号
        收敛域
        系统分析
      采样定理
        Nyquist率
        混叠
        重建
    离散时间分析
      DTFT
        周期频谱
        Z变换关系
        单位圆
      DFT
        有限长度
        循环卷积
        FFT算法
      Z变换
        离散系统
        ROC分析
        逆Z变换
      多速率处理
        抽取
        插值
        滤波器组
    滤波器设计
      FIR滤波器
        线性相位
        窗函数法
        频率采样
      IIR滤波器
        模拟原型
        双线性变换
        脉冲响应不变
      最优设计
        最小二乘
        切比雪夫
        椭圆滤波器
      自适应滤波
        LMS算法
        RLS算法
        收敛分析
    时频分析
      STFT
        加窗Fourier
        时频分辨率
        频谱图
      小波变换
        多分辨率
        尺度函数
        小波基
        Mallat算法
      Wigner-Ville
        时频分布
        交叉项
        Cohen类
      稀疏表示
        字典学习
        压缩感知
        稀疏恢复
    统计信号处理
      随机过程
        平稳性
        功率谱密度
        遍历性
      估计理论
        MMSE估计
        ML估计
        贝叶斯估计
      谱估计
        周期图
        Welch方法
        参数化方法
      检测理论
        假设检验
        Neyman-Pearson
        匹配滤波
    现代主题
      压缩感知
        稀疏性
        受限等距
        恢复算法
      深度学习
        CNN特征提取
        端到端学习
        神经网络滤波
      图信号处理
        图Fourier变换
        图谱分析
        图滤波器

```

---

## 变换之间的关系

```mermaid
graph TD
    subgraph 连续域
        FS[傅里叶级数<br/>周期连续] --> FT[傅里叶变换<br/>非周期连续]
        FT --> LT[Laplace变换<br/>推广到复平面]
    end
    
    subgraph 采样
        FT --> DTFT[DTFT<br/>离散时间]
        DTFT --> DFT[DFT<br/>有限离散]
    end
    
    subgraph 离散域
        Z[Z变换<br/>离散系统] --> DFT
        DFT --> FFT[FFT<br/>快速算法]
    end
    
    FT -.-> DTFT
    
    style FT fill:#e3f2fd
    style DTFT fill:#e8f5e9
    style FFT fill:#fff3e0

```

---

## 滤波器特性对比

| 类型 | 相位特性 | 设计方法 | 稳定性 | 计算复杂度 |
|------|----------|----------|--------|------------|
| FIR | 严格线性相位 | 窗函数、最优化 | 无条件稳定 | 较高(N阶) |
| IIR | 非线性相位 | 原型变换 | 需检查极点 | 较低(2N阶) |
| 自适应 | 随时间变化 | 迭代算法 | 收敛依赖 | 实时更新 |

---

## 小波变换的多分辨率

```mermaid
mindmap
  root((小波多分辨率<br/>Multiresolution Analysis))
    基本概念
      嵌套子空间
        ...⊂V₋₁⊂V₀⊂V₁⊂...
        完备性
        分离性
      尺度函数φ
        两尺度方程
        φ(t) = Σh[n]φ(2t-n)
        低通滤波器
      小波函数ψ
        小波方程
        ψ(t) = Σg[n]φ(2t-n)
        带通滤波器
    Mallat算法
      分解
        近似系数 a_j
        细节系数 d_j
        滤波+抽取
      重构
        插值+滤波
        完美重建
        正交/双正交
    常见小波
      Haar
        最简单
        不连续
        紧支撑
      Daubechies
        紧支撑正交
        消失矩
        光滑性
      样条小波
        对称性
        线性相位
        计算高效

```

---

## 压缩感知理论

```mermaid
graph LR
    subgraph 稀疏信号
        S[稀疏信号x∈ℝᴺ] --> M[测量y=Φx∈ℝᴹ]
        M --> R[恢复 min‖x‖₁ s.t. y=Φx]
    end
    
    subgraph 理论基础
        RIP[限制等距性] --> U[唯一恢复]
        U --> B[ Basis Pursuit]
    end
    
    M -.-> RIP
    R -.-> B
    
    style S fill:#e3f2fd
    style M fill:#e8f5e9
    style R fill:#fff3e0

```

---

## 前沿方向

- **量子信号处理**: 量子傅里叶变换、量子滤波
- **神经信号处理**: 脑机接口、神经编码
- **分布式处理**: 传感器网络、一致估计
- **图深度学习**: 图卷积网络、几何深度学习

---

*文档版本：1.0*
*创建时间：2026年4月*
*分类：数学×工程学 / 交叉学科*
