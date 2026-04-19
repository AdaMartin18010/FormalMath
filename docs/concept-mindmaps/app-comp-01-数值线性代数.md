---
msc_primary: 00

  - 00A99
title: 数值线性代数 - 思维导图
processed_at: '2026-04-05'
---
# 数值线性代数 - 思维导图

## 概述

数值线性代数是科学计算的核心基础，研究矩阵和向量的高效、稳定计算方法。从线性方程组求解、特征值计算到矩阵分解，这些算法支撑着现代科学、工程和金融的几乎所有数值计算任务。

---

## 核心思维导图

```mermaid
mindmap
  root((数值线性代数<br/>Numerical Linear Algebra))
    线性方程组
      直接法
        Gauss消去
          部分选主元
          计算复杂度O(n³)
        LU分解
          PA = LU
          前代/回代
        Cholesky分解
          A = LLᵀ
          对称正定
      迭代法
        古典迭代
          Jacobi
          Gauss-Seidel
          SOR
        Krylov子空间
          CG
          GMRES
          BiCGSTAB
    特征值问题
      幂法
        最大模特征值
        反幂法
      QR算法
        收缩技术
        隐式位移
      Lanczos/Arnoldi
        大型稀疏
        Ritz值
    矩阵分解
      SVD
        A = UΣVᵀ
        低秩逼近
      QR分解
        正交化
        最小二乘
      特征分解
        正规矩阵
        A = QΛQᴴ
    特殊结构
      稀疏矩阵
        CSR格式
        迭代优势
      带状矩阵
        追赶法
        降复杂度

```

---

## 直接法求解

```mermaid
graph TD
    subgraph LU分解
        A[A] --> B[消去: 化为上三角U]
        B --> C[记录乘数: 得下三角L]
        C --> D[PA = LU]
    end
    
    subgraph 求解步骤
        D --> E[解Ly = Pb: 前代]
        E --> F[解Ux = y: 回代]
    end
    
    subgraph 选主元
        G[部分选主元] --> H[行交换]
        I[全主元] --> J[行列交换]
    end
    
    style D fill:#e3f2fd
    style F fill:#e8f5e9

```

---

## 迭代法对比

| 方法 | 适用矩阵 | 收敛条件 | 计算/步 | 特点 |
|------|----------|----------|---------|------|
| Jacobi | 一般 | 严格对角占优 | O(n²) | 并行友好 |
| Gauss-Seidel | 一般 | 严格对角占优/HPD | O(n²) | 串行更快 |
| SOR | 一般 | 最优ω | O(n²) | 加速GS |
| CG | 对称正定 | - | O(n²) | 最优迭代 |
| GMRES | 一般 | - | O(kn²) | 非对称首选 |
| BiCGSTAB | 一般 | - | O(n²) | 短递推 |

---

## Krylov子空间方法

```mermaid
mindmap
  root((Krylov方法))
    子空间定义
      Kₘ(A,b)
        span{b, Ab, ..., Aᵐ⁻¹b}
        维数m
      投影原理
         Galerkin条件
        Petrov-Galerkin
    共轭梯度CG
      适用
        对称正定
      性质
        有限步收敛
        最优能量范数
      预处理
        不完全Cholesky
        多重网格
    GMRES
      最小残差

        ||Ax-b||₂最小

      Arnoldi过程
        正交化
        Hessenberg矩阵
      重启
        GMRES(k)
        内存限制
    其他方法
      MINRES
        对称不定
      BiCGSTAB
        非对称短递推
      QMR
        光滑收敛

```

---

## 特征值算法

```mermaid
graph TD
    subgraph 稠密矩阵
        A[Householder<br/>三对角化] --> B[QR迭代]
        B --> C[对角矩阵<br/>特征值]
    end
    
    subgraph 大型稀疏
        D[Lanczos<br/>三对角投影] --> E[Ritz值近似]
        E --> F[重启/精化]
    end
    
    subgraph 部分特征值
        G[幂法] --> H[最大模特征值]
        I[反幂法+位移] --> J[特定区域特征值]
        K[子空间迭代] --> L[多个特征值]
    end
    
    style B fill:#e3f2fd
    style E fill:#fff3e0

```

---

## SVD与最小二乘

```mermaid
mindmap
  root((SVD应用))
    分解定义
      A = UΣVᵀ
        U,V正交
        Σ对角
      计算
        Golub-Kahan
        分治算法
    应用
      最小二乘
        x = VΣ⁺Uᵀb
        数值稳定
      低秩逼近
        Aₖ = UₖΣₖVₖᵀ
        Eckart-Young定理
      伪逆
        A⁺ = VΣ⁺Uᵀ
      主成分分析
        协方差特征值

```

---

## 学习路径

```mermaid
flowchart LR
    subgraph L1[基础]
        A[向量/矩阵运算] --> B[浮点算术]
        B --> C[条件数]
    end
    
    subgraph L2[直接法]
        C --> D[Gauss消去]
        D --> E[LU/Cholesky]
    end
    
    subgraph L3[迭代法]
        E --> F[古典迭代]
        F --> G[Krylov方法]
    end
    
    subgraph L4[高级]
        G --> H[特征值算法]
        H --> I[SVD]
        I --> J[预处理技术]
    end
    
    style D fill:#e3f2fd
    style G fill:#fff3e0

```

---

## 关键公式速查

| 公式 | 说明 |
|------|------|
| $\kappa(A) = \|A\|\|A^{-1}\|$ | 条件数 |
| $PA = LU$ | LU分解带选主元 |
| $A = LL^T$ | Cholesky分解 |
| $x_{k+1} = x_k + \alpha_k r_k$ | 最速下降 |
| $||Ax-b||_2$最小化 | 最小二乘 |
| $A = U\Sigma V^T$ | SVD分解 |
| $A = QR$ | QR分解 |

---

## 应用领域

- **科学计算**: 有限元、有限差分求解
- **数据科学**: 主成分分析、推荐系统
- **机器学习**: 优化算法、神经网络
- **图形学**: 物理模拟、几何处理
- **金融工程**: 协方差矩阵、风险模型

---

*文档版本：1.0*
*创建时间：2026年4月*
*分类：应用数学 / 计算数学 / 思维导图*
