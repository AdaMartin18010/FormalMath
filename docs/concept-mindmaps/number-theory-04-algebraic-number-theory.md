# 代数数论基础 - 思维导图

## 概述

代数数论研究代数数域的算术性质，将整数理论推广到代数整数。从高斯研究二次型到克罗内克的梦想，这一领域架起了数论与代数的桥梁。

---

## 核心思维导图

```mermaid
mindmap
  root((代数数论<br/>Algebraic Number Theory))
    代数数域
      定义
        ℚ的有限扩张
        次数[K:ℚ]=dim_ℚ(K)
      本原元素
        K=ℚ(α)
        单扩张定理
      嵌入
        复嵌入: K→ℂ
        r₁个实嵌入
        2r₂对复共轭
      判别式
        d_K区分域
        基的行列式
    代数整数
      定义
        首一整系数多项式根
        构成环O_K
      整基
        O_K是自由ℤ模
        秩=[K:ℚ]
      范数与迹
        N_{K/ℚ}(α)=∏σ(α)
        Tr_{K/ℚ}(α)=∑σ(α)
      单位群
        Dirichlet单位定理
        秩=r₁+r₂-1
    理想理论
      分式理想
        I(O_K)群结构
        主理想子群P(O_K)
      唯一分解
        理想唯一分解
        类数h_K=|Cl(K)|
      素理想
        整除(p)的素理想
        分歧、惯性、分裂
      范数
        N(P)=[O_K:P]
        乘性
    素理想分解
      分解类型
        e: 分歧指数
        f: 惯性次数
        g: 素理想个数
      判别式
        p|d_K ⇔ p分歧
      分解法则
        f(x) mod p因式分解
        决定分解类型
    类域论
      希尔伯特类域
        最大非分歧阿贝尔扩张
        Gal(H/K)≅Cl(K)
      互反律
        Artin映射
        局部-整体原理
      克罗内克
        青春之梦
        分圆域生成阿贝尔扩张
```

---

## 代数数域结构

```mermaid
graph TD
    subgraph 域扩张
        A[ℚ] --> B[K=ℚ(α)]
        B --> C[次数 n=[K:ℚ]]
    end
    
    subgraph 嵌入
        C --> D[实嵌入 r₁]
        C --> E[复嵌入对 r₂]
        D --> F[n=r₁+2r₂]
    end
    
    subgraph 整数环
        B --> G[O_K=代数整数]
        G --> H[整基 α₁,...,α_n]
        H --> I[判别式 d_K]
    end
    
    subgraph 对偶
        I --> J[迹形式<br/>Tr(αβ)]
        J --> K[差积]
    end
    
    style A fill:#e3f2fd
    style G fill:#fff3e0
    style I fill:#e8f5e9
```

---

## 素理想分解

```mermaid
graph TD
    subgraph 有理素数
        A[有理素数 p] --> B{O_K中分解}
    end
    
    subgraph 分解类型
        B --> C[分裂<br/>(p)=P₁...P_g]
        B --> D[分歧<br/>e>1]
        B --> E[惯性<br/>(p)素理想]
    end
    
    subgraph 判别式判定
        F[p|d_K] --> D
        F --> G[分歧<br/>充要条件]
    end
    
    subgraph 分解公式
        C --> H[e₁f₁+...+e_gf_g=n]
        D --> H
        E --> H
    end
    
    style A fill:#e3f2fd
    style C fill:#e8f5e9
    style D fill:#ffcdd2
    style E fill:#fff3e0
```

---

## 分解类型判定

| 类型 | 条件 | 特征 | 例子(ℚ(√d)) |
|------|------|------|-------------|
| 分裂 | (d/p)=1 | (p)=P·P' | p≡1(4)时p=5,13... |
| 分歧 | p\|d_K | (p)=P² | p=2或p\|d |
| 惯性 | (d/p)=-1 | (p)素 | p≡3(4)时p=3,7... |

---

## 理想类群

```mermaid
graph TD
    subgraph 分式理想
        A[I(O_K)] --> B[非零理想群]
        B --> C[乘法结构]
    end
    
    subgraph 主理想
        D[P(O_K)] --> E[αO_K]
        E --> F[子群]
    end
    
    subgraph 类群
        C --> G[Cl(K)=I/P]
        F --> G
        G --> H[类数 h_K=|Cl(K)|]
    end
    
    subgraph 意义
        H --> I[h_K=1 ⇔ O_K是UFD]
        H --> J[测量唯一分解失败]
    end
    
    style A fill:#e3f2fd
    style G fill:#fff3e0
    style H fill:#e8f5e9
```

---

## 单位群结构

```mermaid
graph TD
    subgraph 单位群O_K*
        A[O_K*] --> B[根的单位W_K]
        A --> C[自由部分]
    end
    
    subgraph 根的单位
        B --> D[有限循环群]
        D --> E[实域: {±1}]
        D --> F[复域: 更多]
    end
    
    subgraph Dirichlet定理
        C --> G[秩=r₁+r₂-1]
        G --> H[基本单位]
        H --> I[生成整个自由部分]
    end
    
    subgraph 调节子
        I --> J[Reg(K)]
        J --> K[格的基本体积]
    end
    
    style A fill:#e3f2fd
    style G fill:#fff3e0
    style J fill:#e8f5e9
```

---

## 二次域详解

```mermaid
mindmap
  root((二次域<br/>Quadratic Fields))
    基本形式
      K=ℚ(√d)
        d无平方因子
        d∈ℤ
      判别式
        d_K=d (d≡1 mod 4)
        d_K=4d (d≡2,3 mod 4)
    整数环
      d≡2,3(4)
        O_K=ℤ[√d]
        基{1,√d}
      d≡1(4)
        O_K=ℤ[(1+√d)/2]
        基{1,(1+√d)/2}
    素数分解
      p=2
        分歧或分裂
        看d mod 8
      p奇素数
        (d/p)=1: 分裂
        (d/p)=-1: 惯性
        p|d: 分歧
    单位群
      虚二次域
        r₁=0,r₂=1
        秩=0
        有限单位
      实二次域
        r₁=2,r₂=0
        秩=1
        无限循环
        基本单位ε
    类数
      虚二次
        h_K有限计算
        类数1问题已解决
        Heegner-Stark
      实二次
        类数猜想
        连续分数展开
        基本单位关联
```

---

## 分圆域

```mermaid
graph TD
    subgraph 定义
        A[ℚ(ζ_n)] --> B[ζ_n=e^{2πi/n}]
        B --> C[次数 φ(n)]
    end
    
    subgraph 整数环
        C --> D[O_K=ℤ[ζ_n]]
        D --> E[分圆单位]
    end
    
    subgraph 素数分解
        F[p∤n] --> G[f=ord_p(n)]
        G --> H[e=1, g=φ(n)/f]
        
        I[p|n] --> J[分歧]
    end
    
    subgraph 克罗内克
        K[青春之梦] --> L[所有阿贝尔扩张⊆分圆域]
        L --> M[Kronecker-Weber定理]
    end
    
    style A fill:#e3f2fd
    style D fill:#fff3e0
    style M fill:#e8f5e9
```

---

## 关键公式速查

| 公式 | 说明 |
|------|------|
| $N_{K/\mathbb{Q}}(\alpha) = \prod_{\sigma} \sigma(\alpha)$ | 范数定义 |
| $\text{Tr}_{K/\mathbb{Q}}(\alpha) = \sum_{\sigma} \sigma(\alpha)$ | 迹定义 |
| $d_K = \det(\text{Tr}(\omega_i\omega_j))$ | 判别式 |
| $N(P) = [O_K : P]$ | 素理想范数 |
| $\sum e_i f_i = n$ | 分解公式 |
| $O_K^* \cong W_K \times \mathbb{Z}^{r_1+r_2-1}$ | Dirichlet单位定理 |

---

## 学习路径

```mermaid
flowchart LR
    subgraph L1[基础]
        A[代数数定义] --> B[整数环O_K]
        B --> C[范数与迹]
    end
    
    subgraph L2[理想]
        C --> D[素理想分解]
        D --> E[分歧理论]
        E --> F[理想类群]
    end
    
    subgraph L3[单位与几何]
        F --> G[Dirichlet单位定理]
        G --> H[闵可夫斯基几何]
        H --> I[有限类数证明]
    end
    
    subgraph L4[类域论]
        I --> J[希尔伯特类域]
        J --> K[互反律]
        K --> L[局部-整体]
    end
    
    style A fill:#e3f2fd
    style D fill:#fff3e0
    style G fill:#e8f5e9
    style K fill:#ffcdd2
```

---

## 与其他概念的联系

- **代数几何**: 数域↔函数域类比
- **表示论**: Galois表示、自守形式
- **L函数**: Dedekind ζ函数、Artin L函数
- **算术几何**: 椭圆曲线、模曲线
- **密码学**: 椭圆曲线、类群计算
- **编码理论**: 代数几何码

---

*文档版本：1.0*
*创建时间：2026年4月*
*分类：数论 / 代数数论 / 思维导图*
