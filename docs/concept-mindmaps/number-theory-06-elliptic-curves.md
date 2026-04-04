# 椭圆曲线 - 思维导图

## 概述

椭圆曲线是亏格为1的代数曲线，具有自然的阿贝尔群结构。从费马大定理的证明到现代密码学，椭圆曲线是连接数论、代数几何与计算的桥梁。

---

## 核心思维导图

```mermaid
mindmap
  root((椭圆曲线<br/>Elliptic Curves))
    定义与方程
      Weierstrass方程
        y²=x³+ax+b
        判别式Δ≠0
      射影模型
        齐次坐标
        无穷远点O
      一般形式
        特征≠2,3简化
        特征2,3特殊形式
    群结构
      几何定义
        三点共线之和为O
        切线交点
      代数公式
        加法公式
        倍点公式
      阶
        n-挠点E[n]
        有限域E(F_q)
    复乘理论
      格点解释
        ℂ/Λ≅E(ℂ)
        魏尔斯特拉斯℘函数
      模函数
        j不变量
        模曲线
      复乘
        End(E)>ℤ
        虚二次域
    有限域上的曲线
      Hasse定理
        |#E(F_q)-q-1|≤2√q
        迹a_q
      Frobenius
        π: (x,y)→(x^q,y^q)
        特征多项式
      超奇异
        p|a_q
        特殊性质
    BSD猜想
      解析秩
        L(E,s)在s=1零点阶
        ord_{s=1}L(E,s)=rank(E)
      沙群
        Ш(E)有限
        精确公式
      特殊值
        L(E,1)/Ω_E
        有理数
    密码学应用
      ECDLP
        Q=nP求n困难
        安全基础
      协议
        ECDH密钥交换
        ECDSA签名
      配对
        Weil配对
        Tate配对
        基于身份加密
```

---

## 椭圆曲线群结构

```mermaid
graph TD
    subgraph 几何定义
        A[P+Q+R=O] --> B[三点共线]
        B --> C[切线即重点]
    end
    
    subgraph 代数公式
        D[y²=x³+ax+b] --> E[斜率λ]
        E --> F[和坐标公式]
    end
    
    subgraph 群公理
        F --> G[封闭性]
        F --> H[结合律]
        F --> I[单位元O]
        F --> J[逆元-P]
    end
    
    subgraph 挠子群
        K[E[n]≅(ℤ/nℤ)²] --> L[n-挠点]
        K --> M[分圆域]
    end
    
    style A fill:#e3f2fd
    style D fill:#fff3e0
    style K fill:#e8f5e9
```

---

## Weierstrass方程形式

| 特征 | 标准形式 | 条件 |
|------|----------|------|
| ≠2,3 | y²=x³+ax+b | 4a³+27b²≠0 |
| =3 | y²=x³+a₂x²+a₄x+a₆ | 判别式≠0 |
| =2 | y²+a₁xy+a₃y=x³+a₂x²+a₄x+a₆ | 非奇异 |
| 一般 | 射影光滑三次 | 有有理点 |

---

## 复乘理论

```mermaid
graph TD
    subgraph 复环面
        A[格Λ⊂ℂ] --> B[ℂ/Λ ≅ E(ℂ)]
        B --> C[℘函数<br/>℘(z)=1/z²+Σ'(1/(z-ω)²-1/ω²)]
    end
    
    subgraph 同构
        C --> D[℘'²=4℘³-g₂℘-g₃]
        D --> E[魏尔斯特拉斯方程]
    end
    
    subgraph 模不变量
        E --> F[j(E)=1728g₂³/Δ]
        F --> G[j-不变量分类]
        G --> H[j相同⇔复同构]
    end
    
    subgraph 复乘
        I[End(E)≅O⊂虚二次域] --> J[CM椭圆曲线]
        J --> K[j(O)代数整数]
    end
    
    style A fill:#e3f2fd
    style C fill:#fff3e0
    style I fill:#e8f5e9
```

---

## 有限域上的理论

```mermaid
graph TD
    subgraph Frobenius自同态
        A[π: (x,y)→(x^q,y^q)] --> B[π∈End(E)]
        B --> C[特征多项式<br/>X²-a_qX+q]
    end
    
    subgraph Hasse定理
        D[#E(F_q)=q+1-a_q] --> E[|a_q|≤2√q]
        E --> F[√q屏障]
    end
    
    subgraph 超奇异
        G[a_q=0⇔p|a_q] --> H[超奇异椭圆曲线]
        H --> I[自同态代数可除]
    end
    
    subgraph 点计数
        J[Schoof算法<br/>多项式时间] --> K[SEA改进<br/> Elkies-Atkin]
        K --> L[实用密码学]
    end
    
    style A fill:#e3f2fd
    style E fill:#e8f5e9
    style H fill:#fff3e0
```

---

## BSD猜想详解

```mermaid
mindmap
  root((BSD猜想<br/>Birch-Swinnerton-Dyer))
    秩的猜想
      解析秩=代数秩
        ord_{s=1}L(E,s) = rank(E(ℚ))
      证据
        r=0,1时已知
        大量数值验证
      进展
        Coates-Wiles (CM, r=0)
        Gross-Zagier
        Kolyvagin (r=0,1)
    L函数
      定义
        L(E,s)=∏_p(1-a_p p^{-s}+ε_p p^{1-2s})^{-1}
        ε_p={0 p坏,1 p好}
      函数方程
        Λ(E,s)=N^{s/2}(2π)^{-s}Γ(s)L(E,s)
        Λ(E,s)=w·Λ(E,2-s)
    精确公式
      导子N_E
        坏约化素数
      周期Ω_E
        实周期或两倍
      调节子Reg(E)
        高度配对
      沙群Ш(E)
        挠部分
        猜想有限
      Tamagawa数c_p
        局部信息
    弱化形式
      L(E,1)=0⇔E有有理点
        秩≥1
      L(E,1)≠0⇒秩=0
        Kolyvagin证明
```

---

## 椭圆曲线密码学

```mermaid
graph TD
    subgraph 困难问题
        A[ECDLP] --> B[给定P,Q=kP]
        B --> C[求k困难]
        C --> D[最佳算法O(√n)]
    end
    
    subgraph 安全参数
        D --> E[256位曲线<br/>≈128位安全]
        E --> F[比RSA更高效]
    end
    
    subgraph 协议
        G[ECDH] --> H[密钥交换]
        I[ECDSA] --> J[数字签名]
        K[ECIES] --> L[加密方案]
    end
    
    subgraph 配对
        M[Weil配对<br/>e_n:E[n]×E[n]→μ_n] --> N[基于身份加密]
        N --> O[短签名<br/>BLS]
    end
    
    style A fill:#e3f2fd
    style E fill:#e8f5e9
    style M fill:#fff3e0
```

---

## 关键公式速查

| 公式 | 说明 |
|------|------|
| $y^2 = x^3 + ax + b$, $\Delta = -16(4a^3+27b^2) \neq 0$ | Weierstrass方程 |
| $P+Q = -R$ | 群加法（R=PQ直线交点） |
| $\lambda = \frac{y_2-y_1}{x_2-x_1}$ 或 $\frac{3x_1^2+a}{2y_1}$ | 斜率公式 |
| $|\#E(\mathbb{F}_q) - q - 1| \leq 2\sqrt{q}$ | Hasse界 |
| $L(E,s) = \prod_p (1 - a_p p^{-s} + \varepsilon_p p^{1-2s})^{-1}$ | Hasse-Weil L函数 |
| $\hat{h}(P) = \lim_{n\to\infty} \frac{h(2^n P)}{4^n}$ | 典范高度 |

---

## 学习路径

```mermaid
flowchart LR
    subgraph L1[基础]
        A[Weierstrass方程] --> B[群结构]
        B --> C[有理函数域]
    end
    
    subgraph L2[复理论]
        C --> D[复环面]
        D --> E[℘函数]
        E --> F[模形式]
    end
    
    subgraph L3[算术]
        F --> G[有限域上曲线]
        G --> H[Mordell-Weil定理]
        H --> I[高度理论]
    end
    
    subgraph L4[现代]
        I --> J[BSD猜想]
        J --> K[Galois表示]
        K --> L[模性定理]
    end
    
    style A fill:#e3f2fd
    style D fill:#fff3e0
    style H fill:#e8f5e9
    style L fill:#ffcdd2
```

---

## 与其他概念的联系

- **代数几何**: 曲线、雅可比簇
- **代数数论**: 分圆域、类域论
- **表示论**: Galois表示、自守形式
- **模形式**: 模性定理（谷山-志村-韦伊）
- **密码学**: ECDLP、配对密码
- **物理学**: 弦理论、卡拉比-丘

---

*文档版本：1.0*
*创建时间：2026年4月*
*分类：数论 / 椭圆曲线 / 思维导图*
