# 同余理论 - 思维导图

## 概述

同余理论是数论的基石，由高斯系统化。它将整数的无限性"折叠"到有限剩余类环中，揭示了周期性和结构性的深刻联系。

---

## 核心思维导图

```mermaid
mindmap
  root((同余理论<br/>Congruence Theory))
    基本定义
      同余关系
        a ≡ b (mod n) ⇔ n|a-b
        等价关系
        剩余类划分
      完全剩余系
        {0,1,...,n-1}
        {1,2,...,n}
        任意代表元
      简化剩余系
        与n互素的代表元
        欧拉函数φ(n)
    模运算性质
      加减法
        a≡b, c≡d ⇒ a±c≡b±d
      乘法
        a≡b, c≡d ⇒ ac≡bd
      除法
        ac≡bc (mod n)
        需要gcd(c,n)=1
    线性同余
      一元方程
        ax ≡ b (mod n)
        有解 ⇔ gcd(a,n)|b
      解的个数
        恰有d=gcd(a,n)个解
      中国剩余定理
        模两两互素
        解唯一确定
    高次同余
      拉格朗日定理
        模p: 次数为d的多项式
        至多有d个根
      Hensel引理
        模p^k提升
        单根可唯一提升
      原根存在性
        模p存在原根
        循环群结构
    幂运算
      欧拉定理
        a^φ(n) ≡ 1 (mod n)
        gcd(a,n)=1
      费马小定理
        a^{p-1} ≡ 1 (mod p)
        p不整除a
      卡迈克尔函数
        最小指数λ(n)
    离散对数
      定义
        g^x ≡ a (mod p)
        记x=ind_g(a)
      性质
        ind(ab)≡ind(a)+ind(b)
        ind(a^k)≡k·ind(a)
      计算困难性
        离散对数问题
        密码学基础
```

---

## 同余关系结构

```mermaid
graph TD
    subgraph 等价关系
        A[整数集ℤ] --> B[模n划分]
        B --> C[剩余类]
        C --> D[ℤ/nℤ]
    end
    
    subgraph 代数结构
        D --> E[加法群<br/>循环群C_n]
        D --> F[乘法幺半群]
        F --> G[单位群U(n)<br/>阶φ(n)]
    end
    
    subgraph 核心定理
        G --> H[欧拉定理<br/>a^φ(n)≡1]
        H --> I[原根存在<br/>U(p)≅C_{p-1}]
    end
    
    style A fill:#e3f2fd
    style D fill:#fff3e0
    style G fill:#e8f5e9
```

---

## 中国剩余定理

```mermaid
graph TD
    subgraph CRT条件
        A[模数n₁,n₂,...,n_k] --> B[两两互素]
    end
    
    subgraph 同构
        B --> C[ℤ/nℤ ≅ ℤ/n₁ℤ × ... × ℤ/n_kℤ]
        C --> D[n = n₁n₂...n_k]
    end
    
    subgraph 单位群同构
        C --> E[U(n) ≅ U(n₁) × ... × U(n_k)]
        E --> F[φ(n) = φ(n₁)...φ(n_k)]
    end
    
    subgraph 应用
        D --> G[大模数计算分解]
        E --> H[RSA优化]
        G --> I[多项式插值]
    end
    
    style B fill:#e8f5e9
    style C fill:#fff3e0
    style E fill:#e3f2fd
```

---

## 同余方程求解策略

| 方程类型 | 条件 | 解法 | 解数 |
|----------|------|------|------|
| ax ≡ b (mod n) | gcd(a,n)=d | d∤b时无解 | d或0 |
| x² ≡ a (mod p) | p奇素数 | 欧拉准则 | 0,1,2 |
| x^k ≡ a (mod p) | gcd(k,p-1)=d | 指数计算 | d或0 |
| 多项式f(x)≡0 | 模p | 因式分解 | ≤deg(f) |
| 方程组 | 两两互素 | CRT | 唯一 |

---

## Hensel引理提升

```mermaid
graph LR
    subgraph 模p
        A[解f(x)≡0 (mod p)] --> B{单根?}
        B -->|是| C[唯一提升]
        B -->|否| D[多重根]
    end
    
    subgraph 提升过程
        C --> E[模p²解]
        E --> F[模p³解]
        F --> G[...]
        G --> H[p进数解]
    end
    
    subgraph 多重根处理
        D --> I[可能无解]
        D --> J[多个提升]
        D --> K[需更高精度检验]
    end
    
    style A fill:#e3f2fd
    style C fill:#e8f5e9
    style D fill:#ffcdd2
```

---

## 原根与离散对数

```mermaid
mindmap
  root((原根与离散对数<br/>Primitive Roots))
    原根存在条件
      模p
        总是存在
        共φ(p-1)个
      模p^k
        p奇素数: 存在
        p=2, k≥3: 不存在
      模2p^k
        奇素数p: 存在
    原根判定
      阶等于φ(n)
      g^d≡1的最小d
      检验: g^{φ(n)/q}≠1
    指标理论
      离散对数
        g^x ≡ a
        模p-1计算
      性质
        ind(ab)=ind(a)+ind(b)
        ind(a^k)=k·ind(a)
      换底公式
        ind_h(a)=ind_g(a)/ind_g(h)
    计算复杂性
      已知原根
        大步小步法O(√p)
        指数演算亚指数
      寻找原根
        概率多项式时间
        假设GRH确定多项式
    密码学应用
      Diffie-Hellman
        密钥交换
      ElGamal
        加密系统
      DSA
        数字签名
```

---

## 二次同余与Legendre符号

```mermaid
graph TD
    subgraph Legendre符号
        A[(a/p)] --> B[+1: 二次剩余]
        A --> C[-1: 二次非剩余]
        A --> D[0: p|a]
    end
    
    subgraph 欧拉准则
        B --> E[a^{(p-1)/2} ≡ 1]
        C --> F[a^{(p-1)/2} ≡ -1]
    end
    
    subgraph 二次互反律
        G[(p/q)(q/p) = (-1)^{(p-1)(q-1)/4}] --> H[奇素数互反]
        G --> I[补充定律
        (-1/p), (2/p)]
    end
    
    subgraph Jacobi扩展
        J[(a/n)] --> K[复合模数]
        K --> L[计算便利]
        L --> M[但(a/n)=1不保证剩余]
    end
    
    style A fill:#e3f2fd
    style G fill:#fff3e0
    style J fill:#e8f5e9
```

---

## 关键公式速查

| 公式 | 说明 |
|------|------|
| $a^{\varphi(n)} \equiv 1 \pmod{n}$ | 欧拉定理 (gcd(a,n)=1) |
| $a^{p-1} \equiv 1 \pmod{p}$ | 费马小定理 (p∤a) |
| $(\frac{a}{p}) \equiv a^{(p-1)/2} \pmod{p}$ | 欧拉准则 |
| $(\frac{p}{q})(\frac{q}{p}) = (-1)^{(p-1)(q-1)/4}$ | 二次互反律 |
| $\varphi(n) = n\prod_{p|n}(1-\frac{1}{p})$ | 欧拉函数公式 |
| $ax \equiv b \pmod{n}$ | 有解 ⇔ gcd(a,n)\|b |

---

## 学习路径

```mermaid
flowchart LR
    subgraph L1[基础]
        A[同余定义] --> B[模运算性质]
        B --> C[剩余类环]
    end
    
    subgraph L2[核心定理]
        C --> D[中国剩余定理]
        D --> E[欧拉定理]
        E --> F[费马小定理]
    end
    
    subgraph L3[深入]
        F --> G[原根理论]
        G --> H[二次剩余]
        H --> I[互反律]
    end
    
    subgraph L4[应用]
        I --> J[同余方程]
        J --> K[密码学]
        K --> L[p进数]
    end
    
    style A fill:#e3f2fd
    style D fill:#fff3e0
    style G fill:#e8f5e9
    style K fill:#ffcdd2
```

---

## 与其他概念的联系

- **群论**: ℤ/nℤ是循环群；U(n)是乘法群
- **环论**: ℤ/nℤ是环；域当且仅当n为素数
- **域论**: 有限域F_p ≅ ℤ/pℤ
- **代数几何**: 模p代数簇
- **密码学**: RSA、ElGamal、椭圆曲线
- **计算理论**: 模幂算法、多项式时间

---

*文档版本：1.0*
*创建时间：2026年4月*
*分类：数论 / 同余理论 / 思维导图*
