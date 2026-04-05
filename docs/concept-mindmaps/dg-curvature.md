---
msc_primary: 00A99
msc_secondary:
- 00A99
title: 曲率思维导图
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 曲率思维导图

## 概述
曲率是描述空间弯曲程度的几何不变量，是黎曼几何的核心概念。不同类型的曲率从各个角度刻画了流形的几何和拓扑性质。

## 思维导图

```mermaid
mindmap
  root((曲率<br/>Curvature))
    Riemann曲率张量
      定义
        R(X,Y)Z=[∇_X,∇_Y]Z-∇_{[X,Y]}Z
        度量联络的曲率
      分量表示
        Rⁱⱼₖₗ
        四阶张量
      对称性
        反对称: Rᵢⱼₖₗ=-Rⱼᵢₖₗ
        交换: Rᵢⱼₖₗ=Rₖₗᵢⱼ
        第一Bianchi: 循环和=0
      Bianchi恒等式
        ∇R的循环和=0
        第二Bianchi恒等式
    截面曲率
      定义
        2维子空间
        K(σ)=⟨R(X,Y)Y,X⟩/(|X|²|Y|²-⟨X,Y⟩²)

      几何意义
        高斯曲率推广
        二维截面的弯曲
      等距不变
        决定Riemann曲率
        2维: 等同高斯曲率
      常曲率空间
        K=const
        球面/欧氏/双曲
    Ricci曲率
      定义
        Ric(X,Y)=tr(Z→R(Z,X)Y)
        曲率张量的迹
      分量
        Rᵢⱼ=Rᵏᵢₖⱼ
        对称2阶张量
      标量曲率
        S=gⁱʲRᵢⱼ
        Ricci的迹
      几何意义
        体积二阶变化
        测地球体积
      Einstein流形
        Ric=λg
        真空Einstein方程
    高斯曲率(2维)
      定义
        K=det(II)/det(I)
        内在定义
      Gauss绝妙定理
        K仅依赖于第一基本形
        等距不变
      全曲率
        ∫KdA
        Gauss-Bonnet定理
      符号
        K>0: 椭圆型
        K=0: 抛物型
        K<0: 双曲型
    平均曲率
      定义
        H=tr(II)/n
        第二基本形式的迹
      极小曲面
        H=0
        面积泛函临界点
      常平均曲率
        CMC曲面
        肥皂泡
    曲率比较
      截面曲率比较
        三角比较
        Toponogov定理
      Ricci比较
        体积比较
        Bishop-Gromov
      标量曲率比较
        Kazdan-Warner
        整体拓扑约束
    曲率与拓扑
      Gauss-Bonnet
        2维: ∫KdA=2πχ(M)
        拓扑约束
      Chern-Gauss-Bonnet
        高维推广
        示性数积分
      Bochner技术
        曲率→调和形式
        Betti数约束
      球定理
        1/4<pinching⇒球面
      分裂定理
        Ric≥0+直线⇔分裂
      Bonnet-Myers
        Ric>0⇒紧致有界
    曲率流
      Ricci流
        ∂g/∂t=-2Ric
        Hamilton, Perelman
      平均曲率流
        曲面演化
        奇点分析
      应用
        Poincaré猜想
        几何化猜想
    特殊曲率
      常曲率
        K=const
        空间形式
      共形平坦
        共形于欧氏
        Weyl张量为0 (n=3)
      Einstein
        Ric=λg
        齐性空间
      凯勒曲率
        复流形
        双全纯截面曲率

```

## 曲率张量的分解（维数≥4）

```

Riemann = Weyl + Ricci(trace-free) + 标量曲率部分

Rᵢⱼₖₗ = Wᵢⱼₖₗ + (1/(n-2))(gᵢₖRⱼₗ - ...) + (S/(n(n-1)))(gᵢₖgⱼₗ - ...)

```

## 曲率类型对比

| 曲率 | 阶数 | 几何意义 | 主要应用 |
|------|------|---------|---------|
| **Riemann** | 4 | 完整曲率信息 | 微分几何基础 |
| **截面曲率** | 2维子空间 | 截面弯曲 | 比较几何 |
| **Ricci** | 2 | 体积变化 | Einstein方程 |
| **标量** | 0 | 最简单的曲率 | 变分问题 |
| **高斯** | 0(2维) | 2维曲率 | 曲面论 |

## 核心定理

| 定理 | 内容 |
|------|------|
| **Gauss绝妙** | K仅依赖第一基本形（等距不变） |
| **Gauss-Bonnet** | ∫KdA = 2πχ(M) |
| **Bonnet-Myers** | Ric > 0 ⇒ 直径有限、基本群有限 |

## 关联概念
- [黎曼度量](./dg-riemannian-metric.md)
- [测地线](./dg-geodesic.md)
- [张量分析](./dg-tensor.md)
