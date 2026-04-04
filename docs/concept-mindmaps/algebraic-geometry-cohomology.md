---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# 代数几何中的上同调思维导图

## 概述
上同调是代数几何的核心工具，连接了几何、代数和算术，通过不同的上同调理论（平展、ℓ进、晶体等）研究代数簇的深刻性质。

## 思维导图

```mermaid
mindmap
  root((代数几何上同调<br/>Algebraic Geometry Cohomology))
    凝聚层上同调
      导出函子定义
        Hⁱ(X,F)=RⁱΓ(X,F)
        整体截面函子
      Serre定理
        仿射簇Hⁱ=0 (i>0)
        判别仿射性
      有限性
        真映射下凝聚层上同调凝聚
        射影情形有限维
      计算
        Čech上同调
        谱序列
    Serre对偶
      光滑射影簇
        Hⁱ(X,F)≅H^{n-i}(X,F*⊗ω_X)*
        典范层ω_X
      迹映射
        Hⁿ(X,ω_X)→k
        非退化配对
      Grothendieck推广
        相对对偶
        真映射情形
    黎曼-Roch定理
      曲线情形
        χ(L)=deg(L)+1-g
        古典公式
      Hirzebruch-Riemann-Roch
        χ(E)=∫ch(E)td(X)
        示性类公式
      Grothendieck-Riemann-Roch
        真映射的相对版本
        自然变换
    étale上同调
      动机
        代数闭域特征p
        常值层有缺陷
      定义
        étale位
        层与上同调
      ℓ进上同调
        Hⁱ(X,ℚ_ℓ)
        ℓ≠p
      Weil猜想
        Deligne证明
        黎曼假设类比
      基变换
        光滑真映射
        拓扑类比
    晶体上同调
      特征p工具
        de Rham替代
        无穷小方法
      定义
        晶体位
        结构层O_{X/S}
      de Rham-Witt
        与de Rham联系
        提升情形
    de Rham上同调
      特征0情形
        Hⁱ_dR(X)
        代数de Rham
      代数构造
        超截面的层
        超上同调
      比较定理
        解析de Rham≅奇异上同调
        Grothendieck
    motive理论
      Grothendieck动机
        纯motive
        光滑射影簇对应
      混合motive
        非光滑非紧
        Deligne理论
      标准猜想
        未解决的核心问题
        Weil猜想的延伸
      实现函子
        ℓ进上同调
        de Rham
        Betti
    应用
      Weil猜想
        zeta函数的函数方程
        黎曼假设
      BSD猜想
        椭圆曲线秩与L函数
        部分结果
      Hodge理论
        Hodge分解
        纯Hodge结构
      周期映射
        族的变化
        Torelli定理
    比较同构
      周期映射
        Betti↔de Rham
        复结构
      p-adic Hodge理论
        étale↔de Rham↔晶体
        Fontaine理论
      标准猜想
        motive等价类
        猜想框架
    上同调理论列表
      Betti
        解析拓扑
        奇异上同调
      de Rham
        微分形式
        特征0
      ℓ进
        étale拓扑
        ℓ≠p
      晶体
        特征p
        无穷小
      Chow群
        代数闭链
        有理等价

```

## 代数几何中的上同调理论

```

                 标准猜想
                     ↓
Motive理论 ←────────────────→ 各种上同调理论
    │                              │
    ├─ Betti上同调 ───────────────→ 拓扑方法
    ├─ de Rham上同调 ─────────────→ 微分形式
    ├─ ℓ进上同调 ─────────────────→ 算术几何
    ├─ 晶体上同调 ────────────────→ 特征p
    └─ Chow群 ────────────────────→ 代数闭链

```

## 黎曼-Roch定理的发展

| 版本 | 适用范围 | 公式 |
|------|---------|------|
| **古典RR** | 光滑射影曲线 | χ(L) = deg(L) + 1 - g |
| **Hirzebruch-RR** | 光滑射影簇 | χ(E) = ∫ ch(E)·td(X) |
| **Grothendieck-RR** | 光滑簇间的真映射 | ch(f_!E)·td(Y) = f_*(ch(E)·td(X)) |

## Weil猜想（Deligne定理）

| 猜想 | 内容 | 证明 |
|------|------|------|
| **有理性** | Zeta函数是有理函数 | Dwork(1960) |
| **函数方程** | Z(X,q⁻ⁿT⁻¹)=±q^{nE/2}T^E Z(X,T) | Grothendieck |
| **黎曼假设** | 根的绝对值=q^{i/2} | Deligne(1974) |

## 核心定理

| 定理 | 内容 |
|------|------|
| **Serre对偶** | Hⁱ(X,F) ≅ H^{n-i}(X, F*⊗ω_X)* |
| **Deligne** | 光滑射影簇的ℓ进上同调满足Weil猜想 |
| **Grothendieck比较** | 代数de Rham ≅ 解析de Rham ≅ 奇异上同调 |

## 关联概念
- [代数簇](./algebraic-geometry-variety.md)
- [概形](./algebraic-geometry-scheme.md)
- [层](./algebraic-geometry-sheaf.md)
- [上同调](./algebraic-cohomology.md)
