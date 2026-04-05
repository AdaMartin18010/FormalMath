---
msc_primary: 00A99
msc_secondary:
- 00A99
title: Sobolev空间 思维导图
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# Sobolev空间 思维导图

## 中心概念
Sobolev空间是弱可微函数构成的Banach空间，是研究偏微分方程弱解的核心理论框架。它架起了经典解与广义解之间的桥梁，是现代PDE理论的基石。

## 核心分支

```mermaid
mindmap
  root((Sobolev空间 Sobolev Space))
    弱导数
      分布导数
      弱导数定义
      分部积分
      唯一性
    空间定义
      W^{k,p}定义
      范数结构
      H^s空间
      分数阶空间
    基本性质
      Banach空间
      Hilbert空间H^k
      可分性
      自反性
    嵌入定理
      Sobolev嵌入
      Morrey不等式
      紧嵌入
      Rellich-Kondrachov
    迹定理
      边界迹
      迹算子
      迹空间
      延拓定理
    Poincaré不等式
      经典形式
      加权形式
      Friedrichs不等式
      应用
    插值理论
      实插值
      复插化
      中间空间
      精确指数
    负指数空间
      H^{-s}定义
      对偶性
      分布表示
      应用
    紧流形上
      黎曼流形
      Laplace-Beltrami
      特征函数
      热核估计
    非线性分析
      临界点理论
      变分方法
      Mountain Pass
      约束极值
    应用领域
      椭圆PDE
      抛物PDE
      流体方程
      几何分析
    历史发展
      Sobolev
      Schwartz
      Lions
      Nirenberg

```

### 定义与公理
- **弱导数**: $D^\alpha u = v$ 若 $\int u D^\alpha \phi = (-1)^{|\alpha|} \int v \phi$ 对所有测试函数 $\phi$
- **Sobolev空间**: $W^{k,p}(\Omega) = \{u \in L^p : D^\alpha u \in L^p, |\alpha| \leq k\}$
- **范数**: $\|u\|_{W^{k,p}} = \left(\sum_{|\alpha| \leq k} \|D^\alpha u\|_{L^p}^p\right)^{1/p}$

- **$H^s$空间**: Fourier定义的分数阶空间

### 基本性质
- **Banach空间**: $W^{k,p}$ 完备（$1 \leq p \leq \infty$）
- **Hilbert空间**: $H^k = W^{k,2}$ 是Hilbert空间
- **可分性**: $W^{k,p}$ 可分（$1 \leq p < \infty$）
- **自反性**: $W^{k,p}$ 自反（$1 < p < \infty$）

### 重要例子
- **$H^1(\mathbb{R}^n)$**: 一阶弱导数平方可积
- **$H_0^1(\Omega)$**: $C_c^\infty(\Omega)$ 在 $H^1$ 范数下的闭包
- **$W^{1,\infty}$**: Lipschitz函数空间
- **$H^s(\mathbb{T}^n)$**: 周期函数的分数阶空间
- **$H^{-1}$**: $H_0^1$ 的对偶空间

### 核心定理
- **Sobolev嵌入定理**: $W^{k,p} \hookrightarrow L^q$ 或 $C^{m,\alpha}$（证明思路：位势估计）
- **Rellich-Kondrachov**: 有界域上嵌入是紧的
- **Poincaré不等式**: $\|u\|_{L^p} \leq C\|\nabla u\|_{L^p}$（$u \in W_0^{1,p}$）

- **迹定理**: $W^{1,p}(\Omega) \to W^{1-1/p,p}(\partial\Omega)$ 有界满射
- **Gagliardo-Nirenberg不等式**: 插值不等式

### 相关概念
- **父概念**: 泛函分析、分布理论、偏微分方程
- **子概念**: Besov空间、Triebel-Lizorkin空间、BMO
- **相邻概念**: 变分法、椭圆方程、几何分析

### 应用领域
- **椭圆PDE**: 边值问题的弱解存在性
- **抛物PDE**: 热方程、反应扩散方程
- **流体方程**: Navier-Stokes方程、Euler方程
- **几何分析**: 极小曲面、Yamabe问题

### 历史发展
- **创立者**: Sergei Sobolev (1930年代)，研究双曲方程
- **关键发展**:
  - 1950年代：Schwartz分布理论
  - 1960年代：Lions、Stampacchia变分方法
  - 1960年代：Nirenberg、Gagliardo插值理论
  - 1970年代：Adams《Sobolev Spaces》系统阐述
- **现代研究**: 分数阶Sobolev空间、非局部方程

### 参考资源
- **推荐教材**: Adams《Sobolev Spaces》、Evans《Partial Differential Equations》
- **相关论文**: Sobolev《Méthode nouvelle à résoudre le problème de Cauchy》(1935)、Nirenberg《On elliptic partial differential equations》(1959)
- **在线资源**: PDE Notes (Lawrence C. Evans)

---

**概念链接**: [[泛函分析]] [[分布理论]] [[PDE]] [[变分法]] [[几何分析]]
