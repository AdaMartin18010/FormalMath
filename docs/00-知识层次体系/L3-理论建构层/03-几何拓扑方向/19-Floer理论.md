---
msc_primary: 00

  - 00A99
title: 19 Floer理论
processed_at: '2026-04-05'
---
# 19 Floer理论

﻿# 19-Floer理论

---

**文档编号**: FM.L3.TOP.19  
**理论名称**: Floer理论  
**MSC分类**: 57R58, 53D40  
**创建日期**: 2026年4月3日  
**版本**: 2.0

---

## 一、理论概述

### 1.1 理论定位

Floer理论是1988年由Andreas Floer创立的无穷维Morse理论，为辛几何、低维拓扑和规范场论提供了革命性的同调不变量。Floer的原始动机是证明**Arnold猜想**——辛流形上Hamilton微分同胚的不动点个数下界由Morse理论给出。为此，Floer将有限维Morse理论的框架推广到辛作用泛函（action functional）的临界点——即Hamilton系统的闭轨道——并构造了相应的"Morse复形"，即**Floer同调**。Floer理论随后发展出多个变体：拉格朗日Floer同调、瞬子Floer同调、Heegaard Floer同调等，成为现代几何拓扑的支柱之一。

### 1.2 核心思想

在有限维Morse理论中，流形的拓扑由Morse函数的临界点及其梯度流所编码。Floer观察到：在辛流形 \((M, \omega)\) 的环路空间上，**辛作用泛函**

$$
\mathcal{A}_H(\gamma) = \int_0^1 \gamma^*\theta - \int_0^1 H_t(\gamma(t))\,dt
$$

（其中 \(\theta\) 为 \(\omega\) 的标势，\(H_t\) 为时变Hamilton函数）的临界点恰为Hamilton方程的1-周期轨道。尽管环路空间是无穷维的，Floer证明了：在适当的解析框架下（Gromov紧性、Fredholm理论），可以定义连接不同临界点的"梯度流"（实为 Cauchy-Riemann 型方程的解，即伪全纯曲线），并由此构造良定义的同调群——Floer同调。

---

## 二、核心定义(L1)清单

### 定义 2.1（Hamilton向量场与作用泛函）

设 \((M, \omega)\) 为辛流形，\(H: M \times S^1 \to \mathbb{R}\) 为光滑函数（Hamilton函数）。由 \(\iota_{X_H}\omega = -dH\) 定义的向量场 \(X_H\) 称为 **Hamilton向量场**。其1-周期轨道 \(\gamma: S^1 \to M\)（满足 \(\dot{\gamma}(t) = X_{H_t}(\gamma(t))\)）是**辛作用泛函** \(\mathcal{A}_H\) 在环路空间上的临界点。

### 定义 2.2（Floer方程与伪全纯曲线）

设 \(J\) 为与 \(\omega\) 相容的殆复结构。映射 \(u: \mathbb{R} \times S^1 \to M\) 称为连接周期轨道 \(\gamma^-, \gamma^+\) 的**Floer轨迹**，若满足：

$$
\frac{\partial u}{\partial s} + J(u)\left(\frac{\partial u}{\partial t} - X_{H_t}(u)\right) = 0
$$

且 \(\lim_{s \to \pm\infty} u(s,t) = \gamma^\pm(t)\)。当 \(H = 0\) 时，此即 \((J, \omega)\)-**伪全纯曲线**方程。

### 定义 2.3（Floer复形与同调）

在适当的非退化条件（1-周期轨道的线性化Poincaré映射无特征值1）和可定向性假设下，以1-周期轨道为生成元、以Floer轨迹的模空间维数为0的组件数为边界算子的**Floer复形** \(CF_*(M, H, J)\) 是良定义的。其同调群 \(HF_*(M, H, J)\) 称为 **Hamiltonian Floer同调**，典范同构于 \((M, \omega)\) 的量子同调（或奇异同调，依设定而异）。

---

## 三、支撑定理(L2)清单

### 定理 3.1（Floer，Arnold猜想的弱形式）

设 \((M, \omega)\) 为紧辛流形，且 \([\omega]|_{\pi_2(M)} = 0\)（即辛形式在2-球面上的积分为零，或称"弱单调"条件）。则任何非退化Hamilton微分同胚 \(\phi_H^1\) 的不动点个数满足：

$$
\# \text{Fix}(\phi_H^1) \geq \sum_{i=0}^{2n} b_i(M; \mathbb{Z}_2)
$$

其中 \(b_i\) 为Betti数。若 \((M, \omega)\) 为单调的，系数可提升为 \(\mathbb{Z}\)。

### 定理 3.2（Floer同调的不变性）

Hamiltonian Floer同调 \(HF_*(M, H, J)\) 与 \(H\) 和 \(J\) 的选择无关（在适当的同伦类中），且典范同构于 \((M, \omega)\) 的普通同调 \(H_*(M; \Lambda)\)（以Novikov环为系数）。

### 定理 3.3（拉格朗日Floer同调）

设 \(L_0, L_1 \subset M\) 为紧拉格朗日子流形（满足适当的几何条件）。以 \(L_0 \cap L_1\) 的交点为生成元、以带边界条件的伪全纯条（strip）为边界的**拉格朗日Floer复形** \(CF_*(L_0, L_1)\) 定义了**拉格朗日Floer同调** \(HF_*(L_0, L_1)\)。当 \(L_0 = L_1 = L\) 时，这推广了Morse理论到拉格朗日子流形。

### 定理 3.4（Heegaard Floer同调，Ozsváth-Szabó）

对闭定向3-流形 \(Y\)，选取Heegaard分解，Ozsváth和Szabó构造了**Heegaard Floer同调** \(\widehat{HF}(Y)\)，以对称积空间中的拉格朗日交为模型。这是3-流形和扭结分类的最强不变量之一，满足手术正合列（surgery exact sequence），可计算扭结的genus和纤维性。

---

## 四、理论结构图

```
Floer理论
├── Hamiltonian Floer同调
│   ├── 辛作用泛函与1-周期轨道
│   ├── Floer方程（s-dependent Cauchy-Riemann）
│   ├── Gromov紧性与模空间
│   └── 与量子同调/奇异同调的同构（PSS映射）
├── 拉格朗日Floer同调
│   ├── 拉格朗日交点（生成元）
│   ├── 伪全纯条（边界算子）
│   └── Fukaya范畴（A_∞-范畴结构）
├── 瞬子Floer同调
│   ├── 3-流形上的Yang-Mills泛函
│   ├── ASD瞬子（反自对偶联络）
│   └── Atiyah-Floer猜想（ instanton ≅ Lagrangian Floer）
└── Heegaard Floer理论
    ├── Heegaard分解与对称积
    ├── 扭结Floer同调 HFK(K)
    └── 4-维流形的切片亏格与边界映射
```

---

## 五、向L4前沿的开放问题

1. **Arnold猜想的完全解决**：一般辛流形（不满足弱单调条件）上的Arnold猜想仍部分开放，高维情形和一般系数下的精细下界是活跃方向。
2. **同调镜像对称（Kontsevich）**：Fukaya范畴（拉格朗日Floer理论的范畴化）与导出范畴 of coherent sheaves 之间的等价性，是当代数学物理中最重要的猜想之一。
3. **Atiyah-Floer猜想**：对3-流形 \(Y\) 的分解 \(Y = Y_1 \cup_\Sigma Y_2\)，瞬子Floer同调 \(HF^{\text{inst}}(Y)\) 是否同构于拉格朗日Floer同调 \(HF(L_{Y_1}, L_{Y_2})\)？部分情形已被证明（Salamon-Wehrheim）。
4. **组合化与算法化**：Heegaard Floer同调虽然有组合定义，但其完全组合算法仍在发展中（如Manolescu-Ozsváth-Thurston的工作）。

---

**文档信息**
- **创建日期**: 2026年4月3日
- **状态**: 已完成扩充
