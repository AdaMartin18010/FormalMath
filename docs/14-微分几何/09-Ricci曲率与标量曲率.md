---
title: Ricci曲率与标量曲率
description: 详细介绍Ricci曲率和标量曲率的定义、几何意义、缩并过程，以及Einstein流形和Einstein场方程的数学基础。
msc_primary:
  - 53B20
msc_secondary:
  - 53C25
  - 83C05
processed_at: '2026-04-20'
references:
  textbooks:
    - id: lee_riemannian
      type: textbook
      title: Riemannian Manifolds
      authors:
        - John M. Lee
      publisher: Springer
      year: 1997
      msc: 53-01
    - id: do_carmo_riemannian
      type: textbook
      title: Riemannian Geometry
      authors:
        - Manfredo P. do Carmo
      publisher: Birkhäuser
      year: 1992
      msc: 53-01
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
---

# Ricci曲率与标量曲率

## 引言

Riemann曲率张量是一个庞大的对象（$n^4$ 个分量，尽管对称性减少了独立分量），在物理和几何中直接使用起来往往过于复杂。通过适当的"缩并"（contraction），我们可以得到更简洁但仍富含信息的不变量：Ricci曲率张量和标量曲率。

Ricci曲率 $\operatorname{Ric}$ 是一个对称 $(0,2)$-张量，描述体积元在测地线收敛/发散时的变化率，在广义相对论中直接出现在Einstein场方程中。标量曲率 $S$ 是Ricci曲率的进一步缩并，度量某点处体积元与欧氏空间的偏差。Einstein流形——满足 $\operatorname{Ric} = \lambda g$ 的流形——是Riemann几何和理论物理的重要研究对象。

本教程从Riemann张量的缩并出发，建立Ricci曲率、标量曲率的几何意义，分析Einstein流形的性质，并推导Einstein场方程的数学形式。

---

## 1. Ricci曲率

### 1.1 定义

**定义 1.1**。Riemann曲率张量 $R^l_{\,kij}$ 对第一和第三指标的 **缩并** 给出 **Ricci曲率张量**：
$$R_{ij} := R^k_{\,ikj} = g^{kl} R_{likj}.$$
等价地，对向量场 $X, Y$：
$$\operatorname{Ric}(X, Y) = \operatorname{tr}(Z \mapsto R(Z, X)Y).$$

**命题 1.1**。$R_{ij} = R_{ji}$，即Ricci张量对称。

**证明**：由Riemann张量的对称性 $R_{ikjl} = R_{jlik}$（对换第一对与第二对）和第一Bianchi恒等式。∎

### 1.2 几何意义

**定理 1.1（体积二阶变分）**。设 $\gamma$ 为弧长参数测地线，$\{E_1 = \dot{\gamma}, E_2, \dots, E_n\}$ 为沿 $\gamma$ 的平行标准正交标架。则Jacobi场行列式 $J(t) = \det(d\exp_p)_{t\dot{\gamma}(0)}$ 满足
$$\frac{J''(t)}{J(t)} = -\frac{1}{n-1}\operatorname{Ric}(\dot{\gamma}, \dot{\gamma}) + O(t).$$

故Ricci曲率控制测地线管的体积膨胀/收缩速率。

---

## 2. 标量曲率

**定义 2.1**。对Ricci张量再次缩并（通过度量提升一个指标后缩并）：
$$S := g^{ij} R_{ij} = \sum_{i,j} g^{ij} R_{ij} = \operatorname{tr}_g(\operatorname{Ric}).$$

**命题 2.1**。标量曲率是坐标无关的光滑函数 $S: M \to \mathbb{R}$。

**几何意义**：$S(p)$ 度量点 $p$ 处无穷小测地球体积与欧氏空间中对应球的体积的偏差：
$$\frac{\operatorname{Vol}(B_g(p, r))}{\operatorname{Vol}(B_{\mathbb{R}^n}(0, r))} = 1 - \frac{S(p)}{6(n+2)} r^2 + O(r^4).$$

---

## 3. Einstein流形

### 3.1 定义

**定义 3.1**。Riemann流形 $(M, g)$ 称为 **Einstein流形**，若存在常数 $\lambda \in \mathbb{R}$ 使
$$\operatorname{Ric} = \lambda g. \tag{E}$$

**命题 3.1**。对连通流形，$\dim M \geq 3$ 时，若 $\operatorname{Ric} = f g$（$f$ 为函数），则 $f$ 必为常数（由第二Bianchi恒等式）。

### 3.2 例子

**例 3.1**。常曲率空间是Einstein的：$\operatorname{Ric} = (n-1)K g$。

**例 3.2**。Calabi-Yau流形：Ricci平坦（$\lambda = 0$），Kähler，具有平行旋量。在弦论中作为紧化额外维度的背景几何。

**例 3.3**。$\mathbb{C}P^n$（Fubini-Study度量）：$\operatorname{Ric} = (n+1)g$。

### 3.3 二维与三维的特殊性

**命题 3.2**。任何二维流形都是Einstein的（因Ricci只有一个独立分量，$R_{ij} = K g_{ij}$）。

**命题 3.3**。三维Einstein流形必为常曲率空间（因Riemann张量由Ricci完全确定）。

---

## 4. Einstein场方程

### 4.1 Einstein张量

**定义 4.1**。**Einstein张量** 定义为
$$G := \operatorname{Ric} - \frac{1}{2} S g.$$

**命题 4.1**。$\operatorname{div} G = 0$（Bianchi恒等式的推论）。这一恒等式保证了Einstein方程与能量-动量守恒兼容。

### 4.2 Einstein场方程

**定义 4.2（Einstein场方程）**。设 $(M^{4}, g)$ 为四维Lorentz流形（物理时空）。Einstein场方程（无宇宙学常数）为
$$G = 8\pi T, \tag{EFE}$$
其中 $T$ 为能量-动量张量。

**等价形式**：$\operatorname{Ric} = 8\pi\left(T - \frac{1}{2}\operatorname{tr}(T) g\right)$。

**真空情形**（$T = 0$）：$G = 0$，等价于 $\operatorname{Ric} = 0$（因 $\dim = 4$，$\operatorname{Ric} = \frac{1}{2}S g$，$S = 0$）。

### 4.3 Schwarzschild解

**定理 4.1（Schwarzschild, 1916）**。真空Einstein方程 $\operatorname{Ric} = 0$ 的球对称静态解为
$$ds^2 = -\left(1 - \frac{2GM}{r}\right)dt^2 + \left(1 - \frac{2GM}{r}\right)^{-1}dr^2 + r^2 d\Omega^2.$$

这是描述球对称质量 $M$ 外引力场的精确解，是广义相对论的第一个精确解。

---

## 5. 与已有文档的关联

- [08-曲率张量](08-曲率张量.md)：Ricci和标量曲率由Riemann张量缩并得到。
- [10-截面曲率](10-截面曲率.md)：截面曲率是Riemann张量的二维限制。
- [26-爱因斯坦流形与常曲率空间分类](26-爱因斯坦流形与常曲率空间分类.md)：Einstein流形的系统分类。
- [变分法-基础](../../10-应用数学/变分法-基础.md)：Einstein方程可由Hilbert作用量的变分导出。

---

## 参考文献

1. A. Besse, *Einstein Manifolds*, Springer, 1987.
2. M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992. (Ch. 4)
3. J. M. Lee, *Riemannian Manifolds*, Springer, 1997. (Ch. 7)
4. R. M. Wald, *General Relativity*, Univ. Chicago Press, 1984.

---

**适用**：docs/14-微分几何/
