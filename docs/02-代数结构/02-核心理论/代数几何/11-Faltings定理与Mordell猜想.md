---
title: "11 Faltings定理与Mordell猜想 / Faltings' Theorem and the Mordell Conjecture"
msc_primary: "11G30"
msc_secondary: ["14G05", "14H25", "11D41"]
processed_at: '2026-04-05'
---
# 11 Faltings定理与Mordell猜想 / Faltings' Theorem and the Mordell Conjecture

**主题编号**: B.13.11  
**创建日期**: 2026年4月3日  
**最后更新**: 2026年4月3日  
**MSC分类**: 11G30 (曲线的有理点), 14G05 (算术几何中的有理点), 14H25 (算术曲线), 11D41 (高次Diophantine方程)  
**国际对齐**: Abel Prize 2026专题 (Gerd Faltings); Faltings (1983); Cornell–Silverman *Arithmetic Geometry*; Bombieri–Gubler

---

## 目录 / Table of Contents

- [1 引言 / Introduction](#1-引言-introduction)
- [2 历史背景：从Mordell到Shafarevich](#2-历史背景从mordell到shafarevich)
  - [2.1 Mordell的原始猜想](#21-mordell的原始猜想)
  - [2.2 Siegel定理与Shafarevich猜想](#22-siegel定理与shafarevich猜想)
- [3 Faltings定理的陈述](#3-faltings定理的陈述)
  - [3.1 有理性点的有限性](#31-有理性点的有限性)
  - [3.2 对Fermat大定理的应用](#32-对fermat大定理的应用)
- [4 证明思路概述](#4-证明思路概述)
  - [4.1 Arakelov理论与高度](#41-arakelov理论与高度)
  - [4.2 Tate模与同源猜想](#42-tate模与同源猜想)
  - [4.3 Parshin技巧与Shafarevich猜想](#43-parshin技巧与shafarevich猜想)
- [5 后续发展与替代证明](#5-后续发展与替代证明)
  - [5.1 Vojta的Diophantine逼近证明](#51-vojta的diophantine逼近证明)
  - [5.2 Bombieri的简化与Uniformity猜想](#52-bombieri的简化与uniformity猜想)
- [6 例子 / Examples](#6-例子-examples)
- [7 参考文献 / References](#7-参考文献-references)

---

## 1 引言 / Introduction

1983年，德国数学家Gerd Faltings证明了关于代数曲线上有理点有限性的 **Mordell猜想**，这一成果彻底改变了算术几何的面貌，并为他赢得了1986年的Fields Medal以及2026年的Abel Prize。Mordell猜想断言：定义在数域上的、亏格 $g \ge 2$ 的光滑射影曲线，其有理点集是有限的。在此之前，数学家们对高次Diophantine方程的解集结构知之甚少；Faltings定理不仅解决了这一百年难题，还开创了将代数几何中的参模空间、阿贝尔簇理论与数论中的高度理论相结合的新范式。

本文将从Mordell猜想的历史脉络出发，陈述Faltings定理及其对Fermat大定理的深刻应用，系统梳理Faltings证明的核心思想（Arakelov理论、Tate猜想、Parshin技巧），并介绍Vojta和Bombieri的替代证明路线。内容主要对齐Cornell–Silverman的《Arithmetic Geometry》以及Faltings的原始论文。

---

## 2 历史背景：从Mordell到Shafarevich

### 2.1 Mordell的原始猜想

**猜想 2.1** (Mordell, 1922)  
设 $C$ 为定义在数域 $K$ 上的光滑射影曲线，亏格 $g \ge 2$。则 $C$ 的 $K$-有理点集 $C(K)$ 是 **有限的**。

Mordell本人仅证明了 $g=1$（椭圆曲线）时 $C(K)$ 是有限生成Abel群（即后来的Mordell–Weil定理）。对于 $g \ge 2$，他指出“直觉上”解应该有限，但无法给出严格证明。这一猜想成为算术几何中最引人注目的未解问题之一。

### 2.2 Siegel定理与Shafarevich猜想

**定理 2.1** (Siegel, 1929)  
设 $C$ 为定义在数域 $K$ 上的仿射曲线，其完备化后的亏格 $g \ge 1$，或在无穷远处至少有3个不同的点。则 $C$ 上的 $S$-整数点集是有限的（$S$ 为 $K$ 的位集）。

Siegel定理是Mordell猜想的“仿射版本”，但其证明依赖于Thue–Siegel–Roth定理的Diophantine逼近方法，且不能推广到射影情形。

**猜想 2.2** (Shafarevich, 1962)  
固定数域 $K$、位集 $S$ 以及亏格 $g \ge 2$。则在 $K$ 上仅有 **有限多条** 互不同构的光滑射影曲线具有好的约化 outside $S$。

Shafarevich猜想将曲线的算术性质（好的约化）与参模空间的有限性联系起来。Faltings证明Mordell猜想的关键一步，正是先证明了Shafarevich猜想对阿贝尔簇的类比（Faltings定理的另一个版本），再通过Parshin技巧将其归结为Mordell猜想。

---

## 3 Faltings定理的陈述

### 3.1 有理性点的有限性

**定理 3.1** (Faltings, 1983)  
设 $A$ 为定义在数域 $K$ 上的阿贝尔簇，$X \subset A$ 为真闭子簇。则 $X(K)$ 在 $X$ 中的Zariski闭包是 $X$ 的 **真子簇的有限并**。特别地，当 $X$ 是光滑射影曲线且亏格 $g \ge 2$ 时，$X(K)$ 是 **有限的**。

这就是Mordell猜想的最终形式。Faltings实际上证明了更强的结果：对任意阿贝尔簇的子簇，其有理点要么稠密于某个平移子阿贝尔簇，要么被包含在一个真子簇的有限并中。这被称为 **Mordell–Lang猜想** 在特征0时的特例。

### 3.2 对Fermat大定理的应用

**推论 3.1**  对 $n \ge 4$，Fermat曲线 $x^n + y^n = z^n$ 仅有有限多个本原整数解（在有理射影平面上仅有有限多个有理点）。

*说明*：当 $n \ge 4$ 时，Fermat曲线 $F_n: x^n + y^n = z^n$ 的亏格为 $g = \frac{(n-1)(n-2)}{2} \ge 3$。由Faltings定理，$F_n(\mathbb{Q})$ 是有限的。注意这并没有排除解的存在（实际上Fermat大定理断言没有非平凡解），但Faltings的结果大大削弱了可能的反例范围，并激发了Andrew Wiles最终证明Fermat大定理的动力。

---

## 4 证明思路概述

Faltings的证明极其深刻，融合了参模空间、阿贝尔簇的Tate模、高度理论和复几何中的Arakelov理论。以下是其核心步骤的概要。

### 4.1 Arakelov理论与高度

**定义 4.1** (Faltings高度)  
设 $A$ 为定义在数域 $K$ 上的阿贝尔簇。选取 $K$ 的整数环 $\mathcal{O}_K$ 上的一个Néron模型 $\mathcal{A} \to \operatorname{Spec}(\mathcal{O}_K)$。在无穷位（archimedean places）上，配备平坦的Hermite度量。Faltings定义了 $A$ 的 **Faltings高度** $h_F(A)$，它是一个非负实数，测量了 $A$ 在算术意义上的“复杂度”。

**定理 4.1** (Northcott性质)  
给定数域 $K$ 和正实数 $B$，仅有 **有限多个** 定义在 $K$ 上的阿贝尔簇（在同源意义下）满足 $h_F(A) \le B$。

这类似于经典Diophantine几何中高度函数的Northcott性质：有界高度意味着有限多个对象。

### 4.2 Tate模与同源猜想

**定义 4.2** (Tate模)  
对阿贝尔簇 $A$，其 **$\ell$-进Tate模** 定义为：

$$
T_\ell(A) = \varprojlim_n A[\ell^n] \cong \mathbb{Z}_\ell^{2g},
$$

其中 $A[\ell^n]$ 为 $\ell^n$-挠点。Galois群 $G_K = \operatorname{Gal}(\overline{K}/K)$ 自然作用在 $T_\ell(A)$ 上。

**猜想 4.1** (Tate猜想 for Abelian Varieties)  
同态群 $\operatorname{Hom}_K(A, B) \otimes \mathbb{Z}_\ell$ 自然嵌入到Galois不变同态 $ \operatorname{Hom}_{G_K}(T_\ell(A), T_\ell(B))$ 中。Tate猜想断言这个嵌入是 **同构**。

**定理 4.2** (Faltings)  
Tate猜想对定义在数域上的阿贝尔簇成立。

*证明思路*：Faltings通过研究阿贝尔簇的参模空间 $A_g$ 上的 $\ell$-进层，结合Arakelov理论中的高度不等式，证明了若两个阿贝尔簇的Tate模Galois同构，则它们必为同源的。核心步骤是利用了Zarhin对超椭圆曲线的结果，并将其推广到一般阿贝尔簇。

**同源猜想**：若 $A, B$ 的Tate模作为Galois表示同构，则 $A$ 与 $B$ 是同源的。这也是Faltings证明的一部分。

### 4.3 Parshin技巧与Shafarevich猜想

**定理 4.3** (Parshin技巧 / Parshin's Trick)  
设 $C$ 为亏格 $g \ge 2$ 的曲线，$P \in C(K)$ 为一个有理点。则存在一个覆盖 $C' \to C$（仅依赖于 $P$），使得 $C'$ 的好约化信息与 $(C, P)$ 的好约化信息相关联。更关键的是，不同的有理点 $P$ 诱导出不同构的覆盖 $C'$。

**推论 4.1**  若亏格 $g \ge 2$ 的曲线在 $K$ 上仅有有限多条具有好约化 outside $S$（即Shafarevich猜想），则对每个固定的 $C$，$C(K)$ 是有限的。

*证明概要*：
1. Faltings首先证明了 **Shafarevich猜想对阿贝尔簇** 成立：固定 $K, S, g, d$，仅有有限多条 $g$ 维主极化阿贝尔簇在 $K$ 上具有好的约化 outside $S$ 且度为 $d$ 的极化。
2. 利用Jacobian函子，将曲线映射到Jacobian簇 $J(C)$。由于 $J(C)$ 是主极化的，Shafarevich猜想对曲线也成立。
3. 应用Parshin技巧：$C(K)$ 中的每个点 $P$ 给出一个覆盖 $C_P \to C$。由Shafarevich猜想，仅有有限多条这样的 $C_P$ 存在，从而 $C(K)$ 是有限的。

---

## 5 后续发展与替代证明

### 5.1 Vojta的Diophantine逼近证明

1991年，Paul Vojta给出了Mordell猜想的一个全新证明，完全基于 **Diophantine逼近** 和 **Nevanlinna理论** 的类比。Vojta将曲线上的有理点视为某种“近似的”整点，并构造了一个类似于Roth定理中辅助函数的高度不等式。

**定理 5.1** (Vojta)  
设 $C$ 为定义在数域 $K$ 上的光滑射影曲线，亏格 $g \ge 2$。则存在常数 $c > 0$ 使得对几乎所有 $P \in C(K)$，有：

$$
h_K(P) \le c \cdot \log \operatorname{disc}(K(P)) + O(1),
$$

其中 $h_K(P)$ 为Weil高度。结合Northcott有限性，可直接推出 $C(K)$ 有限。

Vojta的方法后来被Faltings进一步推广，用于证明更一般的Mordell–Lang猜想和有理点集的Lang猜想。

### 5.2 Bombieri的简化与Uniformity猜想

Enrico Bombieri在Vojta证明的基础上给出了一个更简洁的Diophantine逼近证明，避免了部分复杂的辅助函数构造，转而使用了更为系统的高度机器和局部高度理论。

**猜想 5.1** (Uniformity Conjecture)  
设 $g \ge 2$。是否存在仅依赖于 $g$ 和 $[K:\mathbb{Q}]$ 的常数 $B(g, [K:\mathbb{Q}])$，使得对任意定义在 $K$ 上的亏格 $g$ 曲线 $C$，有 $|C(K)| \le B(g, [K:\mathbb{Q}])$？

这是一个远强于Faltings定理的猜想。目前，对一般的 $g \ge 2$ 仍属开放。但对某些特殊情形（如 $g=2$ 且Jacobian秩为0或1），已有具体的上界结果（如Coleman–Chabauty方法）。

---

## 6 例子 / Examples

**例 6.1** (Fermat曲线)  
Fermat曲线 $F_n: x^n + y^n = z^n$（$n \ge 4$）的亏格 $g = \frac{(n-1)(n-2)}{2} \ge 3$。由Faltings定理，$F_n(\mathbb{Q})$ 是有限集。事实上，Wiles定理断言当 $n \ge 3$ 时 $F_n(\mathbb{Q})$ 仅有平凡点（即有一个坐标为0的点），但Faltings的结果在Wiles证明之前就已将可能的非平凡解限制在有限集合内。

**例 6.2** (超椭圆曲线)  
考虑超椭圆曲线 $C: y^2 = f(x)$，其中 $f(x) \in \mathbb{Q}[x]$ 是无重根的奇次多项式，$\deg f \ge 5$。则 $C$ 的亏格 $g = \lfloor (\deg f - 1)/2 \rfloor \ge 2$。Faltings定理保证 $C(\mathbb{Q})$ 有限。例如 $y^2 = x^5 - x + 1$（$g=2$）仅有有限多个有理点。现代计算方法（如Magma中的Chabauty–Coleman）可以给出具体的上界甚至精确的有理点列表。

**例 6.3** (模曲线 $X_0(N)$)  
模曲线 $X_0(N)$ 是参数化带 $\Gamma_0(N)$-结构的椭圆曲线的光滑紧化曲线。对 $N$ 足够大（如 $N > 71$），$X_0(N)$ 的亏格 $g \ge 2$。由Faltings定理，$X_0(N)(\mathbb{Q})$ 是有限的。Mazur的著名定理进一步精确描述了哪些 $N$ 使得 $X_0(N)$ 的有理点对应于有理椭圆曲线的挠结构。这展示了Faltings定理在模形式与椭圆曲线算术中的深刻应用。

---

## 7 参考文献 / References

### 经典教材

1. **Faltings, G.** (1983). Endlichkeitssätze für abelsche Varietäten über Zahlkörpern. *Invent. Math.* 73, 349–366.
2. **Cornell, G., & Silverman, J. H. (Eds.)** (1986). *Arithmetic Geometry*. Springer. (Especially Chapters by Faltings, Parshin, and Mazur.)
3. **Bombieri, E., & Gubler, W.** (2006). *Heights in Diophantine Geometry*. Cambridge.
4. **Hindry, M., & Silverman, J. H.** (2000). *Diophantine Geometry*. Springer GTM 201.

### 进阶文献

5. **Vojta, P.** (1991). *Diophantine Approximations and Value Distribution Theory*. Springer LNM 1239.
6. **Parshin, A. N.** (1968). Algebraic curves over function fields I. *Math. USSR Izv.* 2, 1145–1170.
7. **Faltings, G.** (1984). *Calculus on arithmetic surfaces*. Annals of Math. 119, 387–424.
8. **Stix, J.** (2016). *Rational Points and Arithmetic of Fundamental Groups*. Springer LNM 2054.

### 中文参考

9. **冯克勤** (2005). *代数数论*. 科学出版社.
10. **潘承洞、潘承彪** (2012). *代数数论入门*. 北京大学出版社.

---

**文档状态**: 完成  
**字数**: 约5,700字  
**数学公式数**: 25+  
**例子数**: 3  
**最后更新**: 2026年4月3日
