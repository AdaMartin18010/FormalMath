#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
批量提升 FormalMath 概念思维导图文件的质量。
为 C 级概念卡片补充实际数学定义、公式、定理和例子。
"""

import os
import re
import glob

# 概念内容数据
def make_content(title, msc, definition, formulas, theorems, examples, related):
    fm = f"""---
msc_primary: 00
  - {msc}
title: {title}
processed_at: '2026-04-20'
---
msc_primary: "{msc}"
msc_secondary: ['00-00']
---

# {title}

## 中心概念
{definition.split(chr(10))[0].replace('**定义（', '').replace('）**。', '').replace('**定义**。**', '') if definition else title + '的核心数学概念'}

## 一、严格定义

{definition}

## 二、核心公式

"""
    for i, f in enumerate(formulas, 1):
        fm += f"{i}. {f}\n\n"
    fm += "## 三、重要定理\n\n"
    for i, t in enumerate(theorems, 1):
        fm += f"{i}. {t}\n\n"
    fm += "## 四、典型例子\n\n"
    for i, e in enumerate(examples, 1):
        fm += f"**例子 {i}**：{e}\n\n"
    fm += "## 五、相关概念\n\n"
    fm += " | ".join(related) + "\n\n"
    fm += f"---\n\n**概念链接**: {' '.join(related)}\n"
    return fm


CONCEPTS = {
    '导数': {
        'msc': '26A24',
        'def': '**定义（导数）**。设函数 $f: I \\to \\mathbb{R}$ 在区间 $I$ 的点 $a$ 的某邻域内有定义。若极限\n$$f\'(a) = \\lim_{h \\to 0} \\frac{f(a+h) - f(a)}{h}$$\n存在且有限，则称 $f$ 在 $a$ 处 **可导**，该极限值称为 $f$ 在 $a$ 处的 **导数**（derivative）。',
        'formulas': [
            '$(x^n)\' = nx^{n-1}, \\quad n \\in \\mathbb{R}$',
            '$(\\sin x)\' = \\cos x, \\quad (\\cos x)\' = -\\sin x$',
            '$(e^x)\' = e^x, \\quad (\\ln x)\' = \\frac{1}{x}$',
            '链式法则：$(f \\circ g)\'(x) = f\'(g(x)) \\cdot g\'(x)$',
            '乘积法则：$(fg)\' = f\'g + fg\'$',
        ],
        'theorems': [
            '**定理（Fermat）**。若 $f$ 在 $a$ 处取极值且可导，则 $f\'(a) = 0$。',
            '**定理（Rolle）**。$f \\in C[a,b] \\cap C^1(a,b)$，$f(a)=f(b)$，则 $\\exists c \\in (a,b)$，$f\'(c)=0$。',
            '**定理（Lagrange 中值）**。$f \\in C[a,b] \\cap C^1(a,b)$，则 $\\exists c \\in (a,b)$：\n$$f\'(c) = \\frac{f(b)-f(a)}{b-a}.$$',
        ],
        'examples': [
            '$f(x) = |x|$ 在 $x=0$ 处不可导：左右极限分别为 $-1$ 和 $1$。',
            '$f(x) = x^2 \\sin(1/x)$（$x \\neq 0$），$f(0)=0$ 在 $x=0$ 处可导（导数为 $0$），但导数在 $0$ 处不连续。',
        ],
        'related': ['[极限](../极限.md)', '[连续性](../连续.md)', '[微分](../微分.md)', '[Taylor公式](../Taylor公式.md)']
    },
    '开集': {
        'msc': '54A05',
        'def': '**定义（开集）**。设 $(X, \\mathcal{T})$ 为拓扑空间。子集 $U \\subset X$ 称为 **开集**（open set），若 $U \\in \\mathcal{T}$。\n\n在度量空间 $(X, d)$ 中，$U$ 开当且仅当对每个 $x \\in U$，存在 $\\varepsilon > 0$ 使得开球\n$$B(x, \\varepsilon) = \\{y \\in X : d(x,y) < \\varepsilon\\} \\subset U.$$',
        'formulas': [
            '$\\varnothing, X \\in \\mathcal{T}$（拓扑公理）',
            '任意开集的并仍是开集：$\\bigcup_{\\alpha} U_\\alpha \\in \\mathcal{T}$',
            '有限开集的交仍是开集：$\\bigcap_{i=1}^n U_i \\in \\mathcal{T}$',
        ],
        'theorems': [
            '**定理**。映射 $f: X \\to Y$ 连续当且仅当 $Y$ 中每个开集的原像是 $X$ 中的开集。',
            '**定理**。开集是开球的并：在度量空间中，$U$ 开 $\\Leftrightarrow$ $U = \\bigcup_{x \\in U} B(x, \\varepsilon_x)$。',
        ],
        'examples': [
            '$\\mathbb{R}$ 中：$(a,b)$ 开；$[a,b)$ 不开；$\\mathbb{R}$ 本身开。',
            '离散拓扑中：每个子集都是开集。',
            '平凡拓扑 $\\{\\varnothing, X\\}$ 中：只有 $\\varnothing$ 和 $X$ 是开集。',
        ],
        'related': ['[拓扑空间](../拓扑空间.md)', '[闭集](../闭集.md)', '[连续映射](../连续映射.md)', '[同胚](../同胚.md)']
    },
    '积分': {
        'msc': '26A42',
        'def': '**定义（Riemann 积分）**。设 $f: [a,b] \\to \\mathbb{R}$ 有界。对分割 $P: a=x_0<x_1<\\dots<x_n=b$，定义 Darboux 上和与下和：\n$$U(f,P) = \\sum_{i=1}^n M_i \\Delta x_i, \\quad L(f,P) = \\sum_{i=1}^n m_i \\Delta x_i,$$\n其中 $M_i = \\sup_{[x_{i-1},x_i]} f$，$m_i = \\inf_{[x_{i-1},x_i]} f$，$\\Delta x_i = x_i - x_{i-1}$。\n\n若 $\\inf_P U(f,P) = \\sup_P L(f,P) = I$，则称 $f$ **Riemann 可积**，$I$ 为 **定积分**，记 $\\int_a^b f(x)\\,dx$。',
        'formulas': [
            'Newton-Leibniz：$\\int_a^b f\'(x)\\,dx = f(b) - f(a)$',
            '分部积分：$\\int_a^b u\\,dv = [uv]_a^b - \\int_a^b v\\,du$',
            '变量替换：$\\int_a^b f(g(x))g\'(x)\\,dx = \\int_{g(a)}^{g(b)} f(u)\\,du$',
        ],
        'theorems': [
            '**定理**。连续函数必 Riemann 可积。',
            '**定理（控制收敛）**。若 $f_n \\to f$ a.e. 且 $|f_n| \\leq g$ 可积，则 $\\lim \\int f_n = \\int f$。',
            '**定理（Fubini）**。$f \\in L^1(X \\times Y)$，则\n$$\\int_{X \\times Y} f = \\int_X \\left(\\int_Y f(x,y)\\,dy\\right) dx = \\int_Y \\left(\\int_X f(x,y)\\,dx\\right) dy.$$',
        ],
        'examples': [
            '$\\int_0^1 x^2\\,dx = \\frac{1}{3}$。',
            'Dirichlet 函数 $\\mathbf{1}_{\\mathbb{Q} \\cap [0,1]}$ 不是 Riemann 可积的（上和为 1，下和为 0）。',
        ],
        'related': ['[导数](../导数.md)', '[微分](../微分.md)', '[测度](../测度.md)', '[极限](../极限.md)']
    },
    'Galois群': {
        'msc': '12F10',
        'def': '**定义（Galois 群）**。设 $K/F$ 为域扩张。$K$ 的 **F-自同构** 是域同构 $\\sigma: K \\to K$ 满足 $\\sigma|_F = \\mathrm{id}_F$。所有 $F$-自同构在复合运算下构成群，称为 **Galois 群**，记\n$$\\mathrm{Gal}(K/F) = \\{\\sigma \\in \\mathrm{Aut}(K) : \\sigma|_F = \\mathrm{id}_F\\}.$$',
        'formulas': [
            '$|\\mathrm{Gal}(K/F)| \\leq [K:F]$（当 $K/F$ 有限时）',
            '若 $K/F$ 是 Galois 扩张，则 $|\\mathrm{Gal}(K/F)| = [K:F]$',
            '固定子域：$K^G = \\{x \\in K : \\sigma(x)=x, \\forall \\sigma \\in G\\}$',
        ],
        'theorems': [
            '**定理（Galois 对应）**。设 $K/F$ 为有限 Galois 扩张。则存在包含关系反序的双射\n$$\\{\\text{中间域 } E: F \\subset E \\subset K\\} \\longleftrightarrow \\{\\text{子群 } H \\subset \\mathrm{Gal}(K/F)\\},$$\n$E \\mapsto \\mathrm{Gal}(K/E)$，$H \\mapsto K^H$。且 $[K:E] = |H|$，$[E:F] = [G:H]$。',
            '**定理**。中间域 $E/F$ 是 Galois 扩张当且仅当对应的子群 $H \\trianglelefteq G$ 正规。此时 $\\mathrm{Gal}(E/F) \\cong G/H$。',
        ],
        'examples': [
            '$\\mathrm{Gal}(\\mathbb{Q}(\\sqrt{2})/\\mathbb{Q}) = \\{\\mathrm{id}, \\sigma\\} \\cong \\mathbb{Z}/2\\mathbb{Z}$，其中 $\\sigma(\\sqrt{2}) = -\\sqrt{2}$。',
            '$\\mathrm{Gal}(\\mathbb{Q}(\\sqrt[3]{2})/\\mathbb{Q}) = \\{\\mathrm{id}\\}$（非 Galois，因复根不在域中）。',
            '$\\mathrm{Gal}(\\mathbb{F}_{p^n}/\\mathbb{F}_p) = \\langle \\mathrm{Frob}_p \\rangle \\cong \\mathbb{Z}/n\\mathbb{Z}$，Frobenius 自同构 $\\mathrm{Frob}_p(x) = x^p$。',
        ],
        'related': ['[群](../群.md)', '[域](../域.md)', '[环](../环.md)', '[模](../模.md)']
    },
    'Taylor公式': {
        'msc': '26A24',
        'def': '**定义（Taylor 展开）**。设 $f$ 在 $a$ 的某邻域内 $n+1$ 阶可导。则 $f$ 在 $a$ 处的 **n 阶 Taylor 多项式**为\n$$P_n(x) = \\sum_{k=0}^n \\frac{f^{(k)}(a)}{k!}(x-a)^k.$$\n\n**Taylor 公式**：存在 $c$ 介于 $a$ 与 $x$ 之间使得\n$$f(x) = P_n(x) + R_n(x), \\quad R_n(x) = \\frac{f^{(n+1)}(c)}{(n+1)!}(x-a)^{n+1}.$$\n$R_n(x)$ 称为 **Lagrange 余项**。',
        'formulas': [
            '$e^x = \\sum_{k=0}^\\infty \\frac{x^k}{k!}, \\quad x \\in \\mathbb{R}$',
            '$\\sin x = \\sum_{k=0}^\\infty (-1)^k \\frac{x^{2k+1}}{(2k+1)!}$',
            '$\\cos x = \\sum_{k=0}^\\infty (-1)^k \\frac{x^{2k}}{(2k)!}$',
            '$\\ln(1+x) = \\sum_{k=1}^\\infty (-1)^{k+1} \\frac{x^k}{k}, \\quad |x|<1$',
            '$(1+x)^\\alpha = \\sum_{k=0}^\\infty \\binom{\\alpha}{k} x^k, \\quad |x|<1$',
        ],
        'theorems': [
            '**定理**。若 $f$ 在 $a$ 处解析，则 Taylor 级数在某邻域内收敛于 $f$。',
            '**定理**。光滑函数 $f \\in C^\\infty$ 的 Taylor 级数不一定收敛于 $f$（经典反例：$f(x) = e^{-1/x^2}$，$x \\neq 0$，$f(0)=0$）。',
        ],
        'examples': [
            '$f(x) = e^x$ 在 $0$ 处的 3 阶 Taylor 展开：$1 + x + \\frac{x^2}{2} + \\frac{x^3}{6} + O(x^4)$。',
            '$f(x) = \\sqrt{1+x}$ 在 $0$ 处展开：$1 + \\frac{x}{2} - \\frac{x^2}{8} + \\frac{x^3}{16} + O(x^4)$。',
        ],
        'related': ['[导数](../导数.md)', '[幂级数](../幂级数.md)', '[解析函数](../解析函数.md)', '[极限](../极限.md)']
    },
    '幂级数': {
        'msc': '30B10',
        'def': '**定义（幂级数）**。形如\n$$\\sum_{n=0}^\\infty a_n (z - z_0)^n$$\n的级数称为以 $z_0$ 为中心的 **幂级数**（power series），其中 $a_n \\in \\mathbb{C}$（或 $\\mathbb{R}$），$z$ 为复（或实）变量。',
        'formulas': [
            '收敛半径（Cauchy-Hadamard）：$R = \\frac{1}{\\limsup_{n\\to\\infty} |a_n|^{1/n}}$',
            '比值公式：若 $\\lim |a_{n+1}/a_n| = L$，则 $R = 1/L$',
            '逐项求导：$f\'(z) = \\sum_{n=1}^\\infty n a_n (z-z_0)^{n-1}$，收敛半径相同',
            '逐项积分：$\\int f(z)\\,dz = C + \\sum_{n=0}^\\infty \\frac{a_n}{n+1}(z-z_0)^{n+1}$',
        ],
        'theorems': [
            '**定理（Abel）**。若幂级数在 $z = z_0 + R$ 处收敛，则它在 $[z_0, z_0+R]$ 上一致收敛。',
            '**定理**。幂级数在收敛圆 $|z-z_0|<R$ 内绝对收敛，在 $|z-z_0|>R$ 发散。',
            '**定理**。幂级数的和函数在收敛圆内解析。',
        ],
        'examples': [
            '$\\sum z^n$ 收敛半径 $R=1$，和为 $\\frac{1}{1-z}$（$|z|<1$）。',
            '$\\sum \\frac{z^n}{n!}$ 收敛半径 $R=+\\infty$，和为 $e^z$。',
            '$\\sum n! z^n$ 收敛半径 $R=0$（仅在 $z=0$ 收敛）。',
        ],
        'related': ['[Taylor公式](../Taylor公式.md)', '[解析函数](../解析函数.md)', '[Fourier级数](../Fourier级数.md)']
    },
    '微分': {
        'msc': '26A24',
        'def': '**定义（微分）**。设 $f: \\mathbb{R}^n \\to \\mathbb{R}^m$ 在 $a$ 的某邻域内有定义。若存在线性映射 $Df(a): \\mathbb{R}^n \\to \\mathbb{R}^m$ 使得\n$$\\lim_{h \\to 0} \\frac{\\|f(a+h) - f(a) - Df(a)h\\|}{\\|h\\|} = 0,$$\n则称 $f$ 在 $a$ 处 **可微**（differentiable），$Df(a)$ 称为 **全微分**（total derivative）。\n\n当 $m=1$ 时，$Df(a)$ 由梯度表示：$Df(a)h = \\nabla f(a) \\cdot h$。',
        'formulas': [
            '一维：$df = f\'(x)\\,dx$',
            '链式法则：$D(f \\circ g)(a) = Df(g(a)) \\circ Dg(a)$',
            'Jacobi 矩阵：$Df = \\left(\\frac{\\partial f_i}{\\partial x_j}\\right)_{m \\times n}$',
            '方向导数：$D_v f(a) = Df(a) \\cdot v = \\lim_{t \\to 0} \\frac{f(a+tv)-f(a)}{t}$',
        ],
        'theorems': [
            '**定理**。若所有偏导数 $\\partial f_i / \\partial x_j$ 在 $a$ 的邻域内存在且连续，则 $f$ 在 $a$ 处可微。',
            '**定理（反函数）**。$f \\in C^1$，$Df(a)$ 可逆，则 $f$ 在 $a$ 的某邻域内是局部微分同胚。',
            '**定理（隐函数）**。$F(x,y)=0$，$\\partial F/\\partial y$ 可逆，则局部可解出 $y = g(x)$。',
        ],
        'examples': [
            '$f(x,y) = x^2 + y^2$：$Df(x,y) = (2x, 2y)$，$\\nabla f = (2x, 2y)^T$。',
            '$f(x,y) = \\frac{xy}{x^2+y^2}$（$(x,y)\\neq(0,0)$），$f(0,0)=0$ 在 $(0,0)$ 处偏导存在但不可微。',
        ],
        'related': ['[导数](../导数.md)', '[积分](../积分.md)', '[偏导数](../偏导数.md)', '[Jacobian矩阵](../Jacobian矩阵.md)']
    },
    '拓扑空间': {
        'msc': '54A05',
        'def': '**定义（拓扑空间）**。集合 $X$ 上的 **拓扑**（topology）是子集族 $\\mathcal{T} \\subset 2^X$ 满足：\n1. $\\varnothing \\in \\mathcal{T}$，$X \\in \\mathcal{T}$；\n2. 任意并封闭：若 $\\{U_\\alpha\\} \\subset \\mathcal{T}$，则 $\\bigcup_\\alpha U_\\alpha \\in \\mathcal{T}$；\n3. 有限交封闭：若 $U_1, \\dots, U_n \\in \\mathcal{T}$，则 $\\bigcap_{i=1}^n U_i \\in \\mathcal{T}$。\n\n$(X, \\mathcal{T})$ 称为 **拓扑空间**，$\\mathcal{T}$ 中的元素称为 **开集**。',
        'formulas': [
            '度量拓扑：$\\mathcal{T}_d = \\{U : \\forall x \\in U, \\exists \\varepsilon > 0, B(x,\\varepsilon) \\subset U\\}$',
            '离散拓扑：$\\mathcal{T}_{\\text{disc}} = 2^X$',
            '平凡拓扑：$\\mathcal{T}_{\\text{triv}} = \\{\\varnothing, X\\}$',
            '余有限拓扑：$\\mathcal{T}_{\\text{cof}} = \\{U : X \\setminus U \\text{ 有限}\\} \\cup \\{\\varnothing\\}$',
        ],
        'theorems': [
            '**定理**。Hausdorff 空间（$T_2$）中极限唯一。',
            '**定理**。紧空间的闭子集紧；Hausdorff 空间中紧子集闭。',
            '**定理（Tychonoff）**。任意族紧空间的乘积在乘积拓扑下紧。',
        ],
        'examples': [
            '$\\mathbb{R}$ 带标准拓扑：开区间 $(a,b)$ 是开集。',
            'Sierpiński 空间：$X = \\{0,1\\}$，$\\mathcal{T} = \\{\\varnothing, \\{1\\}, X\\}$。',
            'Zariski 拓扑：代数簇上，闭集为代数子集。',
        ],
        'related': ['[开集](../开集.md)', '[闭集](../闭集.md)', '[连续映射](../连续映射.md)', '[同胚](../同胚.md)', '[紧致性](../紧致性.md)']
    },
    '一致收敛': {
        'msc': '40A30',
        'def': '**定义（一致收敛）**。设函数序列 $\\{f_n\\}$ 在集合 $E$ 上逐点收敛于 $f$。若对任意 $\\varepsilon > 0$，存在 $N$（不依赖于 $x$）使得当 $n \\geq N$ 时\n$$|f_n(x) - f(x)| < \\varepsilon, \\quad \\forall x \\in E,$$\n则称 $\\{f_n\\}$ 在 $E$ 上 **一致收敛**（uniformly convergent）于 $f$，记 $f_n \\rightrightarrows f$。',
        'formulas': [
            '$\\|f_n - f\\|_\\infty = \\sup_{x \\in E} |f_n(x) - f(x)| \\to 0$',
            'Cauchy 准则：$\\forall \\varepsilon>0, \\exists N, \\forall m,n \\geq N: \\|f_m - f_n\\|_\\infty < \\varepsilon$',
        ],
        'theorems': [
            '**定理**。若 $f_n \\rightrightarrows f$ 且每个 $f_n$ 连续，则 $f$ 连续。',
            '**定理**。若 $f_n \\rightrightarrows f$ 于 $[a,b]$，则 $\\lim \\int_a^b f_n = \\int_a^b f$。',
            '**定理（Dini）**。紧集上单调连续函数列逐点收敛于连续函数，则一致收敛。',
        ],
        'examples': [
            '$f_n(x) = x^n$ 于 $[0,1]$ 逐点收敛到 $f(x)=0$（$x<1$），$f(1)=1$，但不一致收敛。',
            '$f_n(x) = \\frac{x}{n}$ 于 $\\mathbb{R}$ 不一致收敛，但在有界区间上一致收敛于 0。',
        ],
        'related': ['[一致连续](../一致连续.md)', '[逐点收敛](../逐点收敛.md)', '[连续性](../连续.md)', '[积分](../积分.md)']
    },
    '一致连续': {
        'msc': '26A15',
        'def': '**定义（一致连续）**。设 $f: D \\to \\mathbb{R}$，$D \\subset \\mathbb{R}$。若对任意 $\\varepsilon > 0$，存在 $\\delta > 0$（仅依赖于 $\\varepsilon$，不依赖于点）使得对任意 $x,y \\in D$，\n$$|x-y| < \\delta \\implies |f(x)-f(y)| < \\varepsilon,$$\n则称 $f$ 在 $D$ 上 **一致连续**（uniformly continuous）。',
        'formulas': [
            'Lipschitz 条件：$|f(x)-f(y)| \\leq L|x-y|$ 蕴含一致连续',
            '$\\delta(\\varepsilon)$ 全局适用',
        ],
        'theorems': [
            '**定理**。闭区间 $[a,b]$ 上的连续函数必一致连续（Heine-Cantor 定理）。',
            '**定理**。一致连续函数将 Cauchy 列映为 Cauchy 列。',
            '**定理**。$\\mathbb{R}$ 上的连续函数一致连续当且仅当它在 $\\pm\\infty$ 处有有限极限。',
        ],
        'examples': [
            '$f(x) = x^2$ 于 $\\mathbb{R}$ 不一致连续，但在任何有界区间上一致连续。',
            '$f(x) = \\sin x$ 于 $\\mathbb{R}$ 一致连续（Lipschitz，常数为 1）。',
            '$f(x) = 1/x$ 于 $(0,1]$ 不一致连续（在 0 附近振荡加剧）。',
        ],
        'related': ['[连续](../连续.md)', '[一致收敛](../一致收敛.md)', '[Lipschitz](../Lipschitz.md)', '[紧致性](../紧致性.md)']
    },
    '同胚': {
        'msc': '54C05',
        'def': '**定义（同胚）**。设 $X,Y$ 为拓扑空间。映射 $f: X \\to Y$ 称为 **同胚**（homeomorphism），若 $f$ 是双射且 $f$ 与 $f^{-1}$ 都连续。此时称 $X$ 与 $Y$ **同胚**，记 $X \\cong Y$。',
        'formulas': [
            '$f$ 双射 + $f$ 连续 + $f^{-1}$ 连续',
            '等价：$f$ 是双射、连续、开映射（或闭映射）',
        ],
        'theorems': [
            '**定理**。同胚保持所有拓扑性质：紧致性、连通性、Hausdorff 性等。',
            '**定理（区域不变性）**。$U \\subset \\mathbb{R}^n$ 开，$f: U \\to \\mathbb{R}^n$ 连续单射，则 $f(U)$ 开。',
            '**定理**。$[0,1]$ 与 $[0,1)^2$ 不同胚（维数不变性）。',
        ],
        'examples': [
            '$f(x) = \\tan(\\pi x - \\pi/2)$ 给出 $(0,1) \\cong \\mathbb{R}$。',
            '圆周 $S^1$ 与线段 $[0,1]$ 不同胚（$S^1$ 连通去掉一点仍连通，$[0,1]$ 去掉端点不连通）。',
            '咖啡杯与甜甜圈（带柄环面）同胚。',
        ],
        'related': ['[拓扑空间](../拓扑空间.md)', '[连续映射](../连续映射.md)', '[开集](../开集.md)', '[紧致性](../紧致性.md)']
    },
    'Fermat小定理': {
        'msc': '11A07',
        'def': '**定理（Fermat 小定理）**。设 $p$ 为素数，$a$ 为整数且 $p \\nmid a$。则\n$$a^{p-1} \\equiv 1 \\pmod{p}.$$\n等价形式：对任意整数 $a$，$a^p \\equiv a \\pmod{p}$。',
        'formulas': [
            '$a^{p-1} \\equiv 1 \\pmod{p}$（$p \\nmid a$）',
            '$a^p \\equiv a \\pmod{p}$（对所有 $a$）',
            '逆元：$a^{-1} \\equiv a^{p-2} \\pmod{p}$',
        ],
        'theorems': [
            '**证明（群论）**。$\\mathbb{F}_p^\\times$ 是 $p-1$ 阶乘法群，$a$ 的阶整除 $p-1$（Lagrange 定理），故 $a^{p-1}=1$。',
            '**推广（Euler）**。$a^{\\varphi(n)} \\equiv 1 \\pmod{n}$（$\\gcd(a,n)=1$），$\\varphi$ 为 Euler  totient 函数。',
        ],
        'examples': [
            '$p=7$，$a=3$：$3^6 = 729 = 7 \\times 104 + 1 \\equiv 1 \\pmod{7}$。',
            '计算 $2^{100} \\bmod 13$：由 Fermat，$2^{12} \\equiv 1$，故 $2^{100} = 2^{8 \\times 12 + 4} \\equiv 2^4 = 16 \\equiv 3 \\pmod{13}$。',
        ],
        'related': ['[Euler定理](../Euler定理.md)', '[Wilson定理](../Wilson定理.md)', '[模运算](../模运算.md)', '[素数](../素数.md)']
    },
    'Euler定理': {
        'msc': '11A07',
        'def': '**定理（Euler）**。设 $n \\geq 1$，$a$ 为整数且 $\\gcd(a,n)=1$。则\n$$a^{\\varphi(n)} \\equiv 1 \\pmod{n},$$\n其中 $\\varphi(n) = |\\{1 \\leq k \\leq n : \\gcd(k,n)=1\\}|$ 为 **Euler totient 函数**。',
        'formulas': [
            '$\\varphi(p^k) = p^k - p^{k-1}$（$p$ 素数）',
            '$\\varphi$ 积性：$\\gcd(m,n)=1 \\implies \\varphi(mn) = \\varphi(m)\\varphi(n)$',
            '$\\sum_{d|n} \\varphi(d) = n$',
        ],
        'theorems': [
            '**证明**。$(\\mathbb{Z}/n\\mathbb{Z})^\\times$ 是 $\\varphi(n)$ 阶群，由 Lagrange 定理得 $a^{\\varphi(n)} \\equiv 1$。',
            '**Fermat 小定理是特例**：$n=p$ 素数时 $\\varphi(p)=p-1$。',
        ],
        'examples': [
            '$n=10$，$\\varphi(10)=4$。$3^4 = 81 \\equiv 1 \\pmod{10}$。',
            'RSA 加密：取 $n=pq$，公钥 $e$ 满足 $\\gcd(e, \\varphi(n))=1$，私钥 $d \\equiv e^{-1} \\pmod{\\varphi(n)}$。',
        ],
        'related': ['[Fermat小定理](../Fermat小定理.md)', '[Wilson定理](../Wilson定理.md)', '[模运算](../模运算.md)', '[群](../群.md)']
    },
    'Wilson定理': {
        'msc': '11A07',
        'def': '**定理（Wilson）**。设 $p$ 为正整数。则\n$$(p-1)! \\equiv -1 \\pmod{p}$$\n当且仅当 $p$ 是素数。',
        'formulas': [
            '$(p-1)! \\equiv -1 \\pmod{p}$ $\\Leftrightarrow$ $p$ 素数',
            '对素数 $p$，$\\mathbb{F}_p^\\times$ 中满足 $x^2 \\equiv 1$ 的元素恰为 $\\pm 1$',
        ],
        'theorems': [
            '**证明**。若 $p$ 素数，$\\mathbb{F}_p^\\times$ 中每个 $x \\neq \\pm 1$ 有唯一逆元 $x^{-1} \\neq x$。将元素与其逆元配对得 $(p-1)! \\equiv 1 \\cdot (-1) \\equiv -1$。',
            '**逆否证明**。若 $p=ab$ 合数（$1<a,b<p$），则 $a,b$ 均出现于 $(p-1)!$，故 $p|(p-1)!$，$(p-1)! \\equiv 0 \\not\\equiv -1$。',
        ],
        'examples': [
            '$p=5$：$4! = 24 = 5 \\times 5 - 1 \\equiv -1 \\pmod{5}$。',
            '$p=4$（非素数）：$3! = 6 \\equiv 2 \\not\\equiv -1 \\pmod{4}$。',
        ],
        'related': ['[Fermat小定理](../Fermat小定理.md)', '[Euler定理](../Euler定理.md)', '[素数](../素数.md)', '[阶乘](../阶乘.md)']
    },
    'Fourier级数': {
        'msc': '42A16',
        'def': '**定义（Fourier 级数）**。设 $f \\in L^1[-\\pi, \\pi]$ 且 $2\\pi$-周期。其 **Fourier 系数**为\n$$\\hat{f}(n) = \\frac{1}{2\\pi} \\int_{-\\pi}^{\\pi} f(x) e^{-inx} \\,dx, \\quad n \\in \\mathbb{Z}.$$\n形式级数\n$$\\sum_{n=-\\infty}^\\infty \\hat{f}(n) e^{inx}$$
称为 $f$ 的 **Fourier 级数**。',
        'formulas': [
            '$\\hat{f}(n) = \\frac{1}{2\\pi} \\int_{-\\pi}^{\\pi} f(x) e^{-inx} dx$',
            '实形式：$a_n = \\frac{1}{\\pi}\\int f(x)\\cos(nx)dx$，$b_n = \\frac{1}{\\pi}\\int f(x)\\sin(nx)dx$',
            'Parseval：$\\frac{1}{2\\pi}\\int |f|^2 = \\sum_{n} |\\hat{f}(n)|^2$',
        ],
        'theorems': [
            '**定理（Dirichlet）**。若 $f$ 分段 $C^1$，则 Fourier 级数逐点收敛于 $\\frac{f(x^+)+f(x^-)}{2}$。',
            '**定理（Carleson）**。$f \\in L^2$ 的 Fourier 级数几乎处处收敛于 $f$。',
            '**定理（Fejér）**。$f$ 连续 $\\Rightarrow$ Cesàro 和一致收敛于 $f$。',
        ],
        'examples': [
            '方波 $f(x) = \\text{sgn}(x)$ 于 $(-\\pi, \\pi)$：$f(x) \\sim \\frac{4}{\\pi}\\sum_{k=0}^\\infty \\frac{\\sin((2k+1)x)}{2k+1}$。',
            '锯齿波 $f(x) = x$ 于 $(-\\pi, \\pi)$：$x \\sim 2\\sum_{n=1}^\\infty \\frac{(-1)^{n+1}}{n}\\sin(nx)$。',
        ],
        'related': ['[积分](../积分.md)', '[正交多项式](../正交多项式.md)', '[Hilbert空间](../Hilbert空间.md)', '[调和分析](../调和分析.md)']
    },
    'Mordell定理': {
        'msc': '11G05',
        'def': '**定理（Mordell）**。设 $E$ 为定义在有理数域 $\\mathbb{Q}$ 上的椭圆曲线。则 $E$ 的有理点群 $E(\\mathbb{Q})$ 是有限生成 Abel 群：\n$$E(\\mathbb{Q}) \\cong \\mathbb{Z}^r \\oplus E(\\mathbb{Q})_{\\text{tors}},$$\n其中 $r \\geq 0$ 称为 **秩**（rank），$E(\\mathbb{Q})_{\\text{tors}}$ 为有限挠子群。',
        'formulas': [
            '$E: y^2 = x^3 + ax + b$，$\\Delta = -16(4a^3+27b^2) \\neq 0$',
            '$E(\\mathbb{Q}) \\cong \\mathbb{Z}^r \\oplus T$，$|T|<\\infty$',
        ],
        'theorems': [
            '**定理（Mordell-Weil）**。推广到任意数域 $K$：$E(K)$ 有限生成。',
            '**定理（Nagell-Lutz）**。挠点坐标为整数或半整数，且 $y=0$ 或 $y^2|\\Delta$。',
            '**定理（Mazur）**。$E(\\mathbb{Q})_{\\text{tors}}$ 只有 15 种可能结构。',
        ],
        'examples': [
            '$y^2 = x^3 - x$：$E(\\mathbb{Q})_{\\text{tors}} = \\{O, (0,0), (1,0), (-1,0)\\} \\cong \\mathbb{Z}/2\\mathbb{Z} \\times \\mathbb{Z}/2\\mathbb{Z}$，$r=0$。',
            '$y^2 = x^3 - 2$：$E(\\mathbb{Q}) \\cong \\mathbb{Z}$，生成元 $(3,5)$，秩 $r=1$。',
        ],
        'related': ['[椭圆曲线](../椭圆曲线.md)', '[Galois群](../Galois群.md)', '[数论](../数论.md)', '[代数几何](../代数几何.md)']
    },
    'Dirichlet定理': {
        'msc': '11N13',
        'def': '**定理（Dirichlet 算术级数）**。设 $a,q$ 为互素正整数（$\\gcd(a,q)=1$）。则算术级数\n$$\\{a, a+q, a+2q, a+3q, \\dots\\}$$
中含有无穷多个素数。',
        'formulas': [
            '$\\pi(x; q, a) \\sim \\frac{1}{\\varphi(q)} \\frac{x}{\\ln x}$（素数定理推广）',
        ],
        'theorems': [
            '**证明概要**。考虑 Dirichlet $L$-级数 $L(s,\\chi) = \\sum_{n=1}^\\infty \\frac{\\chi(n)}{n^s}$，其中 $\\chi$ 为模 $q$ 的 Dirichlet 特征。证明 $L(1,\\chi) \\neq 0$ 对非主特征，由此推出算术级数中有无穷多素数。',
        ],
        'examples': [
            '$q=4$，$a=1$：$1,5,9,13,17,21,\\dots$ 中有无穷多素数（如 $5,13,17,29,\\dots$）。',
            '$q=4$，$a=3$：$3,7,11,15,19,\\dots$ 中也有无穷多素数。',
        ],
        'related': ['[Dirichlet单位定理](../Dirichlet单位定理.md)', '[素数](../素数.md)', '[Euler定理](../Euler定理.md)', '[模运算](../模运算.md)']
    },
    'Dirichlet单位定理': {
        'msc': '11R27',
        'def': '**定理（Dirichlet 单位定理）**。设 $K$ 为 $n$ 次数域，$r_1$ 为其实嵌入个数，$r_2$ 为复嵌入对个数（$n = r_1 + 2r_2$）。则 $K$ 的整数环 $\\mathcal{O}_K$ 的单位群\\n$$\\mathcal{O}_K^\\times \\cong \\mu_K \\times \\mathbb{Z}^{r_1+r_2-1},$$\n其中 $\\mu_K$ 为 $K$ 中的单位根群（有限循环群），$r_1+r_2-1$ 为 **单位秩**。',
        'formulas': [
            '$\\mathcal{O}_K^\\times \\cong \\mu_K \\times \\mathbb{Z}^{r_1+r_2-1}$',
            '范数条件：$u \\in \\mathcal{O}_K^\\times \\Leftrightarrow |N_{K/\\mathbb{Q}}(u)| = 1$',
        ],
        'theorems': [
            '**定理**。$K=\\mathbb{Q}(\\sqrt{d})$，$d>0$ 无平方因子，则 $\\mathcal{O}_K^\\times \\cong \\{\\pm 1\\} \\times \\mathbb{Z}$（基本单位 $\\varepsilon$ 生成）。',
            '**Pell 方程**：$x^2 - dy^2 = 1$ 的解与 $\\mathbb{Q}(\\sqrt{d})$ 的单位一一对应。',
        ],
        'examples': [
            '$K=\\mathbb{Q}(\\sqrt{2})$：基本单位 $\\varepsilon = 1+\\sqrt{2}$，$N(\\varepsilon)=-1$。所有单位 $\\pm(1+\\sqrt{2})^n$。',
            '$K=\\mathbb{Q}(\\sqrt{-1})$：$\\mathcal{O}_K^\\times = \\{\\pm 1, \\pm i\\} \\cong \\mathbb{Z}/4\\mathbb{Z}$，秩为 0。',
        ],
        'related': ['[Dirichlet定理](../Dirichlet定理.md)', '[代数数论](../代数数论.md)', '[理想](../理想.md)', '[Mordell定理](../Mordell定理.md)']
    },
    'Euclid算法': {
        'msc': '11A05',
        'def': '**定义（Euclid 算法）**。给定整数 $a \\geq b > 0$，通过带余除法迭代计算 $\\gcd(a,b)$：\n$$a = q_1 b + r_1, \\quad 0 \\leq r_1 < b,$$\n$$b = q_2 r_1 + r_2, \\quad 0 \\leq r_2 < r_1,$$\n$$\\vdots$$\n直至 $r_{k+1}=0$，则 $\\gcd(a,b) = r_k$。',
        'formulas': [
            '$\\gcd(a,b) = \\gcd(b, a \\bmod b)$',
            'Bezout 恒等式：$\\exists x,y \\in \\mathbb{Z}: ax+by = \\gcd(a,b)$',
            '复杂度：$O(\\log \\min(a,b))$ 步',
        ],
        'theorems': [
            '**定理**。Euclid 算法正确计算 $\\gcd(a,b)$。',
            '**定理（Lamé）**。Euclid 算法步数不超过 $5 \\times$（较小数的十进制位数）。',
        ],
        'examples': [
            '$\\gcd(48, 18)$：$48 = 2\\cdot18 + 12$，$18 = 1\\cdot12 + 6$，$12 = 2\\cdot6 + 0$。故 $\\gcd=6$。',
            'Bezout：$6 = 18 - 1\\cdot12 = 18 - 1\\cdot(48-2\\cdot18) = 3\\cdot18 - 1\\cdot48$。',
        ],
        'related': ['[素数](../素数.md)', '[模运算](../模运算.md)', '[Fermat小定理](../Fermat小定理.md)', '[Euler定理](../Euler定理.md)']
    },
    '正合列': {
        'msc': '18G10',
        'def': '**定义（正合列）**。Abel 群（或模、层）的同态序列\n$$\\cdots \\longrightarrow A_{n-1} \\xrightarrow{f_{n-1}} A_n \\xrightarrow{f_n} A_{n+1} \\longrightarrow \\cdots$$\n称为在 $A_n$ 处 **正合**（exact），若 $\\mathrm{im}\\,f_{n-1} = \\ker f_n$。若序列在每处都正合，则称为 **正合列**。',
        'formulas': [
            '短正合列：$0 \\to A \\xrightarrow{f} B \\xrightarrow{g} C \\to 0$（$f$ 单，$g$ 满，$\\mathrm{im}f=\\kerg$）',
            '长正合列：$\\cdots \\to H^n(A^\\bullet) \\to H^n(B^\\bullet) \\to H^n(C^\\bullet) \\xrightarrow{\\delta} H^{n+1}(A^\\bullet) \\to \\cdots$',
        ],
        'theorems': [
            '**定理（五引理）**。交换图中若两端行正合且四个竖直映射为同构，则中间也为同构。',
            '**定理（蛇引理）**。短正合列的链复形诱导连接同态 $\\delta$ 使长正合列成立。',
            '**定理**。$0 \\to A \\to B \\to C \\to 0$ 分裂 $\\Leftrightarrow$ $B \\cong A \\oplus C$。',
        ],
        'examples': [
            '$0 \\to 2\\mathbb{Z} \\to \\mathbb{Z} \\to \\mathbb{Z}/2\\mathbb{Z} \\to 0$ 是短正合列。',
            '$0 \\to \\ker f \\to A \\xrightarrow{f} B \\to \\mathrm{coker} f \\to 0$ 正合。',
        ],
        'related': ['[模同态](../模同态.md)', '[同调代数](../同调代数.md)', '[投射模](../投射模.md)', '[内射模](../内射模.md)']
    },
    '模同态': {
        'msc': '13C99',
        'def': '**定义（模同态）**。设 $R$ 为环，$M,N$ 为 $R$-模。映射 $f: M \\to N$ 称为 **$R$-模同态**（module homomorphism），若对任意 $m,m\\' \\in M$，$r \\in R$：\n1. $f(m+m\\') = f(m) + f(m\\')$（加法同态）；\n2. $f(rm) = r \\cdot f(m)$（$R$-线性）。',
        'formulas': [
            '$\\mathrm{Hom}_R(M,N) = \\{f: M\\to N \\mid f \\text{ 为 } R\\text{-模同态}\\}$',
            '$\\ker f = \\{m \\in M : f(m)=0\\}$，$\\mathrm{im}f = \\{f(m) : m \\in M\\}$',
        ],
        'theorems': [
            '**定理（同态基本定理）**。$M/\\ker f \\cong \\mathrm{im} f$。',
            '**定理**。$\\mathrm{Hom}_R(R,N) \\cong N$（作为 $R$-模）。',
            '**定理**。$\\mathrm{Hom}$ 左正合：$0\\to A\\to B\\to C$ 正合 $\\Rightarrow$ $0\\to\\mathrm{Hom}(M,A)\\to\\mathrm{Hom}(M,B)\\to\\mathrm{Hom}(M,C)$ 正合。',
        ],
        'examples': [
            '$f: \\mathbb{Z} \\to \\mathbb{Z}$，$f(n)=kn$ 是 $\\mathbb{Z}$-模同态（$k \\in \\mathbb{Z}$）。',
            '矩阵表示：$R$ 域时，$f: R^n \\to R^m$ 由 $m\\times n$ 矩阵给出。',
        ],
        'related': ['[正合列](../正合列.md)', '[商模](../商模.md)', '[子模](../子模.md)', '[投射模](../投射模.md)', '[内射模](../内射模.md)']
    },
    '投射模': {
        'msc': '13C10',
        'def': '**定义（投射模）**。$R$-模 $P$ 称为 **投射的**（projective），若对任意满模同态 $g: B \\to C$ 和同态 $h: P \\to C$，存在提升 $\\tilde{h}: P \\to B$ 使 $g \\circ \\tilde{h} = h$。等价地，$\\mathrm{Hom}_R(P,-)$ 是正合函子。',
        'formulas': [
            '$P$ 投射 $\\Leftrightarrow$ $\\mathrm{Hom}(P,-)$ 正合',
            '$P$ 投射 $\\Leftrightarrow$ $P$ 是自由模的直和项',
            '$P$ 投射 $\\Leftrightarrow$ 任意满射 $F \\to P \\to 0$（$F$ 自由）分裂',
        ],
        'theorems': [
            '**定理**。自由模必投射。',
            '**定理**。PID 上投射模 = 自由模。',
            '**定理（Quillen-Suslin）**。$k[x_1,\\dots,x_n]$（$k$ 域）上投射模 = 自由模。',
        ],
        'examples': [
            '$\\mathbb{Z}/6\\mathbb{Z} \\cong \\mathbb{Z}/2\\mathbb{Z} \\oplus \\mathbb{Z}/3\\mathbb{Z}$ 中，$\\mathbb{Z}/2$ 和 $\\mathbb{Z}/3$ 作为 $\\mathbb{Z}/6$-模是投射的（非自由）。',
            '$\\mathbb{Z}$ 作为 $\\mathbb{Z}$-模自由，故投射。',
        ],
        'related': ['[内射模](../内射模.md)', '[模同态](../模同态.md)', '[自由模](../自由模.md)', '[正合列](../正合列.md)']
    },
    '内射模': {
        'msc': '13C11',
        'def': '**定义（内射模）**。$R$-模 $I$ 称为 **内射的**（injective），若对任意单模同态 $f: A \\to B$ 和同态 $h: A \\to I$，存在延拓 $\\tilde{h}: B \\to I$ 使 $\\tilde{h} \\circ f = h$。等价地，$\\mathrm{Hom}_R(-,I)$ 是正合函子。',
        'formulas': [
            '$I$ 内射 $\\Leftrightarrow$ $\\mathrm{Hom}(-,I)$ 正合',
            '$I$ 内射 $\\Leftrightarrow$ $\\mathrm{Ext}^1_R(M,I)=0$ 对所有 $M$',
            'Baer 判据：只需检验理想 $\\mathfrak{a} \\subset R$ 上的延拓性',
        ],
        'theorems': [
            '**定理（Baer）**。$I$ 内射当且仅当对任意理想 $\\mathfrak{a} \\subset R$，任意 $f: \\mathfrak{a} \\to I$ 可延拓到 $R \\to I$。',
            '**定理**。$\\mathbb{Q}/\\mathbb{Z}$ 是 $\\mathbb{Z}$-内射模。',
            '**定理**。任意模可嵌入某内射模（内射包存在）。',
        ],
        'examples': [
            '$\\mathbb{Q}$ 作为 $\\mathbb{Z}$-模是内射的。',
            '$\\mathbb{Z}$ 作为 $\\mathbb{Z}$-模不是内射的（如 $2\\mathbb{Z} \\to \\mathbb{Z}$，$n\\mapsto n/2$ 不能延拓）。',
        ],
        'related': ['[投射模](../投射模.md)', '[模同态](../模同态.md)', '[正合列](../正合列.md)', '[Ext](../Ext.md)']
    },
    '条件收敛': {
        'msc': '40A05',
        'def': '**定义（条件收敛）**。级数 $\\sum a_n$ 称为 **条件收敛**（conditionally convergent），若它收敛但非绝对收敛，即 $\\sum a_n$ 收敛而 $\\sum |a_n| = +\\infty$。',
        'formulas': [
            '绝对收敛：$\\sum |a_n| < +\\infty$',
            '条件收敛：$\\sum a_n$ 收敛，$\\sum |a_n| = +\\infty$',
        ],
        'theorems': [
            '**定理（Riemann 重排）**。条件收敛级数可通过重排收敛到任意预设值（包括 $\\pm\\infty$）。',
            '**定理**。绝对收敛级数的任意重排收敛到同一和。',
        ],
        'examples': [
            '交错调和级数 $\\sum \\frac{(-1)^{n+1}}{n} = \\ln 2$ 条件收敛（$\\sum 1/n$ 发散）。',
            '$\\sum \\frac{(-1)^n}{\\sqrt{n}}$ 条件收敛。',
        ],
        'related': ['[级数](../级数.md)', '[绝对收敛](../绝对收敛.md)', '[积分](../积分.md)', '[极限](../极限.md)']
    },
    '微分形式': {
        'msc': '58A10',
        'def': '**定义（微分形式）**。设 $M$ 为 $n$ 维光滑流形。$M$ 上的 **$k$-次微分形式**（differential $k$-form）是光滑的交错 $k$-阶协变张量场，即对每点 $p \\in M$，$\\omega_p \\in \\Lambda^k(T_p^*M)$，且随 $p$ 光滑变化。',
        'formulas': [
            '局部坐标：$\\omega = \\sum_{I} f_I \\, dx_{i_1} \\wedge \\dots \\wedge dx_{i_k}$',
            '外微分：$d\\omega = \\sum_I df_I \\wedge dx_I$',
            '$d^2 = 0$：$d(d\\omega) = 0$',
            '拉回：$F^*\\omega(X_1,\\dots,X_k) = \\omega(F_*X_1,\\dots,F_*X_k)$',
        ],
        'theorems': [
            '**定理（Poincaré 引理）**。$\\mathbb{R}^n$ 的星形区域上闭形式必恰当：$d\\omega=0 \\Rightarrow \\omega=d\\eta$。',
            '**定理（Stokes）**。$\\int_M d\\omega = \\int_{\\partial M} \\omega$。',
        ],
        'examples': [
            '$\\mathbb{R}^2$ 上：$\\omega = x\\,dy - y\\,dx$，$d\\omega = 2\\,dx\\wedge dy$。',
            '$S^1$ 上角度形式 $d\\theta$ 是闭形式但非恰当（$\\int_{S^1} d\\theta = 2\\pi \\neq 0$）。',
        ],
        'related': ['[积分](../积分.md)', '[拓扑空间](../拓扑空间.md)', '[de Rham上同调](../de-Rham上同调.md)', '[流形](../流形.md)']
    },
    '拓扑不变量': {
        'msc': '54A99',
        'def': '**定义（拓扑不变量）**。映射 $I: \\{\text{拓扑空间}\\} \\to \\text{某集合}$ 称为 **拓扑不变量**，若 $X \\cong Y$（同胚）$\\Rightarrow$ $I(X) = I(Y)$。常用不变量包括连通分支数、紧致性、基本群、同调群、Euler 示性数等。',
        'formulas': [
            'Euler 示性数：$\\chi(X) = \\sum_{i=0}^n (-1)^i \\dim H_i(X)$',
            'Betti 数：$b_i = \\dim H_i(X;\\mathbb{Q})$',
        ],
        'theorems': [
            '**定理**。Euler 示性数是拓扑不变量。',
            '**定理**。$\\pi_1$（基本群）是拓扑不变量。',
            '**定理（Brouwer 不动点）**。$D^n \\to D^n$ 连续必有不动点（可用 $H_{n-1}(S^{n-1})$ 证明）。',
        ],
        'examples': [
            '$\\chi(S^2) = 2$，$\\chi(T^2) = 0$。二者不同胚。',
            '$\\pi_1(S^1) = \\mathbb{Z}$，$\\pi_1(S^2) = 0$。二者不同胚。',
        ],
        'related': ['[拓扑空间](../拓扑空间.md)', '[同胚](../同胚.md)', '[同调](../同调.md)', '[基本群](../基本群.md)']
    },
    '提升性质': {
        'msc': '55Q05',
        'def': '**定义（提升性质）**。设 $p: E \\to B$ 为覆叠映射（或更一般的纤维化）。给定映射 $f: X \\to B$ 和 $\\tilde{f}_0: X_0 \\to E$（$X_0 \\subset X$）满足 $p \\circ \\tilde{f}_0 = f|_{X_0}$，若存在 $\\tilde{f}: X \\to E$ 使 $p \\circ \\tilde{f} = f$ 且 $\\tilde{f}|_{X_0} = \\tilde{f}_0$，则称 $\\tilde{f}$ 为 $f$ 的 **提升**（lift）。',
        'formulas': [
            '覆叠映射的 Homotopy 提升性质：$\\tilde{H}(\\cdot, 0) = \\tilde{f}_0$，$p \\circ \\tilde{H} = H$',
        ],
        'theorems': [
            '**定理**。若 $X$ 连通，$p$ 覆叠，则两提升在一点相同则处处相同。',
            '**定理**。$\\gamma: [0,1] \\to B$ 道路，$\\tilde{\\gamma}(0)$ 给定，则存在唯一提升 $\\tilde{\\gamma}$。',
            '**定理**。$p_*: \\pi_1(E, \\tilde{x}_0) \\to \\pi_1(B, x_0)$ 是单射，像为 $\\gamma$ 可提升为环道的那些同伦类。',
        ],
        'examples': [
            '$p: \\mathbb{R} \\to S^1$，$p(t) = e^{2\\pi i t}$。道路 $\\gamma(t) = e^{2\\pi i t}$ 提升为 $\\tilde{\\gamma}(t) = t$。',
            '悬覆叠 $S^1 \\to S^1$，$z \\mapsto z^n$：提升存在当且仅当 $\\gamma$ 绕数被 $n$ 整除。',
        ],
        'related': ['[拓扑空间](../拓扑空间.md)', '[同胚](../同胚.md)', '[基本群](../基本群.md)', '[覆叠空间](../覆叠空间.md)']
    },
    '子模': {
        'msc': '13C99',
        'def': '**定义（子模）**。设 $M$ 为 $R$-模。子集 $N \\subset M$ 称为 **子模**（submodule），若 $N$ 本身在 $M$ 的加法和 $R$ 的数乘下构成 $R$-模。等价地：\n1. $N \\neq \\varnothing$；\n2. $n_1, n_2 \\in N \\Rightarrow n_1 + n_2 \\in N$；\n3. $n \\in N, r \\in R \\Rightarrow r n \\in N$。',
        'formulas': [
            '商模：$M/N = \\{m+N : m \\in M\\}$，$r\\cdot(m+N) = rm+N$',
            '同态基本定理：$M/\\ker f \\cong \\mathrm{im} f$',
        ],
        'theorems': [
            '**定理（对应定理）**。$M$ 的包含 $N$ 的子模与 $M/N$ 的子模一一对应。',
            '**定理**。$N_1, N_2 \\subset M$ 子模，则 $N_1+N_2$ 和 $N_1 \\cap N_2$ 也是子模。',
        ],
        'examples': [
            '$2\\mathbb{Z}$ 是 $\\mathbb{Z}$ 的 $\\mathbb{Z}$-子模。',
            '核 $\\ker f$ 和像 $\\mathrm{im} f$ 分别是子模。',
        ],
        'related': ['[商模](../商模.md)', '[模同态](../模同态.md)', '[正合列](../正合列.md)', '[投射模](../投射模.md)']
    },
    '商模': {
        'msc': '13C99',
        'def': '**定义（商模）**。设 $N \\subset M$ 为 $R$-子模。在商群 $M/N$ 上定义 $R$-模结构：\n$$r \\cdot (m+N) = (rm) + N, \\quad r \\in R, \\; m \\in M.$$\n则 $M/N$ 称为 $M$ 关于 $N$ 的 **商模**（quotient module）。',
        'formulas': [
            '典范投影：$\\pi: M \\to M/N$，$\\pi(m) = m+N$',
            '$\\ker \\pi = N$，$\\mathrm{im} \\pi = M/N$',
            '第三同构定理：$(M/K)/(N/K) \\cong M/N$（$K \\subset N \\subset M$）',
        ],
        'theorems': [
            '**定理（同态基本定理）**。$M/\\ker f \\cong \\mathrm{im} f$。',
            '**定理（第二同构）**。$(N_1+N_2)/N_2 \\cong N_1/(N_1 \\cap N_2)$。',
        ],
        'examples': [
            '$\\mathbb{Z}/n\\mathbb{Z}$ 是 $\\mathbb{Z}$ 关于 $n\\mathbb{Z}$ 的商模。',
            '$\\mathbb{R}[x]/(x^2+1) \\cong \\mathbb{C}$ 作为 $\\mathbb{R}$-代数。',
        ],
        'related': ['[子模](../子模.md)', '[模同态](../模同态.md)', '[正合列](../正合列.md)', '[理想](../理想.md)']
    },
    '子域': {
        'msc': '12F99',
        'def': '**定义（子域）**。设 $K$ 为域。子集 $F \\subset K$ 称为 **子域**（subfield），若 $F$ 在 $K$ 的加法和乘法下自身构成域。等价地：\n1. $F$ 是 $K$ 的加法子群；\n2. $F^\\times = F \\setminus \\{0\\}$ 是 $K^\\times$ 的乘法子群；\n3. $F$ 对加法逆和乘法逆封闭。',
        'formulas': [
            '$\\mathbb{Q} \\subset \\mathbb{R} \\subset \\mathbb{C}$ 为子域链',
            '$[K:F]$ 为 $K$ 作为 $F$-向量空间的维数',
        ],
        'theorems': [
            '**定理**。域 $K$ 的所有子域的交仍是子域（含于最小子域——素域）。',
            '**定理**。有限域 $\\mathbb{F}_{p^n}$ 的子域恰为 $\\mathbb{F}_{p^m}$（$m|n$）。',
        ],
        'examples': [
            '$\\mathbb{Q}(\\sqrt{2}) = \\{a+b\\sqrt{2} : a,b \\in \\mathbb{Q}\\}$ 是 $\\mathbb{R}$ 的子域。',
            '$\\mathbb{F}_2 = \\{0,1\\}$ 是 $\\mathbb{F}_4$ 的唯一真子域。',
        ],
        'related': ['[域](../域.md)', '[Galois群](../Galois群.md)', '[环](../环.md)', '[代数扩张](../代数扩张.md)']
    },
    '可数紧致': {
        'msc': '54D20',
        'def': '**定义（可数紧致）**。拓扑空间 $X$ 称为 **可数紧致**（countably compact），若每个可数开覆盖都有有限子覆盖。等价地：$X$ 中每个无限子集都有聚点。',
        'formulas': [
            '紧 $\\Rightarrow$ 可数紧 $\\Rightarrow$ 极限点紧',
            '第一可数 + 极限点紧 $\\Rightarrow$ 可数紧',
            '度量空间中：紧 $\\Leftrightarrow$ 可数紧 $\\Leftrightarrow$ 极限点紧 $\\Leftrightarrow$ 列紧',
        ],
        'theorems': [
            '**定理**。可数紧致空间的连续像是可数紧致的。',
            '**定理**。$T_1$ + 可数紧 $\\Rightarrow$ 每局部有限开覆盖有限。',
        ],
        'examples': [
            '不可数良序集 $[0, \\omega_1]$ 是可数紧的（非紧）。',
            '长直线（long line）是可数紧的（非紧）。',
        ],
        'related': ['[紧致性](../紧致性.md)', '[拓扑空间](../拓扑空间.md)', '[连续映射](../连续映射.md)', '[序列紧致](../序列紧致.md)']
    },
}


def enrich_file(path, data):
    content = make_content(
        title=data['msc'],
        msc=data['msc'],
        definition=data['def'],
        formulas=data['formulas'],
        theorems=data['theorems'],
        examples=data['examples'],
        related=data['related']
    )
    # Keep the frontmatter line as-is from original if it has specific structure
    # But our generated content already includes frontmatter
    with open(path, 'w', encoding='utf-8') as f:
        f.write(content)
    return True


def main():
    base = 'docs/visualizations/思维导图/概念'
    enriched = []
    for name, data in CONCEPTS.items():
        path = os.path.join(base, name + '.md')
        if os.path.exists(path):
            enrich_file(path, data)
            enriched.append(name)
        else:
            print(f"MISSING: {path}")
    print(f"Enriched {len(enriched)} concept mindmap files.")
    for e in enriched:
        print(f"  - {e}")


if __name__ == '__main__':
    main()
