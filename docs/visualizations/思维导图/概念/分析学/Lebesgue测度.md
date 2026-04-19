---
msc_primary: 00

  - 00A99
title: Lebesgue测度 (Lebesgue Measure)
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# Lebesgue测度 (Lebesgue Measure)

## 中心概念精确定义

**Lebesgue测度**是现代分析的基础，将"长度/面积/体积"的概念推广到远比Riemann可积更广泛的集合类。

> **Lebesgue外测度**：对任意 $E \subset \mathbb{R}^n$，定义：
> $$m^*(E) = \inf\left\{\sum_{k=1}^{\infty} |I_k| : E \subset \bigcup_{k=1}^{\infty} I_k\right\}$$
> 其中 $I_k$ 是开区间（或开矩体），$|I_k|$ 表示体积。

> **Lebesgue可测集**：$E$ 可测当且仅当对任意 $A \subset \mathbb{R}^n$：
> $$m^*(A) = m^*(A \cap E) + m^*(A \cap E^c)$$
> （Carathéodory判别准则）

---

## Mermaid 思维导图

```mermaid
mindmap
  root((Lebesgue测度<br/>Lebesgue Measure))
    外测度
      定义
        开覆盖下确界
        次可加性
      性质
        单调性
        平移不变
        缩放:m*(λE)=|λ|ⁿm*(E)

      限制
        非可数可加
        不可测集存在
    可测集
      Carathéodory
        分割可加
        m*(A)=m*(A∩E)+m*(A∩Eᶜ)
      σ-代数
        ∅可测
        补封闭
        可数并可测
      例子
        区间
        开集/闭集
        Borel集
        零测集
    测度性质
      可数可加
        Eᵢ不交⇒m(∪Eᵢ)=Σm(Eᵢ)
      连续性
        下方连续
        上方连续(有限测度)
      完备性
        零测子集可测
    可测函数
      定义
        原像可测
        几乎处处
      运算封闭
        四则运算
        极限
      逼近
        简单函数
        阶梯函数
    积分理论
      定义
        简单函数
        非负函数
        一般函数
      收敛定理
        单调收敛
        Fatou引理
        控制收敛

```

---

## 核心要素详解

### 1. 外测度的构造与性质

**构造思路**：用可数个开区间覆盖集合，取下确界。

**基本性质**：
1. **非负性**：$m^*(E) \geq 0$，$m^*(\emptyset) = 0$
2. **单调性**：$E_1 \subset E_2$ $\Rightarrow$ $m^*(E_1) \leq m^*(E_2)$
3. **次可数可加性**：$m^*\left(\bigcup_{k=1}^{\infty} E_k\right) \leq \sum_{k=1}^{\infty} m^*(E_k)$
4. **平移不变性**：$m^*(E + a) = m^*(E)$
5. **缩放性质**：$m^*(\lambda E) = |\lambda|^n m^*(E)$

**重要例子**：
- 可数集的外测度为0
- Cantor集的外测度为0（不可数但零测）
- 存在不可测集（需选择公理）

### 2. Carathéodory 可测性准则

**核心问题**：外测度一般不满足可数可加性，需要限制到适当的集合类。

**Carathéodory判别**：$E$ 可测 $\Leftrightarrow$ 对所有试验集 $A$：
$$m^*(A) = m^*(A \cap E) + m^*(A \cap E^c)$$

**直观理解**：可测集 $E$ 能"良好地分割"任意集合的测度。

### 3. Lebesgue σ-代数

**定理**：Lebesgue可测集构成 $\sigma$-代数 $\mathcal{L}$：
- $\emptyset, \mathbb{R}^n \in \mathcal{L}$
- $E \in \mathcal{L}$ $\Rightarrow$ $E^c \in \mathcal{L}$
- $E_k \in \mathcal{L}$ $\Rightarrow$ $\bigcup_{k=1}^{\infty} E_k \in \mathcal{L}$

**包含关系**：
$$\{\text{开集}\} \subset \{\text{Borel集}\} \subset \{\text{Lebesgue可测集}\}$$

**Lebesgue测度在 $\mathcal{L}$ 上的性质**：
- **可数可加性**：不交可测集的可数并的测度等于测度之和
- **完备性**：零测集的子集可测

### 4. 可测函数

**定义**：$f: E \to \mathbb{R}$ 可测，如果对所有开集 $U \subset \mathbb{R}$，$f^{-1}(U)$ 是Lebesgue可测集。

**等价刻画**：以下任一条件：
- 对所有 $a \in \mathbb{R}$，$\{f > a\}$ 可测
- 对所有 $a \in \mathbb{R}$，$\{f \geq a\}$ 可测
- 对所有 $a \in \mathbb{R}$，$\{f < a\}$ 可测

**运算封闭性**：
- 可测函数的线性组合、乘积可测
- 可测函数序列的 $\sup, \inf, \limsup, \liminf, \lim$ 可测

**简单函数逼近**：
任何非负可测函数 $f$ 可表示为简单函数序列的单调极限：
$$f = \lim_{n \to \infty} \phi_n, \quad \phi_n \nearrow f$$

### 5. Lebesgue积分构造

**第一步：简单函数**：$\phi = \sum_{k=1}^n a_k \chi_{E_k}$，定义：
$$\int \phi = \sum_{k=1}^n a_k m(E_k)$$

**第二步：非负可测函数**：
$$\int f = \sup\left\{\int \phi : 0 \leq \phi \leq f, \phi \text{ 简单}\right\}$$

**第三步：一般可测函数**：$f = f^+ - f^-$，若 $\int f^+$ 和 $\int f^-$ 至少一个有限：
$$\int f = \int f^+ - \int f^-$$

**可积性**：$f \in L^1$ $\Leftrightarrow$ $\int |f| < \infty$

---

## 关键性质与定理

### 定理1：单调收敛定理 (MCT)

**定理**：设 $0 \leq f_n \nearrow f$ a.e.，则：
$$\lim_{n \to \infty} \int f_n = \int \lim_{n \to \infty} f_n = \int f$$

### 定理2：Fatou 引理

**定理**：设 $f_n \geq 0$，则：
$$\int \liminf_{n \to \infty} f_n \leq \liminf_{n \to \infty} \int f_n$$

**注意**：不等式一般严格，除非满足额外条件。

### 定理3：控制收敛定理 (DCT)

**定理**：设 $f_n \to f$ a.e.，且存在可积函数 $g$ 使得 $|f_n| \leq g$ a.e.，则：

$$\lim_{n \to \infty} \int f_n = \int f$$

这是分析中最常用的收敛定理。

### 定理4：Riemann vs Lebesgue

**定理**：有界函数 $f$ 在 $[a,b]$ 上Riemann可积 $\Leftrightarrow$ $f$ 的不连续点集是零测集。

**推论**：Riemann可积 $\Rightarrow$ Lebesgue可积，且积分值相同。

---

## 典型例子

### 例子1：Dirichlet函数

$$f(x) = \begin{cases} 1 & x \in \mathbb{Q} \\ 0 & x \notin \mathbb{Q} \end{cases}$$

- **Riemann**：不可积（处处不连续）
- **Lebesgue**：可积，$\int f = 0$（$\mathbb{Q}$ 零测）

### 例子2：Cantor集的构造与测度

**构造**：
- 从 $[0,1]$ 开始
- 每次移除中间三分之一开区间
- 重复可数无穷次

**性质**：
- 剩余集 $C$ 不可数
- $m(C) = 0$
- $C$ 无处稠密、完备、完全不连通

### 例子3：不可测集的构造

利用选择公理，在 $[0,1]$ 上定义等价关系 $x \sim y$ $\Leftrightarrow$ $x - y \in \mathbb{Q}$。

从每个等价类中选一个代表元，构成集合 $V$（Vitali集）。

**结论**：$V$ 不是Lebesgue可测的。

---

## 关联概念网络

### 相似概念

| 概念 | 关系 | 说明 |
|------|------|------|
| **Haar测度** | 推广 | 局部紧群上的不变测度 |
| **Hausdorff测度** | 推广 | 分数维集合的测度 |
| **抽象测度** | 公理化 | 一般测度空间理论 |

### 对偶概念

| 概念 | 对偶关系 | 说明 |
|------|----------|------|
| **可测集 ↔ 可测函数** | 结构与映射 | 函数的原像定义可测性 |
| **测度 ↔ 积分** | 对偶对 | Riesz表示定理 |

### 推广概念

```

Lebesgue测度 → 抽象测度空间
      ↓
   Radon测度
      ↓
   几何测度论
      ↓
   遍历理论

```

---

## 课程对齐

### MIT 18.100
- **Supplementary**: Lebesgue measure introduction
- **Related**: 18.125 (Real Analysis)

### Princeton MAT 218
- **Topic**: Measure theory
- **Text**: Stein & Shakarchi, *Real Analysis*, Ch. 1-2
- **Key topics**: Construction of Lebesgue measure, measurable functions, convergence theorems

---

## 总结

Lebesgue测度是现代分析的基石，通过Carathéodory准则从外测度构造出具有可数可加性的完备测度。相比于Riemann积分，Lebesgue积分具有更强大的收敛定理（单调收敛、控制收敛），使极限与积分可交换的条件大大放宽。可测函数的概念统一了连续函数与许多不连续函数（如Dirichlet函数），为泛函分析、概率论和偏微分方程奠定了严格基础。

---

*创建日期：2026年4月*  
*相关概念：[可测函数](./../../../../../数学家理念体系/勒贝格数学理念/02-数学内容深度分析/04-函数论贡献/01-可测函数理论.md)、[Lebesgue积分](./Lebesgue测度.md)、[Lp空间](Lp空间.md)*
