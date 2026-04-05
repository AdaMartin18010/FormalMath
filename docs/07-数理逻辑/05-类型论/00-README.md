---
title: "类型论 (Type Theory)"
msc_primary: "03B15"
msc_secondary: ['03B30', '03B40', '03B70', '68N18']
processed_at: '2026-04-05'
---

# 类型论 (Type Theory)

**最后更新**: 2026年4月5日  
**MSC分类**: 03B-XX (逻辑基础), 68N-XX (程序语言)

---

## 1. 引言

类型论是数理逻辑和计算机科学的交汇点，为编程语言和形式化证明提供了严格的数学基础。从Church的简单类型λ演算到Martin-Löf的直觉主义类型论，从CoC（构造演算）到同伦类型论（HoTT），类型论不仅统一了逻辑与计算，还推动了现代证明助手（如Lean、Coq、Agda）的发展。

---

## 2. 简单类型λ演算

### 2.1 类型与项

**定义 2.1** (简单类型): 类型由以下文法生成：
$$\sigma, \tau ::= \iota \mid \sigma \to \tau$$
其中 $\iota$ 是基类型，$\sigma \to \tau$ 是函数类型。

**定义 2.2** ($\lambda$-项): 带类型的$\lambda$-项：
$$M, N ::= x \mid \lambda x:\sigma.M \mid M N \mid c$$
其中 $c$ 是常数。

**定义 2.3** (上下文): 上下文 $\Gamma$ 是形如 $x_1:\sigma_1, \ldots, x_n:\sigma_n$ 的假设列表。

---

### 2.2 类型推导

**定义 2.4** (类型判断): $\Gamma \vdash M : \sigma$ 表示在上下文 $\Gamma$ 中项 $M$ 具有类型 $\sigma$。

**类型规则**:

$$
\frac{x:\sigma \in \Gamma}{\Gamma \vdash x : \sigma} \text{ (Var)}
$$

$$
\frac{\Gamma, x:\sigma \vdash M : \tau}{\Gamma \vdash \lambda x:\sigma.M : \sigma \to \tau} \text{ (Abs)}
$$

$$
\frac{\Gamma \vdash M : \sigma \to \tau \quad \Gamma \vdash N : \sigma}{\Gamma \vdash M N : \tau} \text{ (App)}
$$

**定理 2.1** (类型唯一性): 若 $\Gamma \vdash M : \sigma$ 且 $\Gamma \vdash M : \tau$，则 $\sigma = \tau$。

---

### 2.3 归约与正规化

**定义 2.5** ($\beta$-归约): $(\lambda x:\sigma.M) N \to_\beta M[N/x]$

**定义 2.6** ($\eta$-归约): $\lambda x:\sigma.(M x) \to_\eta M$（若 $x \notin FV(M)$）

**定理 2.2** (Church-Rosser): $\to_\beta$ 是合流的。

**定理 2.3** (强正规化): 简单类型$\lambda$-演算中，所有项都是强正规化的（任何归约序列都终止）。

---

## 3. Curry-Howard同构

### 3.1 命题即类型

**定义 3.1** (Curry-Howard对应): 
| 逻辑 | 类型论 |
|------|--------|
| 命题 $A$ | 类型 $A$ |
| 证明 $p$ | 项 $p : A$ |
| $A \to B$ | 函数类型 $A \to B$ |
| $A \land B$ | 积类型 $A \times B$ |
| $A \lor B$ | 和类型 $A + B$ |
| $\forall x A$ | 依赖积 $\Pi x:A.B$ |
| $\exists x A$ | 依赖和 $\Sigma x:A.B$ |

**定理 3.1** (Curry-Howard): 
- 命题 $A$ 在直觉主义命题逻辑中可证 $\Leftrightarrow$ 类型 $A$ 被 inhabite
- 证明 $p$ 归约为 $q$ $\Leftrightarrow$ 项 $p$ 归约为 $q$

---

### 3.2 证明即程序

**示例 3.1**: 证明 $A \to A$ 对应恒等函数：
$$\vdash \lambda x:A.x : A \to A$$

**示例 3.2**: 证明 $(A \to (B \to C)) \to ((A \to B) \to (A \to C))$ 对应组合子：
$$\vdash \lambda f.\lambda g.\lambda x.f x (g x) : \ldots$$

---

## 4. 依赖类型论

### 4.1 Martin-Löf类型论

**定义 4.1** (依赖类型): 
- **依赖积** $\Pi x:A.B(x)$: 对 $x:A$ 返回 $B(x)$ 的函数类型
- **依赖和** $\Sigma x:A.B(x)$: 对 $(x, y)$ 其中 $x:A$, $y:B(x)$ 的积类型

**定义 4.2** (宇宙): 宇宙 $\mathcal{U}$ 是类型的类型（为避免悖论，常分层为 $\mathcal{U}_0 : \mathcal{U}_1 : \mathcal{U}_2 : \ldots$）。

---

### 4.2 归纳类型

**定义 4.3** (归纳定义): 自然数类型 $\mathbb{N}$ 归纳定义为：
- $0 : \mathbb{N}$
- $\text{succ} : \mathbb{N} \to \mathbb{N}$
- 归纳原理: $\text{ind}_\mathbb{N} : P(0) \to (\Pi n:\mathbb{N}.P(n) \to P(\text{succ}(n))) \to \Pi n:\mathbb{N}.P(n)$

**定义 4.4** (等式类型): 同一性类型 $\text{Id}_A(x, y)$（或 $x =_A y$）表示 $x$ 和 $y$ 相等的证明。

**构造**: 
- 自反性: $\text{refl}_x : x =_A x$
- 路径归纳: $\text{ind}_{=_A} : \Pi P.(\Pi x.P(x,x,\text{refl}_x)) \to \Pi x,y.\Pi p:x=y.P(x,y,p)$

---

## 5. 构造演算与CoC

### 5.1 纯类型系统

**定义 5.1** (PTS): 纯类型系统由排序集合 $\mathcal{S}$、轴 $\mathcal{A}$ 和规则 $\mathcal{R}$ 确定。

**定义 5.2** (构造演算CC): CC的规则：
- $(*, *)$: 项到项的函数（简单函数）
- $(*, \square)$: 谓词（项到类型的函数）
- $(\square, *)$: 多态类型
- $(\square, \square)$: 类型构造子

---

### 5.2 Calculus of Inductive Constructions

**定义 5.3** (CIC): Coq基于CIC，添加：
- 归纳定义
- 共归纳定义
- 宇宙多态

**定理 5.1**: CIC是强正规化的，且与构造性集合论一致。

---

## 6. 同伦类型论

### 6.1 单值公理

**定义 6.1** (同伦层级): 
- **命题** (-1-类型): 所有元素相等的类型
- **集合** (0-类型): 等式是命题的类型
- **群胚** (1-类型): 等式是集合的类型

**定义 6.2** (等价): 函数 $f : A \to B$ 是等价，若存在 $g : B \to A$ 使得 $f \circ g \sim \text{id}_B$ 和 $g \circ f \sim \text{id}_A$。

**公理 6.1** (单值公理/Univalence Axiom): 
$$(A =_\mathcal{U} B) \simeq (A \simeq B)$$
等价类型是相等的。

---

### 6.2 高阶归纳类型

**定义 6.3** (HIT): 高阶归纳类型允许路径构造子。

**示例 6.1** (圆 $S^1$): 
- 点构造子: $\text{base} : S^1$
- 路径构造子: $\text{loop} : \text{base} =_{S^1} \text{base}$

---

## 7. 目录结构

```
docs/07-数理逻辑/05-类型论/
├── 00-README.md                    # 本文件
├── 01-简单类型λ演算.md              # 基本类型系统
├── 02-Curry-Howard同构.md           # 证明即程序
├── 03-Martin-Löf类型论.md           # 直觉主义类型论
├── 04-归纳类型.md                   # 自然数、列表
├── 05-构造演算.md                   # CoC、CIC
├── 06-同伦类型论.md                 # HoTT基础
└── 07-实战问题.md                   # 类型推导练习
```

---

## 8. 学习路径

### 8.1 基础路径
**λ演算** → **简单类型** → **Curry-Howard** → **依赖类型** → **证明助手**

### 8.2 应用路径
- **形式化证明**: Lean、Coq、Agda
- **函数式编程**: Haskell、OCaml
- **范畴语义**: CCC、Topos理论

---

**最后更新**: 2026年4月5日  
**维护者**: FormalMath项目组  
**质量等级**: ⭐⭐⭐⭐⭐ (研究级)
