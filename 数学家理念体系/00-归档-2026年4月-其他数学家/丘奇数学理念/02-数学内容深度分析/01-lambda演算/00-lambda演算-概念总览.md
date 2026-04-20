---
title: "01-lambda演算：概念总览"
msc_primary: "01A60"
msc_secondary: ["03B40", "68N18", "68Q55"]
processed_at: '2026-04-05'
---

# 01-lambda演算：概念总览

**文档类型**：概念总览与深度分析
**创建日期**：2026年2月10日
**关联**：[丘奇数学理念 02-数学内容深度分析](./../README.md)、[project/00-国际课程与机构对齐对照表-2026年2月](./../../../../project/00-国际课程与机构对齐对照表-2026年2月.md)（1.9 丘奇/可计算性）

---

## 篇目 × 核心概念 × 先修

| 编号 | 篇目 | 核心概念 | 先修（1–2 条） |
|------|------|----------|----------------|
| 01 | [λ演算语法与语义](./01-λ演算语法与语义.md) | 项、自由/绑定变量、替换、α 转换、操作语义、Church 编码 | 无（入门） |
| 02 | [归约与范式](./02-归约与范式.md) | β 归约、η 归约、范式、合流性 | 01 |
| 03 | [不动点定理](./03-不动点定理.md) | 不动点组合子、Y 组合子、递归 | 01、02 |
| 04 | [类型化λ演算](./04-类型化λ演算.md) | 简单类型、类型规则、Curry–Howard | 01、02；04-其他贡献/01-简单类型论 可并行 |

---

## 一、λ 演算语法与语义

### 1.1 历史背景
阿隆佐·丘奇（Alonzo Church）于1930年代提出了 **λ 演算**（lambda calculus），最初目标是建立一个形式化的逻辑基础，以替代集合论和类型论。虽然最初的逻辑系统被发现不一致（Kleene–Rosser 悖论，1935），但剥离了逻辑解释的纯 λ 演算——作为一种计算模型——被证明是一致且极具表达力的。

### 1.2 语法
λ 项由以下文法生成：
$$M, N ::= x \mid \lambda x.\, M \mid M\,N$$
其中 $x$ 为变量，$\lambda x.\, M$ 为**抽象**（函数定义），$M\,N$ 为**应用**（函数调用）。

**自由变量**和**绑定变量**通过归纳定义：
- $FV(x) = \{x\}$
- $FV(\lambda x.\, M) = FV(M) \setminus \{x\}$
- $FV(M\,N) = FV(M) \cup FV(N)$

**α 转换**（alpha-conversion）允许重命名绑定变量：$\lambda x.\, M =_\alpha \lambda y.\, M[x/y]$（要求 $y \notin FV(M)$）。α 转换体现了"函数的本质不依赖于参数名称"的原则。

### 1.3 替换与操作语义
**替换** $M[x := N]$ 将 $M$ 中所有自由出现的 $x$ 替换为 $N$，同时避免**变量捕获**（capture-avoiding substitution）：
- $x[x := N] = N$
- $y[x := N] = y$（$y \neq x$）
- $(\lambda y.\, M)[x := N] = \lambda y.\, (M[x := N])$（要求 $y \notin FV(N)$ 且 $y \neq x$）
- $(M_1\,M_2)[x := N] = (M_1[x := N])\,(M_2[x := N])$

**β 归约**（beta-reduction）是 λ 演算的核心计算规则：
$$(\lambda x.\, M)\,N \to_\beta M[x := N]$$
即"将函数应用于参数，等价于将函数体中的参数替换为实际输入"。

### 1.4 Church 编码
丘奇展示了自然数可在 λ 演算中编码（**Church numerals**）：
$$\overline{n} = \lambda f.\, \lambda x.\, f^n x$$
其中 $f^n x = f(f(\cdots(fx)\cdots))$（$n$ 次应用）。基本算术运算可定义为：
- **后继**：$\mathrm{succ} = \lambda n.\, \lambda f.\, \lambda x.\, f\,(n\,f\,x)$
- **加法**：$\mathrm{add} = \lambda m.\, \lambda n.\, \lambda f.\, \lambda x.\, m\,f\,(n\,f\,x)$
- **乘法**：$\mathrm{mul} = \lambda m.\, \lambda n.\, \lambda f.\, m\,(n\,f)$

布尔值、有序对和递归函数同样可纯用 λ 项编码，这证明了 λ 演算是**图灵完备**的。

## 二、归约与范式

### 2.1 β 归约与合流性
**β 归约**的传递闭包记为 $\twoheadrightarrow_\beta$。若不存在 $N$ 使得 $M \to_\beta N$，则 $M$ 处于**β 范式**（β-normal form）。

**丘奇–罗瑟定理**（Church–Rosser theorem，1936）断言 β 归约满足**合流性**（confluence）：
$$M \twoheadrightarrow_\beta N_1 \text{ 且 } M \twoheadrightarrow_\beta N_2 \implies \exists P.\, N_1 \twoheadrightarrow_\beta P \text{ 且 } N_2 \twoheadrightarrow_\beta P$$
合流性的推论包括：
- 若项有范式，则范式唯一
- 项的等价性（$=_\beta$）是可判定的，当且仅当项有范式

### 2.2 η 归约与扩展等价
**η 归约**捕获了"外延相等"的概念：
$$\lambda x.\, (M\,x) \to_\eta M \quad (x \notin FV(M))$$
即"对所有输入产生相同输出的函数是相同的"。η 归约与 β 归约共同生成 **βη 等价** $=_{\beta\eta}$，这是 λ 演算的标准外延等价关系。

### 2.3 范式与可判定性
并非所有 λ 项都有 β 范式。经典的非规范化项是 **Y 组合子**的应用（见第三节）。对于**简单类型 λ 演算**（simply typed lambda calculus），丘奇证明了**强规范化**（strong normalization）：每个良类型的项都在有限步内归约到唯一的 β 范式。这一性质是类型系统安全性的理论基础。

## 三、不动点定理

### 3.1 Y 组合子
在 λ 演算中，递归通过**不动点组合子**实现。最著名的例子是 **Y 组合子**：
$$Y = \lambda f.\, (\lambda x.\, f\,(x\,x))\,(\lambda x.\, f\,(x\,x))$$
Y 组合子满足不动点性质：
$$Y\,f =_\beta f\,(Y\,f)$$
即 $Y\,f$ 是 $f$ 的不动点。

### 3.2 递归函数的定义
利用 Y 组合子，可定义任意递归函数。例如，阶乘函数可写为：
$$\mathrm{fact} = Y\,(\lambda f.\, \lambda n.\, \mathrm{ifz}\,n\,\overline{1}\,(\mathrm{mul}\,n\,(f\,(\mathrm{pred}\,n)))$$
其中 $\mathrm{ifz}$ 为零测试。展开后得到：
$$\mathrm{fact}\,\overline{n} =_\beta \mathrm{ifz}\,\overline{n}\,\overline{1}\,(\mathrm{mul}\,\overline{n}\,(\mathrm{fact}\,(\mathrm{pred}\,\overline{n})))$$
这正是阶乘的递归定义。

### 3.3 图灵完备性
丘奇与图灵独立证明了 λ 演算与图灵机在计算能力上等价：任何图灵机可计算的函数都是 λ 可定义的，反之亦然。这一等价性构成了**丘奇–图灵论题**的核心证据。

## 四、类型化 λ 演算

### 4.1 简单类型系统
丘奇在1940年为 λ 演算引入了**简单类型**（simple types）：
$$\sigma, \tau ::= \iota \mid o \mid \sigma \to \tau$$
类型判断规则确保良类型程序的安全性和终止性：
- 变量：$\Gamma, x:\sigma \vdash x:\sigma$
- 抽象：$\dfrac{\Gamma, x:\sigma \vdash M:\tau}{\Gamma \vdash \lambda x:\sigma.\, M : \sigma \to \tau}$
- 应用：$\dfrac{\Gamma \vdash M:\sigma \to \tau \quad \Gamma \vdash N:\sigma}{\Gamma \vdash M\,N : \tau}$

### 4.2 Curry–Howard 对应
简单类型 λ 演算与直觉主义命题逻辑通过 **Curry–Howard 同构** 建立精确对应：

| 逻辑 | 类型论 | 计算 |
|------|--------|------|
| 命题 $A$ | 类型 $A$ | 问题规范 |
| 证明 $p : A$ | 项 $M : A$ | 程序 |
| $A \to B$ | 函数类型 $A \to B$ | 计算变换 |
| 合取 $A \land B$ | 积类型 $A \times B$ | 配对 |
| 析取 $A \lor B$ | 和类型 $A + B$ | 变体 |

这一对应将**证明即程序**（proofs as programs）和**命题即类型**（propositions as types）统一起来，成为现代函数式编程语言（Haskell、ML、Coq、Lean）的理论基石。

---

## 快速定位

- **入门链**：01 → 02 → 03；04 可与 02-递归论、03-可计算性 衔接。
- **国际课程对照**：Oxford Lambda Calculus and Types、Harvard CS152、Stanford CS242；见 project 对照表 1.9 节。

**文档状态**：v2.0（深度分析版）
**最后更新**：2026年4月20日
