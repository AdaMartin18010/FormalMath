---
title: "lambda演算 - 增强版"
msc_primary: "03B40"
msc_secondary: ["68N18", "68Q55", "03D10", "03B70"]
processed_at: "2026-04-05"
---

# Lambda演算 - 增强版

## 目录

- [lambda演算 - 增强版](#lambda演算---增强版)
  - [目录](#目录)
  - [📚 概述](#概述)
  - [🕰️ 历史发展脉络](#历史发展脉络)
  - [🏗️ λ演算基础](#λ演算基础)
  - [📐 组合子逻辑](#组合子逻辑)
  - [🔄 可计算性理论](#可计算性理论)
  - [💡 详细示例](#详细示例)
  - [🔧 技术实现表征](#技术实现表征)
  - [📚 总结](#总结)

---

## 📚 概述

Lambda演算是由阿隆佐·丘奇于1930年代创立的形式系统，用于研究函数定义、函数应用和递归。它与图灵机等价，是计算理论的基础模型之一，也是函数式编程语言的理论基础。

本增强版文档将详细阐述：

- λ演算的语法和归约语义
- 组合子逻辑与无点风格编程
- 类型化λ演算基础
- 丰富的计算示例与实现

---

## 🕰️ 历史发展脉络

### 创立时期 (1930s)

**丘奇的原始工作**：

- 1932：提出λ演算作为逻辑基础
- 1936：证明λ可定义函数与递归函数等价
- 1936：提出判定问题不可解

**丘奇-图灵论题**：
直觉可计算函数 = λ可定义函数 = 图灵可计算函数

### 发展时期 (1940s-1970s)

**简单类型λ演算 (1940)**：
丘奇引入类型避免悖论。

**Curry的研究**：

- 组合子逻辑 (1958)
- 类型推断的发现

**LISP的诞生 (1958)**：
约翰·麦卡锡受λ演算启发创建LISP语言。

### 现代时期 (1970s-至今)

**函数式编程复兴**：
ML (1973)、Scheme (1975)、Haskell (1990) 等语言。

**类型系统研究**：
System F、依赖类型、线性类型等。

---

## 🏗️ λ演算基础

### 语法

**λ项**：
$$M, N ::= x \mid \lambda x.M \mid M N$$

- **变量** $x$：值的占位符
- **抽象** $\lambda x.M$：函数定义
- **应用** $M N$：函数调用

**约定**：

- 应用左结合：$M N P = ((M N) P)$
- 抽象右延伸：$\lambda x.M N = \lambda x.(M N)$
- 多参数：$\lambda x y.M = \lambda x.\lambda y.M$

---

### 变量与替换

**自由变量** (FV)：
$$\begin{align}
\text{FV}(x) &= \{x\} \\
\text{FV}(\lambda x.M) &= \text{FV}(M) \setminus \{x\} \\
\text{FV}(M N) &= \text{FV}(M) \cup \text{FV}(N)
\end{align}$$

**替换** $M[N/x]$：
将 $M$ 中所有自由出现的 $x$ 替换为 $N$。

**捕获避免**：
若 $N$ 中有自由变量 $y$，而 $M$ 中有 $\lambda y.\cdots x \cdots$，则先重命名 $y$。

---

### 归约

**β-归约**：
$$(\lambda x.M) N \rightarrow_\beta M[N/x]$$

函数应用：将参数代入函数体。

**α-转换**：
$$\lambda x.M \equiv_\alpha \lambda y.M[y/x]$$
重命名绑定变量。

**η-归约**：
$$\lambda x.(M x) \rightarrow_\eta M \quad (x \notin \text{FV}(M))$$
函数与其行为的等价。

**归约策略**：
- **最左归约（正规序）**：总是归约最左边的可归约式
- ** applicative序**：先求值参数
- **惰性求值**：延迟参数求值直到需要

---

### 编码数据类型

**布尔值**：
$$\text{true} = \lambda x y.x \quad \text{(选第一个)}$$
$$\text{false} = \lambda x y.y \quad \text{(选第二个)}$$

**条件**：
$$\text{if} = \lambda b x y.b x y$$

**逻辑运算**：
$$\text{and} = \lambda b_1 b_2.b_1 b_2 \text{ false}$$
$$\text{or} = \lambda b_1 b_2.b_1 \text{ true } b_2$$
$$\text{not} = \lambda b.b \text{ false true}$$

---

**自然数（Church数）**：
$$\bar{0} = \lambda f x.x$$
$$\bar{1} = \lambda f x.f x$$
$$\bar{2} = \lambda f x.f (f x)$$
$$\bar{n} = \lambda f x.f^n x$$

数 $n$ 是"将函数应用 $n$ 次"的高阶函数。

**后继**：
$$\text{succ} = \lambda n f x.f (n f x)$$

**加法**：
$$\text{add} = \lambda m n f x.m f (n f x)$$
应用 $m$ 次后再应用 $n$ 次。

**乘法**：
$$\text{mul} = \lambda m n f.m (n f)$$
复合应用。

---

## 📐 组合子逻辑

### 基本组合子

**S组合子**：
$$S = \lambda f g x.f x (g x)$$

**K组合子**：
$$K = \lambda x y.x$$

**I组合子**：
$$I = \lambda x.x$$

**SKI关系**：
$$I = S K K$$
因为 $S K K x = K x (K x) = x$

---

### SK组合子完备性

**定理**：任何λ项都可以用S和K表示。

**转换规则** (T变换)：
- $[x]x = I$
- $[x]M = K M$ （若 $x \notin \text{FV}(M)$）
- $[x](M N) = S ([x]M) ([x]N)$

**示例**：
$[x]y = K y$

$[x](x y) = S ([x]x) ([x]y) = S I (K y)$

---

## 🔄 可计算性理论

### λ可定义性

**定义**：部分函数 $f: \mathbb{N}^k \rightharpoonup \mathbb{N}$ 是λ可定义的，如果存在λ项 $F$ 使得：
$$F \bar{n_1} \cdots \bar{n_k} = \overline{f(n_1, \ldots, n_k)}$$
（当 $f$ 有定义时）

**定理**：
λ可定义函数 = 部分递归函数 = 图灵可计算函数

---

### 不动点组合子

**Y组合子**：
$$Y = \lambda f.(\lambda x.f (x x)) (\lambda x.f (x x))$$

**性质**：
$$Y F = F (Y F)$$

**证明**：
$$\begin{align}
Y F &= (\lambda x.F (x x)) (\lambda x.F (x x)) \\
&= F ((\lambda x.F (x x)) (\lambda x.F (x x))) \\
&= F (Y F)
\end{align}$$

**递归定义**：
$$\text{fact} = Y (\lambda f n.\text{if } (n = 0) \text{ then } 1 \text{ else } n \times f (n-1))$$

---

## 💡 详细示例

### 示例 1：Church数运算

**验证 $\text{add } \bar{2} \bar{3} = \bar{5}$**：

$$\begin{align}
\text{add } \bar{2} \bar{3} &= (\lambda m n f x.m f (n f x)) \bar{2} \bar{3} \\
&=_\beta \lambda f x.\bar{2} f (\bar{3} f x) \\
&= \lambda f x.\bar{2} f ((\lambda f' x'.f'^3 x') f x) \\
&= \lambda f x.\bar{2} f (f^3 x) \\
&= \lambda f x.(\lambda f'' x''.f''^2 x'') f (f^3 x) \\
&= \lambda f x.f^2 (f^3 x) \\
&= \lambda f x.f^5 x \\
&= \bar{5}
\end{align}$$

---

### 示例 2：配对与投影

**配对构造**：
$$\text{pair} = \lambda x y z.z x y$$

**投影**：
$$\text{fst} = \lambda p.p \text{ true}$$
$$\text{snd} = \lambda p.p \text{ false}$$

**验证**：
$$\begin{align}
\text{fst } (\text{pair } M N) &= (\lambda p.p \text{ true}) ((\lambda x y z.z x y) M N) \\
&=_\beta (\lambda x y z.z x y) M N \text{ true} \\
&=_\beta \text{true } M N \\
&=_\beta M
\end{align}$$

---

### 示例 3：列表操作

**nil**：
$$\text{nil} = \lambda c n.n$$

**cons**：
$$\text{cons} = \lambda x xs c n.c x (xs c n)$$

**isnil**：
$$\text{isnil} = \lambda l.l (\lambda x y.\text{false}) \text{ true}$$

**map**：
$$\text{map} = \lambda f.Y (\lambda g l.\text{isnil } l \text{ nil } (\text{cons } (f (\text{head } l)) (g (\text{tail } l))))$$

---

## 🔧 技术实现表征

### Python λ演算解释器

```python
from dataclasses import dataclass
from typing import Union, Set, Dict

@dataclass
class Var:
    name: str

@dataclass
class Lam:
    var: str
    body: 'Term'

@dataclass
class App:
    func: 'Term'
    arg: 'Term'

Term = Union[Var, Lam, App]

def free_vars(term: Term) -> Set[str]:
    """计算自由变量"""
    if isinstance(term, Var):
        return {term.name}
    elif isinstance(term, Lam):
        return free_vars(term.body) - {term.var}
    elif isinstance(term, App):
        return free_vars(term.func) | free_vars(term.arg)

def substitute(term: Term, var: str, replacement: Term) -> Term:
    """替换 [replacement/var]term"""
    if isinstance(term, Var):
        return replacement if term.name == var else term
    elif isinstance(term, Lam):
        if term.var == var:
            return term
        elif term.var in free_vars(replacement):
            # 避免捕获，重命名
            new_var = term.var + "'"
            new_body = substitute(term.body, term.var, Var(new_var))
            return Lam(new_var, substitute(new_body, var, replacement))
        else:
            return Lam(term.var, substitute(term.body, var, replacement))
    elif isinstance(term, App):
        return App(substitute(term.func, var, replacement),
                   substitute(term.arg, var, replacement))

def beta_reduce(term: Term) -> Term:
    """一步β归约"""
    if isinstance(term, App) and isinstance(term.func, Lam):
        # (λx.M) N → M[N/x]
        return substitute(term.func.body, term.func.var, term.arg)
    elif isinstance(term, App):
        # 尝试归约函数或参数
        new_func = beta_reduce(term.func)
        if new_func is not term.func:
            return App(new_func, term.arg)
        new_arg = beta_reduce(term.arg)
        if new_arg is not term.arg:
            return App(term.func, new_arg)
    elif isinstance(term, Lam):
        new_body = beta_reduce(term.body)
        if new_body is not term.body:
            return Lam(term.var, new_body)
    return term

def normalize(term: Term, max_steps: int = 1000) -> Term:
    """正规化"""
    for _ in range(max_steps):
        new_term = beta_reduce(term)
        if new_term == term:
            return term
        term = new_term
    return term  # 可能不终止

# Church编码
def church_num(n: int) -> Term:
    """Church数"""
    body = Var("x")
    for _ in range(n):
        body = App(Var("f"), body)
    return Lam("f", Lam("x", body))

def church_true() -> Term:
    return Lam("x", Lam("y", Var("x")))

def church_false() -> Term:
    return Lam("x", Lam("y", Var("y")))

# 使用示例
if __name__ == "__main__":
    # λx.x (恒等函数)
    id_func = Lam("x", Var("x"))

    # (λx.x) y → y
    app = App(id_func, Var("y"))
    result = beta_reduce(app)
    print(f"归约结果: {result}")  # 应该是 Var("y")

    # Church数 2
    two = church_num(2)
    print(f"Church数2: {two}")
```

---

## 📚 总结

### 核心概念

| 概念 | 说明 |
|-----|-----|
| β-归约 | 函数应用的核心机制 |
| Church数 | 自然数的函数编码 |
| Y组合子 | 递归的不动点构造 |
| SK完备性 | 组合子逻辑的表达能力 |

### 与数理逻辑体系的关联

- **可计算性**：λ演算与图灵机等价
- **类型论**：简单类型、多态类型、依赖类型
- **证明论**：Curry-Howard同构
- **范畴论**：笛卡尔闭范畴语义

### 应用价值

1. **函数式编程**：LISP、ML、Haskell等语言
2. **语义学**：程序语言的指称语义
3. **类型系统**：类型推断、多态
4. **编译器设计**：优化变换的理论基础

---

**文档版本**: 增强版
**最后更新**: 2026年4月5日
**作者**: FormalMath项目
