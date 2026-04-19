---
msc_primary:
  - 00A99
  - 03C90
  - 03B35
title: 语义模型
processed_at: '2026-04-05'
---

# 语义模型

语义模型（Semantic Models）是数理逻辑、理论计算机科学与数学基础的交叉核心领域。它研究形式语言、逻辑系统与计算过程的意义赋予机制——即如何从抽象的句法结构过渡到具体的数学解释。从 Tarski 的真值定义到 Scott 的域理论，从 Kripke 的可能世界语义到 Girard 的线性逻辑相位语义，语义模型为我们理解"证明即程序、公式即类型"的深刻同构提供了坚实的数学基础。

## 1. Tarski 语义

### 1.1 真之定义

**定义 1.1（满足）**. 对一阶语言 $\mathcal{L}$、结构 $\mathcal{M}$ 和赋值 $s$，定义 $\mathcal{M} \models \phi[s]$ 归纳于公式结构：
- $\mathcal{M} \models R(t_1, \dots, t_n)[s]$ 当且仅当 $R^\mathcal{M}(t_1^\mathcal{M}[s], \dots)$；
- $\mathcal{M} \models \forall x \phi[s]$ 当且仅当对所有 $a \in M$，$\mathcal{M} \models \phi[s(x/a)]$。

**定理 1.2（Tarski）**. 在一阶逻辑中，"真"（在结构中满足）是良定义的。

## 2. 范畴语义

### 2.1 笛卡尔闭范畴

**定义 2.1（CCC）**. 范畴 $\mathcal{C}$ 称为笛卡尔闭的，若有：
1. 终对象；
2. 二元积；
3. 指数对象 $B^A$ 满足 $\mathcal{C}(C \times A, B) \cong \mathcal{C}(C, B^A)$。

**定理 2.2（Lambek）**. 简单类型 $\lambda$-演算的模型恰为笛卡尔闭范畴。

### 2.2 Topos 语义

**定义 2.3（子对象分类子）**. Topos 中的对象 $\Omega$ 配备真值映射 $\mathsf{true}: 1 \to \Omega$，使得对每个单态射 $m: A \to B$，存在唯一的特征映射 $\chi_m: B \to \Omega$ 使下图拉回：

$$\begin{CD} A @>>> 1 \\ @V{m}VV @VV{\mathsf{true}}V \\ B @>{\chi_m}>> \Omega \end{CD}$$

## 3. 域理论与 Scott 语义

### 3.1 完全偏序

**定义 3.1（cpo）**. 完全偏序（complete partial order）是有向集都有上确界的偏序集。

**定义 3.2（连续函数）**. $f: D \to E$ 连续，若保向上确界。

**定理 3.3（不动点）**. 设 $D$ 为有底元 $\bot$ 的 cpo，$f: D \to D$ 连续。则 $f$ 有最小不动点 $\mathsf{fix}(f) = \sup_n f^n(\bot)$。

## 4. 例子

### 4.1 例子：命题逻辑的代数语义

命题逻辑对应 Boolean 代数：
- 命题变量 $
Rightarrow$ Boolean 代数中的原子
- $\wedge 
Rightarrow$ 交
- $\vee 
Rightarrow$ 并
- $\neg 
Rightarrow$ 补

**定理 4.1（Stone 表示）**. 每个 Boolean 代数同构于某集合域上的代数。

### 4.2 例子：Kripke 语义

直觉主义逻辑的 Kripke 模型 $(W, \leq, V)$：
- $W$ 为可能世界集；
- $\leq$ 为偏序（知识增长）；
- $V$ 为单调赋值。

$w \Vdash \phi$ 归纳定义，$w \Vdash \phi \to \psi$ 当且仅当对所有 $w' \geq w$，$w' \Vdash \phi$ 蕴含 $w' \Vdash \psi$。

## 5. 交叉引用

- [模型论](docs/07-数理逻辑/模型论-基础.md) — 结构与满足关系
- [类型论](docs/01-基础数学/类型论-基础.md) — Curry-Howard 与范畴语义
- [范畴论](docs/01-基础数学/范畴论-基础.md) — CCC 与 Topos
- [可计算性](docs/07-数理逻辑/04-可计算性理论/02-核心定理.md) — 域理论与不动点

---

**适用**：docs/10-语义模型/
