---
title: "Lean4 vs Coq vs Isabelle"
msc_primary: "03"
---

# 证明助手系统对比

## 概述

本文档从数学基础、逻辑表达力、证明自动化及工程实践四个维度，系统对比四个主流的定理证明系统：Lean4、Coq、Isabelle/HOL 和 Agda。这些系统在现代数学形式化、软件验证及类型理论研究中扮演着核心角色。

## 1. 形式化基础

### 1.1 逻辑与类型理论

**定义 1.1（依赖类型）**. 给定类型族 $B : A \to \mathcal{U}$，依赖乘积类型（Π-类型）定义为

$$\Pi_{x:A} B(x) \;:=\; \{ f \mid \forall x:A,\; f(x) : B(x) \}.$$

依赖和类型（Σ-类型）定义为

$$\Sigma_{x:A} B(x) \;:=\; \{ (x, y) \mid x:A,\; y:B(x) \}.$$

**定义 1.2（归纳构造演算，CIC）**. CIC 是扩展了归纳类型与宇宙层次的依赖类型理论。其核心判断包括：
- 良形性：$\Gamma \vdash A : \mathcal{U}_i$
- 类型归属：$\Gamma \vdash t : A$
- 等价性：$\Gamma \vdash t \equiv u : A$

**定理 1.1（强规范化）**. 在 CIC 中，任何良类型的项 $t : A$ 都满足强规范化性质：不存在无限规约序列 $t \to t_1 \to t_2 \to \cdots$。

*证明概要*：通过可访问性谓词（Accessibility Predicate）与逻辑关系（Logical Relations）构造归纳论证，证明所有良类型项均终止。该性质保证了类型检查算法的可判定性。∎

### 1.2 各系统的逻辑基础

| 特性 | Lean4 | Coq | Isabelle/HOL | Agda |
|------|-------|-----|--------------|------|
| **类型理论** | 依赖类型 (CIC) | 归纳构造演算 (CIC) | 简单类型 + HOL | 依赖类型 (MLTT) |
| **逻辑基础** | 构造性 + 经典（可选） | 构造性（默认） | 经典 | 构造性 |
| **宇宙层次** | 累积 + 非累积 | 累积 | N/A | 累积 |
| **编程范式** | 函数式 | 函数式 | 函数式 + 命令式 | 纯函数式 |
| **自动化** | 中等 | 强 | 很强 | 弱 |
| **性能** | 优秀（编译到 C） | 良好 | 良好 | 良好 |
| **数学库规模** | 极大 (Mathlib4) | 大 | 大 (AFP) | 中等 |
| **学习曲线** | 中等 | 陡峭 | 平缓 | 中等 |
| **IDE 支持** | VS Code (Lean4 插件) | CoqIDE / VS Code | Isabelle/jEdit | Emacs / VS Code |
| **元编程** | 优秀 (Macro / Elab) | 良好 (Ltac / Ltac2) | 中等 (ML / Eisbach) | 良好 (Reflection) |

## 2. 各系统的数学表达力

### 2.1 Lean4

Lean4 基于归纳构造演算，支持不可变宇宙（Non-cumulative Universes）与商类型（Quotient Types）。其类型系统允许直接表达高阶泛函与依赖类型。

**定义 2.1（商类型）**. 给定类型 $A$ 与等价关系 $R : A \to A \to \mathsf{Prop}$，商类型 $A / R$ 的元素为等价类 $[a]_R$，并满足消去原理：若 $f : A \to B$ 满足 $R(a, a') \Rightarrow f(a) = f(a')$，则存在唯一的 $\bar{f} : A/R \to B$ 使得下图交换：

$$\bar{f}([a]_R) = f(a).$$

**定理 2.1（Lean4 中实数的构造完备性）**. 在 Mathlib4 中，实数 $\mathbb{R}$ 定义为 Cauchy 序列的商类型：

$$\mathbb{R} \;:=\; \{ (x_n)_{n\in\mathbb{N}} \mid x_n \in \mathbb{Q},\; \text{Cauchy} \} \;/\; \sim,$$

其中 $(x_n) \sim (y_n)$ 当且仅当 $\forall \varepsilon > 0,\; \exists N,\; \forall n \geq N,\; |x_n - y_n| < \varepsilon$。此构造满足域公理与序完备性。

*应用*：Mathlib4 已利用此构造形式化了从基本分析到复几何的完整理论体系，包括微分形式、层上同调与代数几何的基本概念。

### 2.2 Coq

Coq 同样基于 CIC，但其默认逻辑为构造性逻辑，排斥排中律（LEM）与选择公理（AC），除非显式添加为公理。

**定理 2.2（Curry-Howard 同构，在 Coq 中的实现）**. 在 Coq 中，命题 $P$ 对应类型，证明 $p : P$ 对应该类型的 inhabitant。具体地：

| 逻辑连接词 | 类型构造子 |
|-----------|-----------|
| $P \land Q$ | $P \times Q$（积类型） |
| $P \lor Q$ | $P + Q$（和类型） |
| $P \Rightarrow Q$ | $P \to Q$（函数类型） |
| $\forall x:A,\; P(x)$ | $\Pi_{x:A} P(x)$（依赖乘积） |
| $\exists x:A,\; P(x)$ | $\Sigma_{x:A} P(x)$（依赖和） |
| $\neg P$ | $P \to \bot$（到空类型的函数） |

**定义 2.2（程序提取）**. Coq 的提取机制（Extraction）将构造性证明中的计算内容转换为 OCaml、Haskell 或 Scheme 的可执行代码。若 $P$ 为 $\Sigma$-类型，则提取过程保留其 witness 作为运行时的具体值。

**例子 2.1（欧几里得算法的提取）**. 在 Coq 中证明 $\forall a,b \in \mathbb{N},\; \exists d,\; d = \gcd(a,b)$ 后，提取机制可自动生成计算最大公约数的 OCaml 函数：

```ocaml
let rec gcd a b = if b = 0 then a else gcd b (a mod b)
```

### 2.3 Isabelle/HOL

Isabelle/HOL 基于经典高阶逻辑（Higher-Order Logic），其类型系统为简单类型 lambda 演算，通过 axiomatic type classes 支持多态与重载。

**定义 2.3（高阶逻辑，HOL）**. HOL 的语言由以下项构成：
- 类型：$\iota$（个体）、$o$（布尔值）、$\sigma \to \tau$（函数类型）
- 项：变量 $x^\sigma$、常量 $c^\sigma$、应用 $t\,u$、抽象 $\lambda x^\sigma.\, t$

**定理 2.3（Isabelle 的 LCF 架构可靠性）**. Isabelle 的核心推理引擎（Kernel）仅通过少量可信赖的推理规则生成定理。任何用户定义的 tactic 或自动化工具最终必须调用这些核心规则，因此无法推导出假命题（假设核心实现正确）。

*证明思路*：LCF 架构将定理表示为抽象数据类型（Abstract Data Type），其构造函数对应于 Hilbert 风格的推理规则（如假言推理、泛化、等式替换）。用户无法直接伪造定理对象。∎

**定理 2.4（Sledgehammer 的完备性启发式）**. Isabelle 的 Sledgehammer 工具将目标命题翻译为一阶逻辑（TPTP 格式），调用外部 ATP（如 E、Vampire、Z3）。若外部 ATP 找到反证，则通过 MaSh 或 Metis 重构为 Isabelle 可接受的小规模证明。该过程在经典逻辑片段上是可靠且相对完备的。

### 2.4 Agda

Agda 基于 Martin-Löf 类型理论（MLTT），强调证明的可读性与构造性，支持归纳-归纳定义与无公理 K（--without-K）。

**定义 2.4（无公理 K）**. 在 MLTT 中，对类型 $A$ 与 $a : A$，恒等类型 $a =_A a$ 的元素包括自反路径 $\mathsf{refl}_a$。公理 K 断言：

$$K : \prod_{A:\mathcal{U}} \prod_{a:A} \prod_{P:(a=a) \to \mathcal{U}} \Big( P(\mathsf{refl}_a) \to \prod_{p:a=a} P(p) \Big).$$

禁用 K 后，Agda 可用于探索同伦类型论（HoTT）中的高阶路径结构。

**定理 2.5（Agda 中的路径归纳）**. 在禁用 K 的 Agda 中，J-消去子（路径归纳）成立：

$$J : \prod_{A:\mathcal{U}} \prod_{a:A} \prod_{P:\prod_{x:A} (a=x) \to \mathcal{U}} \Big( P(a, \mathsf{refl}_a) \to \prod_{x:A} \prod_{p:a=x} P(x, p) \Big).$$

这是同伦类型论中路径提升（Path Lifting）与传输（Transport）的基础。

## 3. 形式化案例对比

### 3.1 四色定理

**定理 3.1（四色定理）**. 任何平面图都可以用至多四种颜色着色，使得相邻区域颜色不同。

- **Coq 形式化**：Gonthier（2008）使用 SSReflect 方法在 Coq 中完成证明。核心思路是将问题归约为不可约构型的集合，通过计算验证每个构型的可约性。
- **Isabelle 形式化**：未完全在 Isabelle 中完成，但部分图论基础已形式化于 AFP 中。

### 3.2 奇阶定理（Feit-Thompson）

**定理 3.2（Feit-Thompson 奇阶定理）**. 任何奇数阶有限群都是可解群。

- **Coq 形式化**：MathComp 项目通过 SSReflect 在 Coq 中完成了约 15 万行的形式化证明，涉及有限群表示论与特征标理论的完整形式化。
- **Lean4 形式化**：Mathlib4 包含了群论的可解性定义与相关引理，但完整证明仍在进行中。

### 3.3 素数定理

**定理 3.3（素数定理）**. 令 $\pi(x)$ 为不超过 $x$ 的素数个数，则

$$\pi(x) \sim \frac{x}{\ln x}, \quad x \to \infty.$$

- **Isabelle 形式化**：Harrison（1996）在 HOL Light 中完成；Isabelle/HOL 的 AFP 中亦有基于复分析的证明，涉及 $\zeta$ 函数的解析延拓与围道积分。

## 4. 互操作性

现代形式化数学的发展催生了跨系统互操作的需求。主要技术路径包括：

**定义 4.1（证明交换格式）**. Dedukti 是一种通用的逻辑框架，基于扩展的 $\lambda\Pi$-演算（LF）与重写逻辑。其目标是将不同证明助手的证明翻译为统一的底层表示，再通过反编码（Deduction Modulo Rewriting）生成目标系统的证明。

```
Lean4 ←→ Coq:     通过导出/导入语法（部分支持）
Lean4 ←→ Isabelle: 有限支持（通过手动翻译）
Coq ←→ Isabelle:   通过 Dedukti 中间表示
Agda ←→ 其他:      通过编译到 Haskell（提取计算内容）
```

**定理 4.1（逻辑翻译的可靠性）**. 若存在从系统 $\mathcal{S}_1$ 到 $\mathcal{S}_2$ 的忠实翻译（Faithful Translation）$\phi$，则对 $\mathcal{S}_1$ 中的任何定理 $T$，$\phi(T)$ 在 $\mathcal{S}_2$ 中可证。该性质要求 $\phi$ 保持逻辑连接词与推理规则的对应关系。

## 5. 选择建议

| 应用场景 | 推荐系统 | 核心理由 |
|----------|----------|----------|
| 纯数学形式化 | Lean4 | Mathlib4 的广度与深度无可比拟 |
| 软件验证 | Isabelle/HOL | Sledgehammer 与 LCF 架构的可靠性 |
| 构造性数学与程序提取 | Coq | Curry-Howard 同构的原生支持 |
| 类型理论 / HoTT 研究 | Agda / Lean4 | 无公理 K 与宇宙多态 |
| 教学入门 | Lean4 / Isabelle | 活跃的社区与丰富的学习资源 |
| 工业级系统验证 | Isabelle/HOL | 经过充分验证的工具链 |

## 6. 交叉引用

- [各系统优势分析](docs/09-形式化证明/证明系统对比/01-各系统优势分析.md) — 各证明系统的详细优势与劣势
- [互操作性分析](docs/09-形式化证明/证明系统对比/02-互操作性分析.md) — 系统间翻译与逻辑框架
- [证明系统基础](docs/09-形式化证明/01-证明系统基础.md) — 证明系统的通用理论基础
- [类型论与证明](docs/09-形式化证明/04-类型论与证明-深化版.md) — 类型理论的深入讨论

---

**适用**：docs/09-形式化证明/
