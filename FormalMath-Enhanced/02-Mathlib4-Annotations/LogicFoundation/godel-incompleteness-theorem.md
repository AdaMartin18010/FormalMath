---
msc_primary: 00A99
processed_at: '2026-04-15'
title: Gödel 不完备定理 (Gödel's Incompleteness Theorems)
---
# Gödel 不完备定理 (Gödel's Incompleteness Theorems)

## Mathlib4 引用

```lean
import Mathlib.Logic.Godel.GodelBetaFunction
import Mathlib.Logic.Godel.Diagonal

namespace GodelIncompleteness

-- 注：Mathlib4 中 Gödel 不完备定理的完整形式化
-- 目前仍在发展中，但相关的可计算性、编码（Gödel 编号）
-- 以及对角线引理已有部分形式化。
-- 以下给出标准的不完备性定理表述框架。

variable {L : Language} {T : Theory L} [DecidableEq (Sentence L)]
  [Encodeable (Sentence L)]

/-- 第一不完备定理：一致的、足够强的可公理化理论 T 不完备 -/
theorem first_incompleteness
    (hconsistent : Consistent T)
    (hrep : RepresentsPrimitiveRecursive T)
    (haxiom : RecursivelyAxiomatizable T) :
    ¬Complete T := by
  -- Mathlib4 中该定理的完整形式化目前仍在建设中。
  -- 参见 Logic.Godel 相关模块的进展。
  sorry

/-- 第二不完备定理：一致的理论 T 不能证明自身的一致性 -/
theorem second_incompleteness
    (hconsistent : Consistent T)
    (hrep : RepresentsPrimitiveRecursive T)
    (haxiom : RecursivelyAxiomatizable T) :
    ¬T ⊢ᶠ consistencySentence T := by
  --  Mathlib4 中该定理的完整形式化目前仍在建设中。
  sorry

end GodelIncompleteness
```

## 数学背景

Gödel 不完备定理是20世纪数学与逻辑学中最具革命性的成果，由奥地利逻辑学家 Kurt Gödel 于1931年发表。第一不完备定理断言：任何足够强且一致的形式系统（如 Peano 算术）都不可能既是完备的（能判定所有命题）又是可公理化的。第二不完备定理进一步指出：这样的系统如果一致，则无法在其内部证明自身的一致性。这两一定理彻底粉碎了 Hilbert 计划将所有数学归结为有限、完备公理系统的梦想，深刻影响了数学基础、计算机科学和哲学认识论。

## 直观解释

**第一不完备定理**：想象一个足够复杂的“说谎者谜题”被写进了一本书（形式系统）。如果你尝试在这本书的框架内判断“这句话在这本书里无法被证明”是真是假，就会陷入悖论：如果它为假，那么它可被证明，但它说的是自己不可被证明；如果它为真，那么它不可被证明，意味着书中存在真但无法证明的命题。Gödel 的天才之处在于，他利用**Gödel 编号**将这种自指句严格编码进了算术语言中。

**第二不完备定理**：这本书不仅无法证明自己说的是对的，还无法证明自己内部没有矛盾。

## 形式化表述

设 $T$ 为包含 Robinson 算术 $Q$（或 Peano 算术 $PA$）的一致、可递归公理化理论。

**第一不完备定理**：$T$ 不完备，即存在算术命题 $G$（Gödel 语句）使得 $T \not\vdash G$ 且 $T \not\vdash \neg G$。

**第二不完备定理**：若 $T$ 一致，则 $T \not\vdash \text{Con}(T)$，其中 $\text{Con}(T)$ 是编码“$T$ 一致”的算术语句。

在 Mathlib4 中，相关基础（Gödel β-函数、编码、对角线引理）已有部分形式化，但完整的不完备性定理证明仍在建设中。

## 证明思路

**第一不完备定理**：
1. **算术化元数学**：给形式语言中的符号、公式、证明序列分配自然数编码（Gödel 编号）
2. **可表示性**：证明关键语法谓词（如“$x$ 是公式”、“$x$ 是 $y$ 的证明”）在 $T$ 中是原始递归可表示的
3. **对角线引理**：对任意含一个自由变元的公式 $\phi(x)$，存在语句 $G$ 使得 $T \vdash G \leftrightarrow \phi(\ulcorner G \urcorner)$
4. **构造 Gödel 语句**：取 $\phi(x) = \neg\text{Proof}_T(x, \ulcorner 0=1 \urcorner)$，则对角线引理给出 $G$ 满足 $T \vdash G \leftrightarrow \neg\text{Prov}_T(\ulcorner G \urcorner)$
5. **一致性推导不可证**：若 $T \vdash G$，则 $T \vdash \neg\text{Prov}_T(\ulcorner G \urcorner)$，但同时 $T$ 可证明自身的可证性，导致 $T \vdash 0=1$，矛盾

**第二不完备定理**：
1. 形式化第一不完备定理的证明，使其在 $T$ 内部可表达
2. 证明 $T \vdash \text{Con}(T) \to G$
3. 由第一不完备定理 $T \not\vdash G$，得 $T \not\vdash \text{Con}(T)$

## 示例

### 示例 1：Gödel 语句

$G$: “本语句在 $PA$ 中不可证。”若 $PA$ 一致，则 $G$ 为真但不可证。

### 示例 2：Hilbert 计划

Hilbert 希望为数学找到一个有限、一致、完备的公理基础。Gödel 不完备定理证明：对于任何足够强的一致系统，完备性是不可能的。

### 示例 3：Goodstein 定理

Goodstein 定理是一个关于自然数的真命题，它在 $PA$ 中不可证，但可以在更强的系统（如 ZFC）中证明。这是第一不完备定理的具体实例。

## 应用

- **计算理论**：停机问题的不可判定性与 Gödel 定理的联系
- **密码学与证明系统**：零知识证明与形式化验证的极限
- **人工智能**：形式系统自动推理的理论边界
- **哲学认识论**：人类心智与机器计算能力的辩论
- **集合论**：大基数公理与真理的超越性研究

## 相关概念

- Gödel 编号 (Gödel Numbering)：将语法对象编码为自然数
- 对角线引理 (Diagonal Lemma)：构造自指语句的核心工具
- 原始递归函数 (Primitive Recursive Function)：可算术化的计算模型
- 可表示性 (Representability)：元数学谓词在形式系统中的表达
- 一致性 (Consistency)：系统不能同时证明命题及其否定

## 参考

### 教材

- [Boolos, Burgess & Jeffrey. Computability and Logic. Cambridge, 5th edition, 2007. Chapters 16-17]
- [Mendelson. Introduction to Mathematical Logic. CRC Press, 6th edition, 2015. Chapter 3]

### 历史文献

- [Gödel. Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I. Monatshefte für Mathematik und Physik, 1931]

### 在线资源

- [Mathlib4 文档 - Godel][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Godel.html]
- **注意**：Mathlib4 中 Gödel 不完备定理的完整形式化目前仍在发展中，Gödel β-函数和对角线引理已有部分实现。

---

*最后更新：2026-04-15 | 版本：v1.0.0*
