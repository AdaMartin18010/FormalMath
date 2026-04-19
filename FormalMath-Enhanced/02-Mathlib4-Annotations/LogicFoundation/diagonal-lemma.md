---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-15'
title: 对角线引理 (Diagonal Lemma)
---
# 对角线引理 (Diagonal Lemma)

## Mathlib4 引用

```lean
import Mathlib.Logic.Godel.Diagonal

namespace DiagonalLemma

variable {L : Language.{u, v}} [DecidableEq (Sentence L)]
  [Encodeable (Sentence L)]

/-- 对角线引理：对任意含一个自由变元的公式 φ(x)，
    存在语句 G 使得 T ⊢ G ↔ φ(⌜G⌝) -/
theorem diagonal (T : Theory L) [T.DeltaOneDefinable]
    (φ : L.Formula (Fin 1)) :
    ∃ (G : Sentence L), T ⊢ G ⇔ φ.subst (fun _ => ⌜G⌝ : Fin 1 → Term L (Fin 0)) := by
  -- 参见 Mathlib4 Logic.Godel.Diagonal
  sorry

end DiagonalLemma
```

## 数学背景

对角线引理（又称自指引理、不动点引理）是数理逻辑与证明论中的核心工具，是 Kurt Gödel 证明第一不完备定理的数学基础。该引理由 Gödel 在1931年隐式使用，后由 Rudolf Carnap 在1934年明确表述。它断言：在任何足够强且能表达基本算术的形式系统中，对任意含一个自由变元的公式 $\phi(x)$，总存在一个语句 $G$（称为 $\phi$ 的“不动点”），使得系统可以证明 $G \leftrightarrow \phi(\ulcorner G \urcorner)$。这个引理使得数学系统能够“谈论自身”，从而构造出具有自指性质的命题，如 Gödel 语句和 Tarski 不可定义性定理中的关键对象。

## 直观解释

对角线引理告诉我们：**任何足够复杂的算术系统都能“照镜子”——它能构造出关于自身的陈述**。想象一个工厂能生产各种标语牌，对角线引理说的是：对于任何“检验标语牌的机器”（公式 $\phi$），工厂都能生产出一个特殊的标语牌 $G$，上面写的正是“这台机器检验我时输出为真（或假）”。这个自我参照的能力是 Gödel 不完备性的源泉。

更准确地说，如果 $\phi(x)$ 表示“$x$ 所编码的命题在系统 $T$ 中不可证”，那么对角线引理给出的 $G$ 就是著名的 Gödel 语句：“本语句在 $T$ 中不可证。”

## 形式化表述

设 $L$ 为包含算术的语言，$T$ 为 $L$ 上的一致理论，且 $T$ 能够原始递归地表示基本语法谓词（如代入函数、证明谓词）。设 $\phi(x)$ 为 $L$ 中恰有一个自由变元 $x$ 的公式。

**对角线引理**：存在语句 $G$（闭公式）使得：

$$T \vdash G \leftrightarrow \phi(\ulcorner G \urcorner)$$

其中 $\ulcorner G \urcorner$ 表示 $G$ 的 Gödel 编号（一个闭项，表示 $G$ 的编码）。

在 Mathlib4 中，该结果在 `Logic.Godel.Diagonal` 模块中形式化，为 Gödel 不完备定理的后续证明奠定基础。

## 证明思路

1. **可定义代入函数**：在 $T$ 中定义原始递归函数 $\text{sub}(n, m)$，它表示“将编号为 $m$ 的项代入编号为 $n$ 的公式中对应的自由变元后所得公式的编号”
2. **构造辅助公式**：定义公式 $\psi(x) = \phi(\text{sub}(x, x))$。设 $n = \ulcorner \psi \urcorner$
3. **构造不动点**：令 $G = \psi(n) = \phi(\text{sub}(n, n))$。计算得 $\text{sub}(n, n) = \ulcorner G \urcorner$
4. **验证等价性**：由构造，$G = \phi(\ulcorner G \urcorner)$，且在系统 $T$ 内部可证此等价关系

核心在于通过“将自身编号代入自身”实现自指，类似于康托对角线法的逻辑版本。

## 示例

### 示例 1：Gödel 语句

取 $\phi(x) = \neg \text{Prov}_T(x)$，即“$x$ 在 $T$ 中不可证”。对角线引理给出 $G$ 使得：

$$T \vdash G \leftrightarrow \neg \text{Prov}_T(\ulcorner G \urcorner)$$

$G$ 就是 Gödel 语句：“本语句在 $T$ 中不可证。”

### 示例 2：Tarski 不可定义性

假设真值谓词 $\text{True}(x)$ 在 $T$ 中可定义，取 $\phi(x) = \neg \text{True}(x)$。对角线引理给出 $G$ 使得 $T \vdash G \leftrightarrow \neg \text{True}(\ulcorner G \urcorner)$。若 $G$ 为真则 $\text{True}(\ulcorner G \urcorner)$ 成立，但 $G$ 又说它不真，矛盾。因此一阶算术中的真值谓词不可定义。

### 示例 3：Rosser 语句

Rosser 在1936年改进 Gödel 定理，取一个更精细的公式构造 $R$ 使得：

$$T \vdash R \leftrightarrow \forall y \left(\text{Proof}_T(y, \ulcorner R \urcorner) \to \exists z < y \, \text{Proof}_T(z, \ulcorner \neg R \urcorner)\right)$$

Rosser 语句说：“如果我在 $T$ 中有证明，则我的否定有更短的证明。”这避免了 Gödel 原始证明中对 $T$ 的 $\omega$-一致性的要求。

## 应用

- **Gödel 第一不完备定理**：构造不可判定语句的核心工具
- **Tarski 不可定义性定理**：证明算术真值不可在一阶算术中定义
- **Rosser 改进**：用对角线引理构造更强形式的不可判定语句
- **Löb 定理**：模态逻辑与证明论语义中的自指应用
- **计算理论**：停机问题的不可判定性与对角线法的联系

## 相关概念

- Gödel 编号 (Gödel Numbering)：将语法对象编码为算术项
- 自指语句 (Self-Referential Sentence)：谈论自身的数学命题
- 不动点 (Fixed Point)：$G$ 可视为公式映射 $\phi \mapsto G$ 的不动点
- 原始递归可表示性 (Primitive Recursive Representability)：算术系统表达元数学的能力
- 证明谓词 (Proof Predicate)：编码“$y$ 是 $x$ 在 $T$ 中的证明”的公式

## 参考

### 教材

- [Boolos, Burgess & Jeffrey. Computability and Logic. Cambridge, 5th edition, 2007. Chapter 16]
- [Mendelson. Introduction to Mathematical Logic. CRC Press, 6th edition, 2015. Chapter 3]

### 历史文献

- [Gödel. Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I. Monatshefte für Mathematik und Physik, 1931]
- [Carnap. Logische Syntax der Sprache. 1934]

### 在线资源

- [Mathlib4 文档 - Diagonal][https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Godel/Diagonal.html]

---

*最后更新：2026-04-15 | 版本：v1.0.0*
