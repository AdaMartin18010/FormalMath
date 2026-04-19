---
msc_primary: 49

  - 49J45
exercise_id: ANA-216
title: Gamma收敛与变分逼近
difficulty: 4
type: PRF
topic: 实分析
subtopic: 变分法
source:
  course: 变分学进阶
  chapter: "7.2"
  original: true
processed_at: '2026-04-10'
---

# ANA-216: Gamma收敛与变分逼近

**题号**: ANA-216
**难度**: ⭐⭐⭐⭐ (Level 4)
**类型**: 证明型 (PRF)
**来源**: 变分学进阶 Chapter 7.2
**主题**: De Giorgi的Gamma收敛

---

## 题目

设 $X$ 是度量空间，$F_\varepsilon, F: X \to [0, +\infty]$。称 $F_\varepsilon$ $\Gamma$-收敛于 $F$ 如果：

**(i) 下界不等式**：若 $x_\varepsilon \to x$，则 $\liminf F_\varepsilon(x_\varepsilon) \geq F(x)$

**(ii) 恢复序列**：对每个 $x \in X$，存在 $x_\varepsilon \to x$ 使得 $\lim F_\varepsilon(x_\varepsilon) = F(x)$

**证明**：若 $F_\varepsilon \stackrel{\Gamma}{\to} F$ 且 $x_\varepsilon$ 是 $F_\varepsilon$ 的极小化子，则存在子列 $x_{\varepsilon_k} \to x$，$x$ 是 $F$ 的极小化子且 $F_\varepsilon(x_\varepsilon) \to F(x)$。

---

## 解答

**Step 1: 紧性**

假设 $F_\varepsilon$ 是等强制的，即水平集 $\{F_\varepsilon \leq t\}$ 相对紧。

**Step 2: 收敛子列**

由强制性，$x_\varepsilon$ 位于紧集，存在收敛子列 $x_{\varepsilon_k} \to x$。

**Step 3: 下界估计**

由下界不等式：$F(x) \leq \liminf F_{\varepsilon_k}(x_{\varepsilon_k})$

**Step 4: 比较原理**

对任意 $y \in X$，取恢复序列 $y_\varepsilon \to y$，则：
$$F(x) \leq \liminf F_\varepsilon(x_\varepsilon) \leq \limsup F_\varepsilon(x_\varepsilon) \leq \lim F_\varepsilon(y_\varepsilon) = F(y)$$

$\square$

---

**出题人**: AI Assistant
**审核状态**: 待审核
**最后更新**: 2026年4月10日
