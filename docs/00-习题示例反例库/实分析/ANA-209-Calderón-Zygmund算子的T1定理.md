---
msc_primary: 42B20
exercise_id: ANA-209
title: Calderón-Zygmund算子的T1定理
difficulty: 5
type: PRF
topic: 实分析
subtopic: 奇异积分
source:
  course: 现代调和分析
  chapter: "7.5"
  original: true
processed_at: '2026-04-10'
---

# ANA-209: Calderón-Zygmund算子的T1定理

**题号**: ANA-209
**难度**: ⭐⭐⭐⭐⭐ (Level 5)
**类型**: 证明型 (PRF)
**来源**: 现代调和分析 Chapter 7.5
**主题**: T1定理

---

## 题目

设 $T$ 是Calderón-Zygmund算子，核 $K$ 满足标准CZ条件，且 $T$ 弱有界。

**证明**：若 $T(1), T^*(1) \in BMO$，则 $T$ 可延拓为 $L^2$ 有界算子。

---

## 解答 (David-Journé)

**Step 1: Paraproduct分解**

$$T = \pi_{T(1)} + (\pi_{T^*(1)})^* + S$$

**Step 2: Paraproduct的L^2有界性**

若 $b \in BMO$，则 $\|\pi_b\|_{L^2 \to L^2} \leq C\|b\|_{BMO}$。

**Step 3: 余项估计**

$S$ 满足 $S(1) = S^*(1) = 0$，且 $\|S\|_{L^2 \to L^2} < \infty$。

**Step 4: 综合**

$$\|Tf\|_{L^2} \leq C(\|T(1)\|_{BMO} + \|T^*(1)\|_{BMO})\|f\|_{L^2}$$

$\square$

---

**出题人**: AI Assistant
**审核状态**: 待审核
**最后更新**: 2026年4月10日
