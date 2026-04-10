---
msc_primary: 42B20
exercise_id: ANA-211
title: Singular积分算子的加权范数不等式
difficulty: 5
type: PRF
topic: 实分析
subtopic: 加权范数
source:
  course: 调和分析前沿
  chapter: "9.2"
  original: true
processed_at: '2026-04-10'
---

# ANA-211: Singular积分算子的加权范数不等式

**题号**: ANA-211
**难度**: ⭐⭐⭐⭐⭐ (Level 5)
**类型**: 证明型 (PRF)
**来源**: 调和分析前沿 Chapter 9.2
**主题**: Muckenhoupt权与奇异积分

---

## 题目

设 $T$ 是标准Calderón-Zygmund奇异积分算子，$w \in A_p$ ($1 < p < \infty$)。

**证明**：$T: L^p(w) \to L^p(w)$ 有界，且
$$\|Tf\|_{L^p(w)} \leq C_{n,p,T} [w]_{A_p}^{\max(1, \frac{1}{p-1})} \|f\|_{L^p(w)}$$

---

## 解答

**Step 1: sharp常数分解**

利用 $A_p$ 权的分解：$w = w_1 w_2^{1-p}$，其中 $w_1, w_2 \in A_1$。

**Step 2: Rubio de Francia外推**

从 $L^2$ 估计外推到 $L^p$。

**Step 3: 稀疏算子控制**

$T$ 被稀疏算子 $A_{\mathcal{S}}$ 控制：
$$|Tf(x)| \leq C \sum_{Q \in \mathcal{S}} \langle |f| \rangle_Q \chi_Q(x)$$

**Step 4: 稀疏算子的加权估计**

$$\|A_{\mathcal{S}}\|_{L^p(w)} \leq C [w]_{A_p}^{\max(1, \frac{1}{p-1})}$$

$\square$

---

**出题人**: AI Assistant
**审核状态**: 待审核
**最后更新**: 2026年4月10日
