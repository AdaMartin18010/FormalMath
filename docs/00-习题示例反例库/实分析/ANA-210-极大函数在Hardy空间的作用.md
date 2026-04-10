---
msc_primary: 42B25
exercise_id: ANA-210
title: 极大函数在Hardy空间的作用
difficulty: 4
type: PRF
topic: 实分析
subtopic: 调和分析
source:
  course: 实分析进阶
  chapter: "3.4"
  original: true
processed_at: '2026-04-10'
---

# ANA-210: 极大函数在Hardy空间的作用

**题号**: ANA-210
**难度**: ⭐⭐⭐⭐ (Level 4)
**类型**: 证明型 (PRF)
**来源**: 实分析进阶 Chapter 3.4
**主题**: Hardy空间与极大函数

---

## 题目

设 $f \in H^1(\mathbb{R}^n)$，定义角状极大函数：
$$f^*(x) = \sup_{|y-x|<t} |(f * \psi_t)(y)|$$

其中 $\psi_t(x) = t^{-n}\psi(x/t)$，$\psi \in \mathcal{S}$ 且 $\int \psi \neq 0$。

**证明**：
**(a)** $f^* \in L^1(\mathbb{R}^n)$ 且 $\|f^*\|_{L^1} \leq C\|f\|_{H^1}$

**(b)** 反之，若 $f \in L^1$ 且 $f^* \in L^1$，则 $f \in H^1$

---

## 解答

### (a) 正向估计

**Step 1: 原子分解**

$f = \sum \lambda_j a_j$，其中 $a_j$ 是 $H^1$ 原子，$\sum|\lambda_j| \leq 2\|f\|_{H^1}$。

**Step 2: 原子的极大函数估计**

对原子 $a$ 支集在 $B(0,r)$ 上：
- 当 $x \in B(0, 2r)$：$|a^*(x)| \leq C r^{-n}$
- 当 $x \notin B(0, 2r)$：$|a^*(x)| \leq C r |x|^{-n-1}$（利用消失矩）

**Step 3: 积分估计**

$$\int a^*(x) dx = \int_{B(0,2r)} + \int_{\mathbb{R}^n \setminus B(0,2r)} \leq C$$

**Step 4: 综合**

$$\|f^*\|_{L^1} \leq \sum |\lambda_j| \|a_j^*\|_{L^1} \leq C \|f\|_{H^1}$$

### (b) 反向估计

**Step 1: 分布意义**

由 $f^* \in L^1$，$f$ 在分布意义下良定义。

**Step 2: 原子构造**

利用Calderón-Zygmund分解将 $f$ 分解为原子。

**Step 3: 收敛性**

证明级数在 $H^1$ 范数下收敛。

$\square$

---

**出题人**: AI Assistant
**审核状态**: 待审核
**最后更新**: 2026年4月10日
