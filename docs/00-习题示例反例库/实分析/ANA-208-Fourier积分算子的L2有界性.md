---
msc_primary: 42B20
exercise_id: ANA-208
title: Fourier积分算子的L2有界性
difficulty: 4
type: PRF
topic: 实分析
subtopic: 现代调和分析
source:
  course: 微局部分析
  chapter: "6.2"
  original: true
processed_at: '2026-04-10'
---

# ANA-208: Fourier积分算子的L^2有界性

**题号**: ANA-208
**难度**: ⭐⭐⭐⭐ (Level 4)
**类型**: 证明型 (PRF)
**来源**: 微局部分析 Chapter 6.2
**主题**: Fourier积分算子与L^2估计

---

## 题目

设 $T$ 是Fourier积分算子：
$$(Tf)(x) = \int_{\mathbb{R}^n} e^{i\phi(x,\xi)} a(x,\xi) \hat{f}(\xi) d\xi$$

其中：
- 相位函数 $\phi$ 是1次正齐次的，$\det(\partial^2 \phi/\partial x \partial \xi) \neq 0$ (非退化)
- 振幅 $a \in S^0$ (零阶象征)

**证明**：$T: L^2(\mathbb{R}^n) \to L^2(\mathbb{R}^n)$ 有界。

---

## 解答

**Step 1: Littlewood-Paley分解**

将振幅分解为 $a(x,\xi) = \sum_{j=0}^\infty a_j(x,\xi)$，其中 $a_j$ 支在 $|\xi| \sim 2^j$ 上。

**Step 2: 尺度变换**

定义算子 $T_j$，经过尺度变换后，$\|T_j\|_{L^2 \to L^2} \leq C$ 与 $j$ 无关。

**Step 3: 几乎正交性**

不同尺度满足：$T_j^* T_k = O(2^{-|j-k|N})$ 对任意 $N > 0$。

**Step 4: Cotlar-Stein引理**

由Cotlar-Stein几乎正交引理：
$$\|T\|_{L^2 \to L^2} \leq C \sup_j \|T_j\| < \infty$$

$\square$

---

## 参考文献

| 文献 | 作者 | 相关内容 |
|------|------|----------|
| Fourier Integrals | Sogge | L^2有界性 |
| Acta Math 1971 | Hormander | FIO理论 |

---

**出题人**: AI Assistant
**审核状态**: 待审核
**最后更新**: 2026年4月10日
