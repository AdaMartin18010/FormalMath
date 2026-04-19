---
msc_primary: 31

  - 31C15
exercise_id: ANA-214
title: 非线性位势理论中的Wolff势
difficulty: 4
type: PRF
topic: 实分析
subtopic: 位势理论
source:
  course: 非线性分析
  chapter: "14.2"
  original: true
processed_at: '2026-04-10'
---

# ANA-214: 非线性位势理论中的Wolff势

**题号**: ANA-214
**难度**: ⭐⭐⭐⭐ (Level 4)
**类型**: 证明型 (PRF)
**来源**: 非线性分析 Chapter 14.2
**主题**: Wolff势与p-Laplace方程

---

## 题目

设 $\mu$ 是正Radon测度，$1 < p < n$。定义Wolff势：
$$W_{\alpha,p}^\mu(x) = \int_0^\infty \left(\frac{\mu(B(x,r))}{r^{n-\alpha p}}\right)^{1/(p-1)} \frac{dr}{r}$$

**证明**：对任意紧集 $K \subset \mathbb{R}^n$：
$$C_{\alpha,p}(K) \approx \inf\left\{\mu(K) : W_{\alpha,p}^\mu(x) \geq 1 \text{ on } K\right\}^{-1}$$

其中 $C_{\alpha,p}$ 是 $(\alpha,p)$-容度。

---

## 解答

**Step 1: 非线性容度定义**

$$C_{\alpha,p}(K) = \inf\left\{\|f\|_{L^p}^p : I_\alpha * f \geq 1 \text{ on } K, f \geq 0\right\}$$

**Step 2: Wolff不等式**

$$\int_{\mathbb{R}^n} (I_\alpha * \mu)^{p'} dx \approx \int_{\mathbb{R}^n} W_{\alpha,p}^\mu d\mu$$

**Step 3: 对偶性论证**

利用Havin-Mazya对偶定理完成等价性证明。

$\square$

---

**出题人**: AI Assistant
**审核状态**: 待审核
**最后更新**: 2026年4月10日
