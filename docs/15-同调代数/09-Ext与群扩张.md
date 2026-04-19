---
title: Ext与群扩张
description: 深入探讨Ext^1与群扩张分类之间的精确对应，建立群上同调与群论结构的桥梁。
msc_primary:
  - 20J06
msc_secondary:
  - 18G15
  - 20E22
processed_at: '2026-04-20'
references:
  textbooks:
    - id: weibel_ha
      type: textbook
      title: An Introduction to Homological Algebra
      authors:
        - Charles A. Weibel
      publisher: Cambridge University Press
      year: 1994
      msc: 18-01
    - id: brown_cohomology
      type: textbook
      title: Cohomology of Groups
      authors:
        - Kenneth S. Brown
      publisher: Springer
      year: 1982
      msc: 20-01
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
---

# Ext与群扩张

## 引言

群扩张（group extension）是群论中的基本构造：给定群 $Q$ 和 $N$，一个 $Q$ 由 $N$ 的扩张是一个短正合列

$$1 \longrightarrow N \longrightarrow E \longrightarrow Q \longrightarrow 1.$$

两个扩张称为等价，如果存在交换图表连接它们。将 $N$ 视为 $Q$-模（通过共轭作用），Schreier理论建立了 $\operatorname{Ext}^1_{\mathbb{Z}Q}(\mathbb{Z}, N)$ 与扩张等价类之间的一一对应。

本教程深入探讨这一对应关系，并介绍Schreier因子组的具体构造。

---

## 1. 群扩张的定义

### 1.1 扩张的等价

**定义 1.1**。扩张 $1 \to N \to E \to Q \to 1$ 和 $1 \to N \to E' \to Q \to 1$ **等价**，如果存在同构 $\phi: E \to E'$ 使图表交换。

---

## 2. Schreier理论

### 2.1 因子组

选取截面 $s: Q \to E$。定义**因子组**（factor set）$f: Q \times Q \to N$：

$$s(q)s(q') = f(q, q') s(qq').$$

### 2.2 上闭链条件

**命题 2.1**。$f$ 满足

$$qf(q', q'') - f(qq', q'') + f(q, q'q'') - f(q, q') = 0,$$

即 $f$ 是2-上闭链。

### 2.3 与Ext的对应

**定理 2.2**。$\operatorname{Ext}^1_{\mathbb{Z}Q}(\mathbb{Z}, N) \cong \{\text{群扩张 } 1 \to N \to E \to Q \to 1\}/\sim$。

---

## 3. 分裂扩张

**命题 3.1**。扩张分裂（即 $E \cong N \rtimes Q$）当且仅当对应的 $\operatorname{Ext}^1$ 类为零。

---

## 4. 与已有文档的关联

- [07-左导出函子Ext](07-左导出函子Ext.md)：Ext的定义与计算。
- [17-群上同调](17-群上同调.md)：群上同调 $H^2(Q, N) \cong \operatorname{Ext}^2_{\mathbb{Z}Q}(\mathbb{Z}, N)$。

---

## 练习

1. 对 $Q = \mathbb{Z}/2\mathbb{Z}$，$N = \mathbb{Z}/3\mathbb{Z}$，分类所有扩张。
2. 证明分裂扩张的截面给出群同态。
3. 用Schreier理论构造 $D_8$ 作为 $\mathbb{Z}/2\mathbb{Z}$ 由 $\mathbb{Z}/4\mathbb{Z}$ 的扩张。

---

## 参考文献

1. K. S. Brown, *Cohomology of Groups*, Springer, 1982. (Ch. IV)
2. C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Univ. Press, 1994. (Ch. 6)
