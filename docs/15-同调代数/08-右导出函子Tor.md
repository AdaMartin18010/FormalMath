---
title: 右导出函子Tor
description: 系统介绍Tor_n函子的定义、基本性质、长正合列，以及与平坦模和张量积正合性的深刻联系。
msc_primary:
  - 18G15
msc_secondary:
  - 13D07
  - 16E30
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
    - id: rotman_ha
      type: textbook
      title: An Introduction to Homological Algebra
      authors:
        - Joseph J. Rotman
      publisher: Springer
      year: 2009
      msc: 18-01
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
---

# 右导出函子Tor

## 引言

Tor函子是张量积函子 $-\otimes_R N$ 的左导出函子。张量积函子是右正合的但不一定是左正合的，Tor函子精确地测量了这一"失败"。$\operatorname{Tor}_n^R(M, N)$ 可以通过 $M$ 或 $N$ 的投射分解来计算，具有自然的对称性。

Tor函子在交换代数中具有核心地位：$\operatorname{Tor}_1$ 与挠子模（torsion submodule）密切相关，平坦模的判据直接由Tor的消失给出。在代数几何中，Tor也出现在相交理论和层上同调中。

本教程介绍Tor函子的定义、基本性质、长正合列以及与平坦模的关系。

---

## 1. Tor的定义

### 1.1 通过投射分解

**定义 1.1**。设 $M, N$ 为 $R$-模，$P_\bullet \to M$ 为投射分解。定义

$$\operatorname{Tor}_n^R(M, N) := H_n(P_\bullet \otimes_R N).$$

### 1.2 对称性

**定理 1.2**。$\operatorname{Tor}_n^R(M, N) \cong \operatorname{Tor}_n^R(N, M)$（自然同构）。

---

## 2. 基本性质

### 2.1 低维解释

- $\operatorname{Tor}_0^R(M, N) = M \otimes_R N$。
- $\operatorname{Tor}_1^R(M, N)$ 测量张量积对单射的破坏。

### 2.2 长正合列

**定理 2.1**。对 $0 \to M' \to M \to M'' \to 0$，有长正合列

$$\cdots \to \operatorname{Tor}_1(M'', N) \to M' \otimes N \to M \otimes N \to M'' \otimes N \to 0.$$

---

## 3. 与平坦模的关系

**定理 3.1**。$N$ 平坦当且仅当 $\operatorname{Tor}_n^R(M, N) = 0$ 对所有 $n > 0$ 和 $M$。

---

## 4. 重要例子

**例 4.1**。$\operatorname{Tor}_1^{\mathbb{Z}}(\mathbb{Z}/m, \mathbb{Z}/n) \cong \mathbb{Z}/\gcd(m,n)$。

---

## 5. 与已有文档的关联

- [11-平坦模](11-平坦模.md)：Tor的消失判据。
- [05-投射分解](05-投射分解.md)：Tor由投射分解计算。

---

## 练习

1. 证明 $\operatorname{Tor}_n^R$ 的对称性。
2. 计算 $\operatorname{Tor}_1^{k[x]}(k, k)$（$k[x]$ 在 $(x)$ 处的局部化情形）。
3. 证明 $M$ 平坦当且仅当 $\operatorname{Tor}_1^R(M, N) = 0$ 对所有 $N$。

---

## 参考文献

1. C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Univ. Press, 1994. (Ch. 3)
2. J. J. Rotman, *An Introduction to Homological Algebra*, Springer, 2009. (Ch. 7)
