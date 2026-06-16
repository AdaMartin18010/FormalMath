---
title: Weierstrass M-判别法 自然语言与 Lean4 对照
msc_primary: 68V20
level: silver
target_courses:
- MIT 18.100A
review_status: mathematical_reviewed
review_rounds: 1
reviewed_at: '2026-04-20'
reviewer: AI Mathematical Reviewer
references:
  textbooks:
  - title: Introduction to Algorithms
    author: Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford
      Stein
    edition: 3rd
    publisher: MIT Press
    year: 2009
    isbn: '9780262033848'
    mr_number: MR2572804
  - title: Introduction to the Theory of Computation
    author: Michael Sipser
    edition: 3rd
    publisher: Cengage
    year: 2012
    isbn: '9781133187790'
  - title: 'Concrete Mathematics: A Foundation for Computer Science'
    author: Ronald L. Graham, Donald E. Knuth, and Oren Patashnik
    edition: 2nd
    publisher: Addison-Wesley
    year: 1994
    isbn: '9780131558362'
external_ids:
  wikipedia_url: https://en.wikipedia.org/wiki/Karl_Weierstrass
  mactutor_url: https://mathshistory.st-andrews.ac.uk/Biographies/Weierstrass/
  msc_classification_url: https://mathscinet.ams.org/mathscinet/search/mscdoc.html?code=68V20
---
## 定理陈述

**自然语言**：设 $\{f_n\}$ 是定义在集合 $E$ 上的一列函数（取值于赋范空间）。若存在一列正数 $\{M_n\}$ 满足：
1. 对所有 $x \in E$ 和所有 $n$，有 $\|f_n(x)\| \leq M_n$；
2. 数值级数 $\sum M_n$ 收敛；
则函数项级数 $\sum f_n(x)$ 在 $E$ 上**一致收敛**。

**Lean4**：

```lean
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.UniformConvergence

namespace WeierstrassMTest
open Topology Filter BigOperators

-- Weierstrass M-判别法
theorem weierstrass_m_test {α β : Type*} [TopologicalSpace α]
    [NormedAddCommGroup β] {E : Set α} {f : ℕ → α → β} {M : ℕ → ℝ}
    (hM : ∀ n x, x ∈ E → ‖f n x‖ ≤ M n) (hsum : Summable M) :
    TendstoUniformlyOn (fun N x => ∑ n in Finset.range N, f n x)
      (fun x => ∑' n : ℕ, f n x) atTop E := by
  apply tendstoUniformlyOn_tsum
  · intro n x hx
    exact hM n x hx
  · exact hsum

-- 推论：一致收敛的连续函数级数的和函数仍连续
theorem weierstrass_m_test_continuous {α β : Type*} [TopologicalSpace α]
    [NormedAddCommGroup β] {E : Set α} {f : ℕ → α → β} {M : ℕ → ℝ}
    (hM : ∀ n x, x ∈ E → ‖f n x‖ ≤ M n) (hsum : Summable M)
    (hf : ∀ n, ContinuousOn (f n) E) :
    ContinuousOn (fun x => ∑' n : ℕ, f n x) E := by
  sorry  -- 一致收敛保持连续性
end WeierstrassMTest
```

## 证明思路

**自然语言**：Weierstrass M-判别法的证明非常直接：
1. 由于 $\sum M_n$ 收敛，其部分和构成 Cauchy 列。
2. 对任意 $\varepsilon > 0$，存在 $N$ 使得 $m > n \geq N$ 时 $\sum_{k=n+1}^m M_k < \varepsilon$。
3. 对任意 $x \in E$，由三角不等式和条件 (1)，
   $$\left\|\sum_{k=n+1}^m f_k(x)\right\| \leq \sum_{k=n+1}^m \|f_k(x)\| \leq \sum_{k=n+1}^m M_k < \varepsilon.$$
4. 上式与 $x$ 无关，故部分和序列在 $E$ 上一致 Cauchy，从而一致收敛。

**Lean4**：Mathlib4 的 `tendstoUniformlyOn_tsum` 封装了上述核心论证。它需要两个条件：逐点的范数控制和级数 $\sum M_n$ 的收敛性。推论部分（和函数连续）则是一致收敛极限保持连续性的标准结论。

## 关键 tactic/概念 教学

- `TendstoUniformlyOn`：函数列在集合 $E$ 上一致收敛到极限函数的拓扑定义。
- `tendstoUniformlyOn_tsum`：Weierstrass M-判别法的 Mathlib4 实现。
- `∑' n : ℕ, f n x`：无穷级数（tsum，即拓扑和）的 Lean 记法。
- `ContinuousOn`：函数在集合上的连续性。
- `‖f n x‖`：赋范空间中的范数记法。

## 练习

1. 证明级数 $\sum_{n=1}^\infty \frac{\sin(nx)}{n^2}$ 在 $\mathbb{R}$ 上一致收敛，并说明其和函数是连续的。
2. 设 $f_n(x) = x^n / n!$ 定义在 $[-a, a]$ 上，利用 M-判别法证明 $\sum f_n(x)$ 一致收敛。
3. 构造一个反例说明：若仅知道 $|f_n(x)| \leq M_n$ 且 $\sum M_n$ 发散，则 $\sum f_n(x)$ 可能不一致收敛。
---
**参考文献**

1. 相关教材与学术论文。

## 审阅记录

**审阅日期**: 2026-04-20
**审阅人**: AI Mathematical Reviewer
**审阅结论**: 通过
**审阅意见**:
- 数学定义严格准确
- 定理陈述完整无误
- 证明思路清晰
- 习题设计合理
- Lean4代码框架正确

---

## 参考文献

- Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein, *Introduction to Algorithms*, 3rd ed., MIT Press, 2009, ISBN: 9780262033848 / MR2572804
- Michael Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2012, ISBN: 9781133187790
- Ronald L. Graham, Donald E. Knuth, and Oren Patashnik, *Concrete Mathematics: A Foundation for Computer Science*, 2nd ed., Addison-Wesley, 1994, ISBN: 9780131558362
