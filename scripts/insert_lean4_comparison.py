import re

# Read the file
with open('docs/00-银层核心课程/MIT-18.100A-实分析/比较判别法.md', 'r', encoding='utf-8') as f:
    content = f.read()

# Replacement 1: after 定义 1.2
old1 = '**重要性质**: 非负项级数的部分和序列 $(S_N)$ 是**单调递增**的，因为 $S_{N+1} = S_N + a_{N+1} \\geq S_N$。\n\n---\n\n### 定义 1.3（有界序列与单调序列）'

new1 = '''**重要性质**: 非负项级数的部分和序列 $(S_N)$ 是**单调递增**的，因为 $S_{N+1} = S_N + a_{N+1} \\geq S_N$。

> **双语对照**:
>
> ```lean4
> import Mathlib
>
> -- 非负项级数：序列的每一项均非负
> def NonNegativeSeries (a : ℕ → ℝ) : Prop :=
>   ∀ n, 0 ≤ a n
>
> -- 部分和序列的定义
> def partialSum (a : ℕ → ℝ) (N : ℕ) : ℝ :=
>   ∑ n in Finset.range N, a n
>
> -- 非负项级数的部分和单调递增
> theorem partialSum_monotone {a : ℕ → ℝ} (ha : NonNegativeSeries a) :
>     Monotone (partialSum a) := by
>   /- 证明思路：对任意 m ≤ n，部分和之差为非负项之和 ≥ 0 -/
>   sorry
> ```

---

### 定义 1.3（有界序列与单调序列）'''

if old1 in content:
    content = content.replace(old1, new1)
    print('Replacement 1 done')
else:
    print('Replacement 1 FAILED')

# Write back
with open('docs/00-银层核心课程/MIT-18.100A-实分析/比较判别法.md', 'w', encoding='utf-8') as f:
    f.write(content)

print('File written')
