# 不可达基数

## Mathlib4 引用

```lean
import Mathlib.SetTheory.Cardinal.Inaccessible

namespace SetTheory

/-- 不可达基数的定义 -/
theorem inaccessible_cardinal_def 
    {κ : Cardinal} :
    IsInaccessible κ ↔ 
      IsRegular κ ∧ IsStrongLimit κ := by
  -- 不可达：正则且强极限
  rfl

/-- 不可达基数是ZFC的模型 -/
theorem inaccessible_yields_zfc_model 
    {κ : Cardinal} (hκ : IsInaccessible κ) :
    Model ZFC (V_κ) := by
  -- V_κ是ZFC的传递模型
  sorry

end SetTheory
```

## 数学背景

不可达基数是最小的大基数，由Felix Hausdorff在1908年引入。一个不可数正则强极限基数被称为不可达基数。它是"小"集合（可构造宇宙 $V_\omega$ 中）和"大"集合之间的第一个分界线。不可达基数的存在性不能由ZFC证明——事实上，$V_\kappa$（当 $\kappa$ 不可达时）本身就是ZFC的模型。不可达基数是大基数层级的起点，许多更强的大基数概念（如可测基数、超紧基数）都以不可达基数为基础。

## 直观解释

不可达基数是"无法从下方达到"的基数。想象你试图通过幂集运算和并集运算从 $ℵ_0$ 出发构造越来越大的基数——不可达基数就是这些运算无法触及的"墙"。正则性意味着它不能表示为更少基数的并；强极限性意味着任何更小基数的幂集仍然小于它。不可达基数如同数学宇宙中的一个"高原"，从下方无法到达，但一旦假设其存在，就能建立丰富的理论结构。

## 形式化表述

**定义**：不可数基数 $\kappa$ 是**不可达**的，若：
1. **正则**：$\text{cf}(\kappa) = \kappa$（不能表示为少于 $\kappa$ 个较小基数的并）
2. **强极限**：$\lambda < \kappa \Rightarrow 2^\lambda < \kappa$

**等价表述**：$\kappa > \aleph_0$，$\kappa$ 正则，且 $V_\kappa$ 满足ZFC幂集公理。

**强不可达**：在GCH下，不可达基数等价于正则极限基数。

**一致性**：$\text{Con}(ZFC + \exists \text{不可达}) \Rightarrow \text{Con}(ZFC)$（因为 $V_\kappa \vDash ZFC$）。

## 证明思路

1. **正则性**：证明 $V_\kappa$ 满足替换公理
2. **幂集封闭**：证明 $V_\kappa$ 对幂集封闭
3. **传递模型**：验证 $V_\kappa$ 是传递的
4. **ZFC验证**：逐一验证ZFC公理在 $V_\kappa$ 中成立
5. **相对一致性**：从存在不可达推出Con(ZFC)

## 示例

### 示例 1：第一个不可达基数

**问题**：$\aleph_\omega$ 是否不可达？

**解答**：

$\aleph_\omega = \sup_{n < \omega} \aleph_n$。

$\text{cf}(\aleph_\omega) = \omega < \aleph_\omega$，因此不正则。

$\aleph_\omega$ 不是不可达基数。

第一个不可达基数（如果存在）必须是正则极限基数，如 $\aleph_{\aleph_0}$ 在特定条件下。

### 示例 2：可构造宇宙中的不可达基数

**问题**：$L$ 中的不可达基数。

**解答**：

若 $\kappa$ 在 $V$ 中不可达，则在 $L$ 中也不可当（当且仅当）。

这是因为：
- 正则性和强极限性对 $L$ 绝对
- $L_\kappa = (V_\kappa)^L$

$0^\#$ 存在当且仅当 $L$ 中有不可达基数。

## 应用

- **Grothendieck宇宙**：范畴论的集合论基础
- **模型论**：大模型的存在性
- **大基数层级**：更高大基数的起点
- **内模型理论**：$L$ 的推广
- **反射原理**：不可达基数的反射性质

## 相关概念

- [正则基数](./regular-cardinal.md)：不可达的第一条件
- [强极限基数](./strong-limit-cardinal.md)：不可达的第二条件
- [可测基数](./measurable-cardinal.md)：更强的大基数
- [可构造宇宙](./constructible-universe.md)：不可达基数的内模型
- [Grothendieck宇宙](./grothendieck-universe.md)：不可达的应用

## 参考

### 教材

- Kanamori, A. The Higher Infinite. Springer, 2003.
- Jech, T. Set Theory. Springer, 2003. Chapter 9

### 论文

- Hausdorff, F. Grundzüge einer Theorie der geordneten Mengen. Math. Ann., 65: 435-505, 1908.
- Zermelo, E. Über Grenzzahlen und Mengenbereiche. Fund. Math., 16: 29-47, 1930.

### 在线资源

- [Inaccessible Cardinal Wikipedia](https://en.wikipedia.org/wiki/Inaccessible_cardinal)
- [nLab - Inaccessible Cardinal](https://ncatlab.org/nlab/show/inaccessible+cardinal)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
