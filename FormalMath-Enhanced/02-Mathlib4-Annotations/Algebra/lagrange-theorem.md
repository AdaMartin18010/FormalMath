---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 拉格朗日定理 (Lagrange's Theorem)
---
# 拉格朗日定理 (Lagrange's Theorem)

## Mathlib4 引用

```lean
import Mathlib.GroupTheory.Coset
import Mathlib.GroupTheory.Subgroup.Basic

namespace Subgroup

variable {G : Type*} [Group G] (H : Subgroup G)

/-- 拉格朗日定理：有限群中子群的阶整除群的阶 -/
theorem card_subgroup_dvd_card [Fintype G] [Fintype H] :
    Fintype.card H ∣ Fintype.card G :=
  ⟨H.index, by rw [mul_comm, ← H.index_mul_card]; rfl⟩

end Subgroup
```

## 数学背景

拉格朗日定理是有限群论的基石之一，由约瑟夫·拉格朗日（Joseph-Louis Lagrange）于1771年首次证明。该定理建立了群的阶与其子群阶之间的基本关系，为后续群论发展奠定了重要基础。这一定理不仅具有理论意义，还为数论、密码学和编码理论提供了重要工具。

## 直观解释

拉格朗日定理告诉我们：**有限群的"大小"总是其子群"大小"的倍数**。想象一个由多个相同大小的箱子组成的仓库，子群就像是其中一个箱子，而整个群是所有箱子的集合。定理说明这些箱子必须能完美填满整个仓库，没有剩余空间。

更精确地说，如果将群 $G$ 看作集合，子群 $H$ 将这个集合划分成若干个"陪集"（cosets），每个陪集的大小与 $H$ 相同。这些陪集构成了群的一个划分。

## 形式化表述

设 $G$ 是有限群，$H$ 是 $G$ 的子群，则：

$$|G| = [G:H] \cdot |H|$$

其中：

- $|G|$ 表示群 $G$ 的阶（元素个数）
- $|H|$ 表示子群 $H$ 的阶
- $[G:H]$ 表示 $H$ 在 $G$ 中的指数（左陪集的个数）

## 证明思路

1. **陪集划分**：证明 $H$ 的左陪集构成 $G$ 的一个划分
2. **等势性**：证明每个左陪集与 $H$ 之间存在双射，因此大小相同
3. **计数论证**：计算陪集个数与每个陪集大小的乘积等于群的阶

核心洞察在于陪集将群均匀分割，这是群作用和对称性的体现。

## 示例

### 示例 1：对称群 $S_3$

考虑 3 个元素的对称群 $S_3$，其阶为 $|S_3| = 6$。

设 $H = \{e, (12)\}$ 是由对换 $(12)$ 生成的子群，则 $|H| = 2$。

根据拉格朗日定理，$|H| = 2$ 整除 $|S_3| = 6$，且指数 $[S_3:H] = 3$。

验证：左陪集为 $H$, $(13)H$, $(23)H$，共 3 个，每个含 2 个元素。

### 示例 2：循环群 $\mathbb{Z}_{12}$

考虑模 12 的加法群 $\mathbb{Z}_{12}$，其阶为 12。

设 $H = \langle 4 \rangle = \{0, 4, 8\}$，则 $|H| = 3$。

验证：$3$ 整除 $12$，指数 $[\mathbb{Z}_{12}:H] = 4$。

### 示例 3：应用费马小定理

设 $p$ 是素数，$a$ 是不被 $p$ 整除的整数。

乘法群 $\mathbb{Z}_p^\times$ 的阶为 $p-1$。由 $a$ 生成的子群 $\langle a \rangle$ 的阶整除 $p-1$。

因此 $a^{p-1} \equiv 1 \pmod{p}$，即费马小定理。

## 应用

- **素数阶群**：素数阶群必为循环群
- **费马小定理**：数论中的重要工具
- **RSA 加密**：公钥密码学的数学基础
- **纠错码**：编码理论中的群结构分析

## 相关概念

- [子群 (Subgroup)](./subgroup.md)：群的子集构成的群
- [陪集 (Coset)](./coset.md)：子群的平移副本
- [指数 (Index)](./index.md)：陪集的个数
- [正规子群 (Normal Subgroup)](./normal-subgroup.md)：左右陪集相等的子群
- [商群 (Quotient Group)](./quotient-group.md)：由正规子群构造的新群

## 参考

### 教材

- [M. Artin. Algebra. Pearson, 2nd edition, 2010. Chapter 2]
- [Dummit & Foote. Abstract Algebra. Wiley, 3rd edition, 2004. Section 3.2]

### 历史文献

- [Lagrange. Réflexions sur la résolution algébrique des équations. 1771]

### 在线资源

- [Mathlib4 文档 - Subgroup](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Subgroup/Basic.html)
- [Groupprops - Lagrange's theorem](https://groupprops.subwiki.org/wiki/Lagrange%27s_theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
