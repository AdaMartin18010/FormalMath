# 极限与余极限

## Mathlib4 引用

```lean
import Mathlib.CategoryTheory.Limits.Limits

namespace CategoryTheory.Limits

/-- 极限的泛性质 -/
theorem limit_universal_property
    {C J : Type*} [Category C] [Category J]
    (F : J ⥤ C) [HasLimit F] :
    ∀ (X : C) (cone : Cone F),
      (X ⟶ limit F) ≃ {f : X ⟶ cone.pt //
        ∀ (j : J), f ≫ cone.π.app j = limit.π F j} := by
  -- 极限作为终对象的性质
  intro X cone
  apply limit.homIso

/-- 余极限的泛性质 -/
theorem colimit_universal_property
    {C J : Type*} [Category C] [Category J]
    (F : J ⥤ C) [HasColimit F] :
    ∀ (X : C) (cocone : Cocone F),
      (colimit F ⟶ X) ≃ {f : cocone.pt ⟶ X //
        ∀ (j : J), cocone.ι.app j ≫ f = colimit.ι F j} := by
  -- 余极限作为始对象的性质
  intro X cocone
  apply colimit.homIso

end CategoryTheory.Limits
```

## 数学背景

极限和余极限是范畴论中统一大量数学构造的普遍概念。极限推广了积、等化子、拉回、核等构造；余极限推广了和、余等化子、推出、余核等。这些概念最早由Daniel Kan在1958年系统引入，现已成为现代数学的基础语言。范畴论中几乎所有重要构造都可以用极限或余极限描述。

## 直观解释

极限是从"外部"观察一个图表的整体行为——它捕获了图表中所有对象和箭头的"一致"信息。想象一个蜘蛛网：极限是网中心的点，所有丝线（箭头）都指向它。余极限则是从"内部"构建——将所有对象"粘合"在一起。如同拼图：极限看拼图的最终图案，余极限则是实际将碎片拼合。两者通过对偶性联系：一个范畴中的极限是相反范畴中的余极限。

## 形式化表述

设 $F: \mathcal{J} \to \mathcal{C}$ 是图表（diagram）。

**锥（Cone）**：对象 $X \in \mathcal{C}$ 配备一族态射 $\{X \to F(j)\}_{j \in \mathcal{J}}$，使得所有三角形交换。

**极限**：锥 $(\lim F, \pi)$ 使得对任意锥 $(X, \psi)$，存在唯一 $f: X \to \lim F$ 使得 $\pi_j \circ f = \psi_j$。

**余锥（Cocone）**和**余极限**：对偶定义。

**常见特例**：

- 终对象 = 空图的极限
- 积 = 离散图的极限
- 等化子 = 平行箭头图的极限
- 拉回 =  span 图的极限

## 证明思路

1. **构造候选对象**：找出可能作为极限的对象
2. **构造锥结构**：定义投影态射 $\pi_j$
3. **验证泛性质**：证明唯一映射的存在性
4. **证明唯一性**：在同构意义下极限唯一

## 示例

### 示例 1：集合的积

**问题**：证明集合范畴中，积就是笛卡尔积。

**解答**：

设 $\{X_i\}_{i \in I}$ 是集合族。极限是 $\prod_{i \in I} X_i$，投影为 $\pi_j((x_i)) = x_j$。

验证泛性质：给定 $f_i: Y \to X_i$，唯一映射 $f: Y \to \prod X_i$ 是 $f(y) = (f_i(y))$。

### 示例 2：群的自由积

**问题**：描述群范畴中的余极限。

**解答**：

群族的余积（和）是自由积 $*_{i \in I} G_i$ ——由所有 $G_i$ 生成，但除去群之间所有关系的群。

包含映射 $\iota_j: G_j \to * G_i$ 将元素映到对应的字。

## 应用

- **代数拓扑**：同伦极限与同伦余极限
- **代数几何**：概形的纤维积
- **集合论**：交集和并集作为极限/余极限
- **计算机科学**：数据类型的初始和终代数
- **逻辑**：逻辑连接词作为（余）极限

## 相关概念

- [伴随函子](./adjoint-functor.md)：对角函子的（余）极限伴随
- [完备范畴](./complete-category.md)：所有小极限存在的范畴
- [连续函子](./continuous-functor.md)：保持极限的函子
- [Kan扩张](./kan-extension.md)：极限的推广
- [导出极限](./derived-limit.md)：同调代数中的应用

## 参考

### 教材

- Mac Lane, S. Categories for the Working Mathematician. Springer, 1998. Chapter 3
- Borceux, F. Handbook of Categorical Algebra. Cambridge, 1994. Volume 1

### 论文

- Kan, D.M. Adjoint functors. Trans. Amer. Math. Soc., 87: 294-329, 1958.

### 在线资源

- [Limit (Category Theory) Wikipedia](https://en.wikipedia.org/wiki/Limit_(category_theory))
- [nLab - Limit](https://ncatlab.org/nlab/show/limit)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
