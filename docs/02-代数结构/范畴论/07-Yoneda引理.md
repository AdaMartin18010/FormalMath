---
msc_primary: 18A05
msc_secondary:
  - 18A20
  - 18A25
processed_at: '2026-04-20'
title: Yoneda引理
---

# Yoneda引理

## 1. 引言

Yoneda引理由日本数学家Nobuo Yoneda在20世纪50年代中期提出（虽然最初并未正式发表，而是通过Grothendieck的笔记和Mac Lane的著作传播开来）。这一定理被誉为"范畴论中最深刻的定理"，它将一个对象完全刻画为它与其他所有对象之间的关系。用更精确的语言：任何范畴都可以嵌入到其上的预层范畴中，且这一嵌入是全忠实的。Yoneda引理不仅具有理论上的基础性地位，更在实际中提供了强大的证明技术——要证明两个对象同构，只需证明它们代表的函子自然同构。本文建立Yoneda引理的严格表述，探讨可表函子和Yoneda嵌入，并展示其深远影响。

## 2. Yoneda引理的陈述

### 2.1 协变形式

**定理 2.1**（Yoneda引理）。设 $\mathcal{C}$ 为局部小范畴（hom集为集合），$F: \mathcal{C}^{\mathrm{op}} \to \mathbf{Set}$ 为反变函子（即 $\mathcal{C}$ 上的预层）。则对任意 $A \in \mathcal{C}$，
$$\operatorname{Nat}(\operatorname{Hom}_{\mathcal{C}}(-, A), F) \cong F(A),$$
其中左边为从可表函子 $\operatorname{Hom}(-, A)$ 到 $F$ 的自然变换的集合。这一同构对 $A$ 自然。

*证明*。定义映射 $\Phi: \operatorname{Nat}(\operatorname{Hom}(-, A), F) \to F(A)$，$\Phi(\alpha) = \alpha_A(\operatorname{id}_A)$。

定义逆映射 $\Psi: F(A) \to \operatorname{Nat}(\operatorname{Hom}(-, A), F)$：对 $x \in F(A)$，定义自然变换 $\Psi(x)$ 在对象 $B$ 处的分量为
$$\Psi(x)_B: \operatorname{Hom}(B, A) \to F(B), \quad f \mapsto F(f)(x).$$

验证 $\Psi(x)$ 确为自然变换：对 $g: C \to B$，
$$F(g)(\Psi(x)_B(f)) = F(g)(F(f)(x)) = F(f \circ g)(x) = \Psi(x)_C(f \circ g) = \Psi(x)_C(g^*(f)).$$

验证 $\Phi$ 与 $\Psi$ 互逆：
- $\Phi(\Psi(x)) = \Psi(x)_A(\operatorname{id}_A) = F(\operatorname{id}_A)(x) = x$。
- 对自然变换 $\alpha$，$\Psi(\Phi(\alpha))_B(f) = F(f)(\alpha_A(\operatorname{id}_A)) = \alpha_B(f \circ \operatorname{id}_A) = \alpha_B(f)$（由自然性）。$\square$

### 2.2 反变形式

对协变函子 $G: \mathcal{C} \to \mathbf{Set}$，
$$\operatorname{Nat}(\operatorname{Hom}_{\mathcal{C}}(A, -), G) \cong G(A).$$

## 3. 推论

### 3.1 可表函子的自然同构

**推论 3.1**。$\operatorname{Hom}(-, A) \cong \operatorname{Hom}(-, B)$（自然同构）当且仅当 $A \cong B$。

*证明*。由Yoneda，$\operatorname{Nat}(\operatorname{Hom}(-, A), \operatorname{Hom}(-, B)) \cong \operatorname{Hom}(A, B)$。自然同构对应可逆元。$\square$

### 3.2 Yoneda嵌入

**定义 3.2**。**Yoneda嵌入**为函子 $y: \mathcal{C} \to \mathbf{Set}^{\mathcal{C}^{\mathrm{op}}}$，$y(A) = \operatorname{Hom}(-, A)$，在态射上为后复合。

**推论 3.3**。Yoneda嵌入 $y$ 是全忠实的（fully faithful）。

*证明*。$\operatorname{Hom}_{\mathcal{C}}(A, B) \xrightarrow{y} \operatorname{Nat}(y(A), y(B)) \cong \operatorname{Hom}(A, B)$ 为双射。$\square$

**注记**。Yoneda嵌入说明任何范畴都可视为其预层范畴的子范畴。预层范畴具有丰富的良好性质（完备、余完备、Cartesian闭），这为通过"广义对象"（预层）研究原范畴提供了可能。

## 4. 可表函子

**定义 4.1**。函子 $F: \mathcal{C}^{\mathrm{op}} \to \mathbf{Set}$ 称为**可表的**（representable），若存在 $A \in \mathcal{C}$ 使 $F \cong \operatorname{Hom}(-, A)$。此时 $A$ 称为 $F$ 的**表示对象**（representing object）。

**例 4.2**。遗忘函子 $U: \mathbf{Grp} \to \mathbf{Set}$ 由 $\mathbb{Z}$ 表示：$U(G) \cong \operatorname{Hom}_{\mathbf{Grp}}(\mathbb{Z}, G)$（$g \mapsto (1 \mapsto g)$）。

**例 4.3**。张量积函子 $M \otimes_R -: R\text{-}\mathbf{Mod} \to \mathbf{Ab}$ 有右伴随 $\operatorname{Hom}_{\mathbb{Z}}(M, -)$，但其本身通常不可表。

**例 4.4**。层的茎函子 $\mathbf{Sh}(X) \to \mathbf{Set}$，$\mathcal{F} \mapsto \mathcal{F}_x$ 由摩天大楼层 $i_{x*}S$ 表示。

## 5. Yoneda原理在证明中的应用

**原理 5.1**（Yoneda原理）。要证 $A \cong B$，可证对任意 $X$，$\operatorname{Hom}(X, A) \cong \operatorname{Hom}(X, B)$（自然地）；或对任意 $Y$，$\operatorname{Hom}(A, Y) \cong \operatorname{Hom}(B, Y)$（自然地）。

**例 5.2**（积的结合律）。$(A \times B) \times C \cong A \times (B \times C)$。对任意 $X$，
$$\operatorname{Hom}(X, (A \times B) \times C) \cong \operatorname{Hom}(X, A \times B) \times \operatorname{Hom}(X, C) \cong \operatorname{Hom}(X, A) \times \operatorname{Hom}(X, B) \times \operatorname{Hom}(X, C),$$
同理右边亦然。由Yoneda，两者同构。

## 6. 与项目其他部分的关联

Yoneda引理是范畴论的基石。在伴随函子理论（见[04-伴随函子](04-伴随函子.md)）中，伴随对的单位与余单位可通过Yoneda构造。在层论（见[06-层作为范畴](06-层作为范畴.md)）中，层的可表性与茎的刻画直接相关。在代数几何（见[08-范畴论在代数几何中的应用](08-范畴论在代数几何中的应用.md)）中，可表函子是模空间理论的核心——模函子可表当且仅当相应的模空间存在。在代数拓扑（见`docs/12-代数拓扑/`）中，Brown可表性定理断言满足Mayer-Vietoris和楔形公理的广义上同调论可由谱表示。

## 7. 参考文献

1. N. Yoneda, "On the homology theory of modules", *J. Fac. Sci. Univ. Tokyo* 7 (1954), 193–227.
2. S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed., Springer, 1998.
3. S. Awodey, *Category Theory*, 2nd ed., Oxford University Press, 2010.
4. E. Riehl, *Category Theory in Context*, Dover, 2016.
5. 贺伟，《范畴论》，科学出版社，2006。
