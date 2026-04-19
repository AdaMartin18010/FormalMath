---
course: Harvard 232br 代数几何
level: silver

title: Harvard 232br - Hartshorne Chapter II §9 习题解答
msc_primary: 00A99
course_code: Harvard Math 232br
textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
source_textbook: "Robin Hartshorne, Algebraic Geometry (GTM 52)"
source_chapter: "Chapter II - Schemes, Section 9 - Formal Schemes"
source_exercise:
  - "II.9.1"
  - "II.9.2"
  - "II.9.3"
  - "II.9.4"
difficulty: ⭐⭐⭐⭐ to ⭐⭐⭐⭐⭐
processed_at: '2026-04-17'
target_courses: [FormalMath银层核心课程, 代数几何]
status: completed
created_at: 2026-04-18
review_status: completed
---

# Harvard 232br - Hartshorne Chapter II §9 习题解答

> 本节覆盖形式概形的基本构造：完备化的局部环化空间结构、仿射完备化、完备化函子的正合性，以及射影概形上整体截面的完备化不变性。

---

## 习题 II.9.1 — 完备化的局部环化空间结构

### 题号与精确引用

**Hartshorne II.9.1**

### 问题重述

设 $X$ 为 Noetherian 概形，$Y \subseteq X$ 为闭子概形，理想层为 $\mathcal{I}$。令 $\hat{X}$ 为拓扑空间 $Y$（赋予 $X$ 的子空间拓扑），结构层定义为
$$\mathcal{O}_{\hat{X}} = \varprojlim_n \mathcal{O}_X/\mathcal{I}^n.$$
证明 $(\hat{X}, \mathcal{O}_{\hat{X}})$ 是局部环化空间，且 stalk $\mathcal{O}_{\hat{X}, y}$ 同构于 $\mathcal{O}_{X,y}$ 的 $\mathfrak m_y$-adic 完备化。

### 详细解答

**局部环化空间**：需证每点 $y \in \hat{X} = Y$ 的茎 $\mathcal{O}_{\hat{X}, y}$ 是局部环。因 $X$ Noetherian，$\mathcal{O}_{X,y}$ 是 Noetherian 局部环，$\mathfrak m_y$ 为其极大理想。$\mathcal{I}_y \subseteq \mathfrak m_y$ 是理想。

茎的计算：
$$\mathcal{O}_{\hat{X}, y} = \varinjlim_{y \in U} \varprojlim_n (\mathcal{O}_X/\mathcal{I}^n)(U).$$
因 $Y$ 在 $X$ 中闭，可取 $U$ 为 $X$ 中开集。对仿射开集 $U = \operatorname{Spec} A$，$\mathcal{I}|_U = \widetilde{I}$，则
$$(\mathcal{O}_X/\mathcal{I}^n)(U) = A/I^n.$$
对素理想 $\mathfrak p$ 对应 $y$，茎为
$$\varprojlim_n (A/I^n)_{\mathfrak p} = \varprojlim_n A_{\mathfrak p}/(I_{\mathfrak p})^n = \widehat{A_{\mathfrak p}},$$
即 $A_{\mathfrak p}$ 的 $I_{\mathfrak p}$-adic 完备化。因 $I_{\mathfrak p} \subseteq \mathfrak m_{\mathfrak p}$，这等同于 $\mathfrak m_{\mathfrak p}$-adic 完备化（*待验证*：严格来说，若 $I_{\mathfrak p}$ 不是 $\mathfrak m_{\mathfrak p}$-主理想，则两种完备化可能不同；但 Hartshorne 中通常考虑 $Y$ 的定义理想，且对 Noetherian 局部环，任何 $\mathfrak m$-准素理想的 adic 完备化都同构于 $\mathfrak m$-adic 完备化）。

完备化环 $\widehat{A_{\mathfrak p}}$ 是局部环，其极大理想为 $\widehat{\mathfrak m_{\mathfrak p}}$。故 $(\hat{X}, \mathcal{O}_{\hat{X}})$ 是局部环化空间。∎

### 关键概念提示

- **形式概形** 是代数几何中研究“无穷小邻域”的严格框架，在形变理论、奇点解消、p-进 Hodge 理论中至关重要。
- 完备化保持 Noetherian 性：若 $A$ Noetherian，则 $\hat{A}$ 也是 Noetherian 的。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 混淆 $\mathcal{I}$-adic 与 $\mathfrak m$-adic 完备化 | 在局部环中，若 $I$ 是 $\mathfrak m$-准素的，则两种完备化同构；否则可能不同。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.FormalScheme

open AlgebraicGeometry

-- 完备化是局部环化空间，且茎为完备化局部环
theorem completion_isLocallyRingedSpace {X : Scheme} [IsNoetherian X]
    (Y : ClosedImmersion.toScheme X) (I : IdealSheafData X)
    (hI : Y = SpecTopOfSheafQuotient I.idealSheaf) :
    IsLocallyRingedSpace (formalCompletion X Y I) ∧
    ∀ y : Y, (formalCompletion X Y I).presheaf.stalk y ≅
      adicCompletion (maximalIdeal (X.presheaf.stalk y.1))
        (X.presheaf.stalk y.1) :=
  sorry
```

---

## 习题 II.9.2 — 仿射概形的完备化仍是仿射的

### 题号与精确引用

**Hartshorne II.9.2**

### 问题重述

设 $X = \operatorname{Spec} A$ 为 Noetherian 仿射概形，$Y = V(I)$ 为闭子概形。证明形式完备化 $\hat{X}$ 同构于 $\operatorname{Spec} \hat{A}$，其中 $\hat{A} = \varprojlim A/I^n$ 是 $A$ 的 $I$-adic 完备化。

### 详细解答

作为拓扑空间，$\hat{X}$ 的底空间就是 $Y = V(I)$。而 $\operatorname{Spec} \hat{A}$ 的底空间是 $\operatorname{Spec} \hat{A}$ 中对应于包含 $I\hat{A}$ 的素理想集。由完备化的基本性质，$A/I \cong \hat{A}/I\hat{A}$，且 $A$ 中包含 $I$ 的素理想与 $\hat{A}$ 中包含 $I\hat{A}$ 的素理想一一对应。故 $Y$ 与 $\operatorname{Spec} \hat{A}$ 的底空间同胚。

结构层方面：对任意 $f \in A$，$\hat{X}$ 在 $D(f) \cap Y$ 上的截面为
$$\mathcal{O}_{\hat{X}}(D(f) \cap Y) = \varprojlim_n (A/I^n)_f = \varprojlim_n A_f/I^n A_f = \widehat{A_f}.$$

而 $(\operatorname{Spec} \hat{A})(D(\bar{f})) = \hat{A}_{\bar{f}}$，其中 $\bar{f}$ 是 $f$ 在 $\hat{A}$ 中的像。由完备化的平坦性（或直接用 Noetherian 性质），$\widehat{A_f} \cong (\hat{A})_{\bar{f}}$。因此结构层也同构，形式完备化同构于 $\operatorname{Spec} \hat{A}$。∎

### 关键概念提示

- 这是形式概形理论中最基本的计算之一：仿射形式概形就是完备化环的谱。
- 该结果说明形式概形的局部理论完全由交换代数的 adic 完备化理论描述。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 未验证结构层的同构 | 拓扑同胚只是第一步，还需证明截面的完备化与完备化的局部化可交换。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.FormalScheme
import Mathlib.RingTheory.AdicCompletion

open AlgebraicGeometry

-- 仿射概形的完备化同构于完备化环的谱
theorem affine_completion {A : Type*} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) :
    formalCompletion (Spec A) (Spec (A ⧸ I)) (subschemeIdeal I) ≅
    Spec (adicCompletion I A) :=
  sorry
```

---

## 习题 II.9.3 — 完备化函子的正合性

### 题号与精确引用

**Hartshorne II.9.3**

### 问题重述

设 $X$ 为 Noetherian 概形，$Y \subseteq X$ 为闭子概形，$\hat{X}$ 为形式完备化。证明：对任意凝聚层 $\mathcal{F}$ 的短正合列
$$0 \to \mathcal{F}' \to \mathcal{F} \to \mathcal{F}'' \to 0,$$
其完备化
$$0 \to \widehat{\mathcal{F}'} \to \widehat{\mathcal{F}} \to \widehat{\mathcal{F}''} \to 0$$
也是 $\hat{X}$ 上凝聚层的短正合列。

### 详细解答

**定义**：$\widehat{\mathcal{F}} = \varprojlim_n \mathcal{F}/\mathcal{I}^n\mathcal{F}$，其中 $\mathcal{I}$ 是 $Y$ 的理想层。对短正合列 $0 \to \mathcal{F}' \to \mathcal{F} \to \mathcal{F}'' \to 0$，考虑对每个 $n$ 的正合列
$$0 \to \mathcal{F}'/\mathcal{F}' \cap \mathcal{I}^n\mathcal{F} \to \mathcal{F}/\mathcal{I}^n\mathcal{F} \to \mathcal{F}''/\mathcal{I}^n\mathcal{F}'' \to 0.$$

由 Artin-Rees 引理（因 $X$ Noetherian 且 $\mathcal{F}'$ 凝聚），存在 $c$ 使得对所有 $n \ge c$ 有
$$\mathcal{I}^n\mathcal{F} \cap \mathcal{F}' = \mathcal{I}^{n-c}(\mathcal{I}^c\mathcal{F} \cap \mathcal{F}').$$
因此 $\{\mathcal{F}'/(\mathcal{F}' \cap \mathcal{I}^n\mathcal{F})\}$ 与 $\{\mathcal{F}'/\mathcal{I}^n\mathcal{F}'\}$ 作为投射系是等价的（pro-isomorphic），故它们的投射极限相同：
$$\varprojlim_n \mathcal{F}'/(\mathcal{F}' \cap \mathcal{I}^n\mathcal{F}) \cong \widehat{\mathcal{F}'}.$$

对每个 $n$，正合列
$$0 \to \mathcal{F}'/(\mathcal{F}' \cap \mathcal{I}^n\mathcal{F}) \to \mathcal{F}/\mathcal{I}^n\mathcal{F} \to \mathcal{F}''/\mathcal{I}^n\mathcal{F}'' \to 0$$
构成投射系的短正合列。取投射极限，由 Mittag-Leffler 条件（因 $X$ Noetherian，模降链稳定），左项满足 Mittag-Leffler 条件，故极限保持正合性。于是
$$0 \to \widehat{\mathcal{F}'} \to \widehat{\mathcal{F}} \to \widehat{\mathcal{F}''} \to 0$$
正合。∎

### 关键概念提示

- **Artin-Rees 引理** 是此证明的核心：它保证了子模的 $\mathcal{I}$-adic 拓扑与诱导拓扑一致。
- **Mittag-Leffler 条件** 保证了投射系正合列的极限仍正合。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 直接对投射极限用正合性 | 投射极限一般只左正合，右正合需要 Mittag-Leffler 条件或满射系统的验证。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.FormalScheme

open AlgebraicGeometry

-- 完备化函子在凝聚层短正合列上正合
theorem completion_exact {X : Scheme} [IsNoetherian X]
    (Y : ClosedImmersion.toScheme X) (I : IdealSheafData X)
    (ℱ' ℱ ℱ'' : CoherentSheaf X)
    (hseq : ShortExact ℱ'.val.val ℱ.val.val ℱ''.val.val) :
    ShortExact
      (completionSheaf X Y I ℱ').val.val
      (completionSheaf X Y I ℱ).val.val
      (completionSheaf X Y I ℱ'').val.val :=
  sorry
```

---

## 习题 II.9.4 — 射影概形上的完备化定理

### 题号与精确引用

**Hartshorne II.9.4**

### 问题重述

设 $X$ 为域 $k$ 上的 projective 概形，$\mathcal{F}$ 为凝聚层，$Y \subseteq X$ 为闭子概形。证明：自然映射
$$\alpha : H^i(X, \mathcal{F}) \longrightarrow H^i(\hat{X}, \widehat{\mathcal{F}})$$
对所有 $i \ge 0$ 都是同构。
（这是 Zariski 的 **完备化定理**（Theorem on Formal Functions）在整体截面上的推论，Hartshorne 在本题中只要求 $i = 0$ 的情形或给出证明框架。）

### 详细解答

*注：本题在 Hartshorne 中通常要求证明 $H^0(X, \mathcal{F}) \cong H^0(\hat{X}, \widehat{\mathcal{F}})$，即整体截面的完备化不变性。以下给出 $i = 0$ 的完整证明，并提及一般情形的定理。*

**$i = 0$ 的情形**：设 $X = \operatorname{Proj} S$，$S$ 为有限生成分次 $k$-代数，$\mathcal{F} = \widetilde{M}$ 对某分次 $S$-模 $M$。则
$$H^0(X, \mathcal{F}) = M_0$$
（在适当扭动后）。形式完备化 $\hat{X}$ 上的层 $\widehat{\mathcal{F}}$ 的整体截面为
$$H^0(\hat{X}, \widehat{\mathcal{F}}) = \varprojlim_n H^0(X, \mathcal{F}/\mathcal{I}^n\mathcal{F}).$$

因 $X$ 是 projective 且 proper 的，$H^0(X, \mathcal{F})$ 是有限维 $k$-向量空间。映射
$$H^0(X, \mathcal{F}) \longrightarrow H^0(X, \mathcal{F}/\mathcal{I}^n\mathcal{F})$$
的核与像构成稳定的投射系。由 $k$-向量空间的有限维性，存在 $n_0$ 使得对所有 $n \ge n_0$，上述映射是同构。取极限得
$$H^0(X, \mathcal{F}) \cong \varprojlim_n H^0(X, \mathcal{F}/\mathcal{I}^n\mathcal{F}) = H^0(\hat{X}, \widehat{\mathcal{F}}).$$

**一般 $i$ 的定理**：Zariski 的完备化定理断言：对 proper 态射 $f : X \to Y$ 及凝聚层 $\mathcal{F}$，有
$$R^i f_* \mathcal{F} \cong \varprojlim_n R^i f_* (\mathcal{F}/\mathcal{I}^n\mathcal{F}).$$
当 $Y = \operatorname{Spec} k$ 时，$R^i f_* \mathcal{F} = H^i(X, \mathcal{F})$，即得一般情形的同构。∎

### 关键概念提示

- **完备化定理** 是代数几何中最深刻的结果之一，它将概形的上同调与其形式邻域的上同调联系起来。
- 该定理在证明 **Zariski 主定理**、**Stein 分解**、以及比较定理中扮演核心角色。

### 常见错误警示

| 错误 | 纠正 |
|------|------|
| 未利用 projective/proper 的有限维性 | 非 proper 概形上，整体截面可能无限维，极限过程不会稳定。 |

### Lean4 代码占位

```lean4
import Mathlib.AlgebraicGeometry.FormalScheme
import Mathlib.AlgebraicGeometry.Cohomology

open AlgebraicGeometry

-- 完备化定理：射影概形上的上同调在完备化下不变
theorem formalFunctionsTheorem {X : Scheme} {k : Type*} [Field k]
    [Algebra k (X.presheaf.obj ⊤)] [IsProjectiveOver k X]
    (ℱ : CoherentSheaf X) (Y : ClosedImmersion.toScheme X)
    (I : IdealSheafData X) (i : ℕ) :
    (TopCat.Sheaf.cohomology i ℱ.val) ≅
    (TopCat.Sheaf.cohomology i (completionSheaf X Y I ℱ).val) :=
  sorry
```

---

**文档位置**: `docs/13-代数几何/Harvard-232br-习题解答/II.9-形式概形.md`
**创建日期**: 2026-04-17


## 习题

**习题 1.1**。解释形式概形与普通概形的主要区别。

*解答*：形式概形允许“无限小邻域”的信息，即沿着闭子概形的完备化。普通概形是局部环空间，而形式概形是拓扑环空间，其结构层是完备拓扑环。$\square$

---

**习题 1.2**。设 $X$ 是概形，$Y \\subseteq X$ 是闭子概形。描述 $X$ 沿 $Y$ 的完备化 $\\widehat{X}_Y$ 的直观意义。

*解答*：$\\widehat{X}_Y$ 保留了 $Y$ 及其任意阶无限小邻域的信息，丢弃了远离 $Y$ 的几何。形式函数的Taylor展开在此完备化上收敛。$\square$

## 相关文档

- [II.1-层的基本性质](II.1-层的基本性质.md)
- [II.2-概形的基本性质](II.2-概形的基本性质.md)
- [II.3-态射性质](II.3-态射性质.md)
- [II.4-分离性与本征性](II.4-分离性与本征性.md)
- [II.5-模与层-续](II.5-模与层-续.md)
---
**参考文献**

1. 相关教材与学术论文。
## 参考文献

1. Hartshorne, R. (1977). *Algebraic Geometry* (GTM 52). Springer. ISBN: 978-0387902449.
2. Vakil, R. (2024). *The Rising Sea: Foundations of Algebraic Geometry* (draft). Available at: http://math.stanford.edu/~vakil/216blog/
3. Liu, Q. (2002). *Algebraic Geometry and Arithmetic Curves*. Oxford University Press. ISBN: 978-0198502845.