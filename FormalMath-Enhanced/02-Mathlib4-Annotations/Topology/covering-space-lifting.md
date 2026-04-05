---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 覆盖空间提升性质 (Covering Space Lifting Property)
---
# 覆盖空间提升性质 (Covering Space Lifting Property)

## Mathlib4 引用

```lean
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Equiv

namespace CoveringSpace

variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]
variable {p : E → X} (hp : IsCoveringMap p)

/-- 路径提升性质 -/
theorem path_lifting {γ : Path Y X} {e₀ : E} (he₀ : p e₀ = γ 0) :
    ∃! γ̃ : Path Y E, γ̃ 0 = e₀ ∧ p ∘ γ̃ = γ := by
  -- 利用局部平凡性和道路连通性
  sorry

/-- 同伦提升性质 -/
theorem homotopy_lifting {F : Y → I → X} {f̃ : Y → E}
    (hF : Continuous F) (hf̃ : Continuous f̃)
    (hcomm : ∀ y, p (f̃ y) = F y 0) :
    ∃! F̃ : Y → I → E, Continuous F̃ ∧ (∀ y, F̃ y 0 = f̃ y) ∧ (λ y t => p (F̃ y t)) = F := by
  sorry

/-- 单值性定理 -/
theorem monodromy {γ δ : Path Unit X} (hγ : γ 0 = δ 0) (hδ : γ 1 = δ 1)
    (H : Path.Homotopic γ δ) {e₀ : E} (he₀ : p e₀ = γ 0) :
    let γ̃ := (path_lifting hp he₀).default
    let δ̃ := (path_lifting hp (hγ.symm ▸ he₀)).default
    γ̃ 1 = δ̃ 1 := by
  -- 同伦提升给出相同终点
  sorry

end CoveringSpace
```

## 数学背景

覆盖空间理论是代数拓扑的核心工具，由Poincaré在19世纪末开创，H. Weyl和S. Eilenberg在20世纪上半叶发展。提升性质（路径提升和同伦提升）是覆盖空间理论的基本定理，建立了覆盖空间与基本群的深刻联系。这一理论在黎曼曲面、李群和伽罗瓦理论的拓扑类比中都有重要应用。

## 直观解释

覆盖空间提升性质告诉我们：**在覆盖空间上，"下面"的路径和同伦可以唯一地"提升"到"上面"**。

想象覆盖空间 $E$ 是空间 $X$ 的多层"副本"堆叠（像螺旋楼梯投影到圆）。提升性质说，给定起点在某层，$X$ 中的任何道路可以唯一地"跟踪"到 $E$ 中的一条道路。这就像说，你可以沿着螺旋楼梯走，唯一地对应于地面上的路径。

## 形式化表述

覆盖映射 $p: E \to X$ 满足**提升性质**：

**路径提升**：给定道路 $\gamma: [0,1] \to X$ 和 $e_0 \in E$ 使 $p(e_0) = \gamma(0)$，存在唯一的提升 $\tilde{\gamma}: [0,1] \to E$ 使 $\tilde{\gamma}(0) = e_0$ 且 $p \circ \tilde{\gamma} = \gamma$。

**同伦提升**：给定同伦 $F: Y \times [0,1] \to X$ 和初始提升 $\tilde{f}: Y \to E$，存在唯一的提升 $\tilde{F}$。

**单值性定理**：同伦的道路有相同的提升终点。

## 证明思路

1. **局部提升**：
   - 利用覆盖映射的局部同胚性
   - 在小邻域内提升存在且唯一

2. **拼接提升**：
   - 将道路分为小段
   - 每段在均匀覆盖邻域内
   - 唯一性保证拼接相容

3. **同伦提升**：
   - 类似路径提升，但参数化
   - Lebesgue数保证细分

4. **单值性**：
   - 同伦给出连续的终点映射
   - 离散纤维蕴含常值

核心洞察是局部同胚性和道路连通性的结合。

## 示例

### 示例 1：指数映射

$p: \mathbb{R} \to S^1$，$p(t) = e^{2\pi i t}$。

$\gamma$ 绕 $S^1$ $n$ 圈，提升 $\tilde{\gamma}$ 是从 $0$ 到 $n$ 的直线。

不同提升对应不同层（不同整数起点）。

### 示例 2：万有覆盖

$\mathbb{H} \to \mathbb{C} \setminus \{0, 1\}$（模函数）。

提升性质允许计算映射的分类。

### 示例 3：二重覆盖

$p: S^1 \to S^1$，$p(z) = z^2$。

路径绕奇数圈时，提升连接不同"层"（若起点固定）。

## 应用

- **基本群计算**：$\pi_1(X) \cong \text{Deck}(E)$（覆盖变换群）
- **黎曼曲面**：多值函数的黎曼面构造
- **伽罗瓦理论**：域扩张与覆盖的类比
- **李群**：万有覆盖群的构造
- **辫子群**：构型空间的覆盖

## 相关概念

- [覆盖空间 (Covering Space)](./covering-space.md)：局部同胚的纤维丛
- [万有覆盖 (Universal Cover)](./universal-cover.md)：单连通的覆盖
- [Deck变换 (Deck Transformation)](./deck-transformation.md)：覆盖的自同构
- [纤维 (Fiber)](./fiber.md)：点的原像
- [覆叠群 (Covering Group)](./covering-group.md)：覆盖的同构类

## 参考

### 教材

- [Hatcher. Algebraic Topology. Cambridge, 2002. Chapter 1]
- [Massey. Algebraic Topology: An Introduction. Springer, 1967. Chapter 5]

### 历史文献

- [Weyl. Die Idee der Riemannschen Fläche. 1913]
- [Eilenberg. Transformations continues en circonférence. 1934]

### 在线资源

- [Mathlib4 文档 - Covering](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Covering/Basic.html)
- [Hatcher - Covering Spaces](https://pi.math.cornell.edu/~hatcher/AT/ATch1.pdf)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
