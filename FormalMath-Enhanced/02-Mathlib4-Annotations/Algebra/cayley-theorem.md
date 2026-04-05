---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 凯莱定理 (Cayley's Theorem)
---
# 凯莱定理 (Cayley's Theorem)

## Mathlib4 引用

```lean
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.GroupAction.Basic

namespace Equiv

variable {G : Type*} [Group G]

/-- 凯莱定理：每个群都同构于某个置换群的子群 -/
def leftRegularRepresentation : G →* Perm G where
  toFun g := ⟨fun h ↦ g * h, fun h ↦ g⁻¹ * h,
    fun _ ↦ by simp [mul_assoc], fun _ ↦ by simp [mul_assoc]⟩
  map_one' := by ext; simp
  map_mul' := by intros; ext; simp [mul_assoc]

/-- 左正则表示是单射 -/
theorem leftRegularRepresentation_injective :
    Function.Injective (leftRegularRepresentation : G → Perm G) := by
  intro g h eq
  simpa using congr_arg (fun f ↦ f 1) eq

end Equiv
```

## 数学背景

凯莱定理由英国数学家阿瑟·凯莱（Arthur Cayley）于1854年提出，是群论发展史上的里程碑。这一定理的重要性在于它表明置换群是"通用"的——任何抽象群都可以在置换群中找到其具体实现。这为群论的研究提供了具体化、可视化的途径。

## 直观解释

凯莱定理告诉我们：**每个群都可以看作是一组置换**。想象一群舞者在舞台上，每个舞者有一个特定的舞步序列。群中的每个元素对应一个"舞步指令"，将每个舞者移动到另一个位置。这些指令的集合就构成了一个置换群。

具体来说，群 $G$ 的每个元素 $g$ 通过左乘作用在群上：$h \mapsto gh$。这个作用是一个置换（双射），所有这样的置换构成了与 $G$ 同构的群。

## 形式化表述

设 $G$ 是任意群，则 $G$ 同构于对称群 $\text{Sym}(G)$ 的某个子群。

即存在单同态：

$$\varphi: G \hookrightarrow \text{Sym}(G)$$

其中 $\varphi(g)(h) = gh$（左正则表示）。

## 证明思路

1. **构造映射**：定义左正则表示 $\varphi(g)(h) = gh$
2. **验证置换**：证明每个 $\varphi(g)$ 是双射
3. **验证同态**：证明 $\varphi(gh) = \varphi(g) \circ \varphi(h)$
4. **验证单射**：若 $\varphi(g) = \text{id}$，则 $g = e$

关键在于群的乘法满足结合律和逆元存在性。

## 示例

### 示例 1：克莱因四元群 $V_4$

$V_4 = \{e, a, b, c\}$，其中每个非单位元的阶为 2。

左正则表示：

- $e \mapsto ()$（恒等置换）
- $a \mapsto (e\ a)(b\ c)$
- $b \mapsto (e\ b)(a\ c)$
- $c \mapsto (e\ c)(a\ b)$

$V_4$ 同构于 $S_4$ 的一个子群。

### 示例 2：循环群 $\mathbb{Z}_4$

$\mathbb{Z}_4 = \{0, 1, 2, 3\}$，模 4 加法。

左正则表示为 4-循环：

- $1 \mapsto (0\ 1\ 2\ 3)$
- $2 \mapsto (0\ 2)(1\ 3)$
- $3 \mapsto (0\ 3\ 2\ 1)$

$\mathbb{Z}_4$ 同构于由 4-循环生成的 $S_4$ 的子群。

### 示例 3：二面体群 $D_3$

正三角形的对称群 $D_3$，阶为 6。

通过凯莱嵌入，$D_3$ 同构于 $S_6$ 的子群。实际上，$D_3 \cong S_3$，可以更有效地嵌入 $S_3$。

## 应用

- **群的具体化**：将抽象群转化为置换群进行计算
- **计算机代数**：群的计算机表示和算法
- **组合群论**：通过置换作用研究群性质
- **编码理论**：置换群在纠错码中的应用

## 相关概念

- 置换群 (Permutation Group)：由置换构成的群
- 群作用 (Group Action)：群在集合上的作用
- 正则表示 (Regular Representation)：左乘和右乘作用
- 忠实作用 (Faithful Action)：核为平凡的群作用

## 参考

### 教材

- [Dummit & Foote. Abstract Algebra. Wiley, 3rd edition, 2004. Section 4.2]
- [Fraleigh. A First Course in Abstract Algebra. Pearson, 7th edition, 2002. Section 8.3]

### 历史文献

- [Cayley. On the theory of groups. Philosophical Magazine, 1854]

### 在线资源

- [Mathlib4 文档 - Perm](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Perm/Basic.html)[需更新]
- [nLab - Cayley's theorem](https://ncatlab.org/nlab/show/Cayley%27s+theorem)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
