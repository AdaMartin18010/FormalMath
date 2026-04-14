---
msc_primary: 00A99
processed_at: '2026-04-15'
title: 圆的基本群 (Fundamental Group of the Circle)
---
# 圆的基本群 (Fundamental Group of the Circle)

## Mathlib4 引用

```lean
import Mathlib.AlgebraicTopology.FundamentalGroupoid

namespace AlgebraicTopology

/-- 圆 S¹ 的基本群同构于整数加群 Z -/
theorem fundamental_group_circle :
    FundamentalGroup (Metric.sphere (0 : ℂ) 1) (1 : ℂ) ≅ Multiplicative ℤ := by
  -- 利用覆叠空间 R → S¹ 和提升性质证明
  sorry

end AlgebraicTopology
```

## 数学背景

圆的基本群是代数拓扑学中最经典、最重要的计算结果之一，它建立了拓扑学与群论之间的深刻联系。该定理断言：圆 S^1 在基点处的基本群同构于整数加群 Z。这一结果由庞加莱（Henri Poincaré）在19世纪末开创的基本群理论中隐含，后由覆叠空间理论的系统发展得到严格证明。圆的基本群不仅是理解覆叠空间、同伦论和纤维丛的入门实例，也是现代数学物理中拓扑不变量的原型。

## 直观解释

圆的基本群揭示了一个优美的拓扑-代数对应：圆上的环路（从基点出发并回到基点的连续路径）按照绕圆心的圈数进行分类。想象一只蚂蚁在圆环上爬行，从某一点出发最终回到该点。这只蚂蚁的路径可能完全没有绕圆心转圈（平凡的环路），可能顺时针绕了 1 圈、2 圈，也可能逆时针绕了 1 圈、2 圈。基本群告诉我们：这些环路在同伦意义下（允许连续变形）完全由绕数决定，而绕数的集合恰好构成整数群 Z。

## 形式化表述

设 S^1 = \{z \in \mathbb{C} : |z| = 1\} 是复平面上的单位圆，1 \in S^1 是基点。则 S^1 在基点 1 处的基本群为：

$$\pi_1(S^1, 1) \cong \mathbb{Z}$$

同构映射由绕数（winding number）给出：对任意基于 1 的环路 γ: [0, 1] → S^1，定义其绕数为：

$$\text{wind}(\gamma) = \frac{1}{2\pi i} \int_\gamma \frac{dz}{z}$$

这个积分值总是一个整数，表示环路 γ 绕原点旋转的净圈数（逆时针为正）。

其中：

- π_1(X, x_0) 表示空间 X 在基点 x_0 处的基本群
- 同伦 γ_1 ~ γ_2 意味着一条环路可以连续变形为另一条
- 群运算由环路的拼接（concatenation）给出

## 证明思路

1. **覆叠空间**：考虑覆叠映射 p: R → S^1，p(t) = e^{2\pi i t}，即将实直线螺旋缠绕到圆上
2. **道路提升**：S^1 中任何基于 1 的环路 γ 可以唯一提升为 R 中基于 0 的道路 \tilde{\gamma}
3. **绕数定义**：由于 γ(1) = 1，提升后的终点 \tilde{\gamma}(1) 必为某个整数 n \in Z，定义绕数为 n
4. **同态与同构**：绕数定义了群同态 π_1(S^1, 1) → Z，由覆叠空间的唯一提升性质知其是双射

核心洞察在于覆叠空间 R → S^1 将圆上的环路展开为直线上的路径，终点的差异精确度量了绕数。

## 示例

### 示例 1：常值环路

常值环路 γ(t) = 1 的绕数为 0，对应基本群中的单位元。

### 示例 2：标准环路

γ_n(t) = e^{2\pi i n t} 绕原点 n 圈。当 n = 1 时，这是基本群的生成元；n = -1 对应反向绕行。

### 示例 3：Brouwer 不动点定理

圆的基本群可用于证明 Brouwer 不动点定理的一个版本：圆盘 D^2 到自身的任何连续映射都有不动点。若不然，可从边界 S^1 构造缩回（retraction），但缩回会诱导基本群的满同态 Z → \{0\}，这是不可能的。

## 应用

- **覆叠空间理论**：基本群与覆叠空间的 Galois 对应
- **复分析**：Cauchy 积分公式和留数定理中的绕数概念
- **代数拓扑**：高阶同伦群和纤维序列的计算
- **拓扑量子场论**：辫群和 anyon 统计的数学基础
- **动力系统**：庞加莱-Bendixson 定理和周期轨道的拓扑分类

## 相关概念

- 基本群 (Fundamental Group)：基于同伦等价类的环路群
- 覆叠空间 (Covering Space)：局部同胚的连续满射
- 绕数 (Winding Number)：闭曲线绕某点的圈数
- 同伦 (Homotopy)：连续变形的路径等价关系
- Brouwer 不动点定理 (Brouwer Fixed-Point Theorem)：圆盘自映射必有不动点

## 参考

### 教材

- [A. Hatcher. Algebraic Topology. Cambridge, 2002. Chapter 1]
- [W. S. Massey. A Basic Course in Algebraic Topology. Springer, 1991. Chapter 2]

### 在线资源

- [Mathlib4 - FundamentalGroupoid](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/FundamentalGroupoid.html)

---

*最后更新：2026-04-15 | 版本：v1.0.0*