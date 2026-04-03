---
msc_primary: 00A99
processed_at: '2026-04-03'
---

# Pólya计数定理 (Pólya's Enumeration Theorem)

## Mathlib4 引用

```lean
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

namespace PolyaCounting

variable {α : Type*} [Finite α] (G : Type*) [Group G] [MulAction G α] [Finite G]

/-- 循环指标 -/
def cycleIndex (G : Type*) [Group G] [Finite G] [MulAction G α] : MvPolynomial ℕ ℝ :=
  (1 / Fintype.card G) * ∑ g : G, ∏ c in cycleType g, X (Fintype.card c)

/-- Pólya计数定理 -/
theorem polya_counting (colors : Type*) [Finite colors] (w : colors → ℝ) :
    ∑ o in orbitRel G (α → colors), weight w o =
    eval (fun k => ∑ c : colors, w c ^ k) (cycleIndex G) := by
  -- 生成函数版本的不等价染色计数
  sorry

/-- 带权轨道生成函数 -/
theorem polya_generating_function (colors : Type*) [Finite colors] :
    ∑ o in orbitRel G (α → colors), monomial (countColor o) 1 =
    cycleIndex G.eval (fun k => ∑ c : colors, X c ^ k) := by
  -- 多元生成函数版本
  sorry

end PolyaCounting
```

## 数学背景

Pólya计数定理由匈牙利数学家George Pólya于1937年发表，是Burnside引理的深刻推广。它不仅计算不等价配置的个数，还能追踪配置中各种"颜色"的使用情况（通过生成函数）。这一定理在化学（同分异构体计数）、组合学和物理学中有革命性影响。

## 直观解释

Pólya定理告诉我们：**不等价染色配置的生成函数，可以通过群的循环指标代入颜色生成函数得到**。想象用不同宝石装饰皇冠，Pólya定理不仅告诉你有多少种不等价装饰，还能告诉你每种装饰用了多少红宝石、多少蓝宝石——全部编码在一个优雅的公式中。

## 形式化表述

设有限群 $G$ 作用在有限集 $X$ 上，颜色集 $C$ 有权重函数 $w: C \to \mathbb{R}$。

**循环指标**：
$$Z_G(x_1, x_2, ...) = \frac{1}{|G|} \sum_{g \in G} x_1^{c_1(g)} x_2^{c_2(g)} \cdots$$

其中 $c_k(g)$ 是 $g$ 作用下的 $k$-循环数。

**Pólya定理**：
$$\sum_{\text{轨道 } O} W(O) = Z_G\left(\sum_{c} w(c), \sum_{c} w(c)^2, ...\right)$$

其中 $W(O)$ 是轨道 $O$ 中配置的权重。

## 证明思路

1. **循环分解**：将群元素分解为不相交循环
2. **不动点结构**：$g$ 的不动点对应于循环上常值染色
3. **Burnside引理**：应用轨道计数
4. **生成函数**：追踪权重信息
5. **代入公式**：循环指标的自然解释

## 示例

### 示例 1：项链（带颜色计数）

$n$ 个珠子的项链，$k$ 种颜色。

循环指标：$Z_{C_n} = \frac{1}{n} \sum_{d|n} \varphi(d) x_d^{n/d}$

$m$ 红、$n-m$ 蓝的染色数：展开 $Z_{C_n}(r+b, r^2+b^2, ...)$ 的系数

### 示例 2：立方体面染色

循环指标涉及24个旋转的循环结构：

- 恒等：$x_1^6$
- 面旋转：$x_1^2 x_4$ 等
- 对角旋转：$x_2^3$ 等

### 示例 3：酒精计数

烷基 $C_n H_{2n+1}$ 的计数利用根树的对称群。

## 应用

- **化学**：同分异构体系统计数
- **图论**：图枚举
- **组合设计**：计数不等价设计
- **编码理论**：等价码计数
- **统计力学**：配分函数计算

## 相关概念

- [Burnside引理](./burnside-lemma.md)：基础版本
- [循环指标](./cycle-index.md)：群的结构不变量
- [生成函数](./generating-function-theorem.md)：计数工具
- [对称群](./symmetric-group.md)：常见作用群

## 参考

### 教材

- [Pólya & Read. Combinatorial Enumeration of Groups, Graphs, and Chemical Compounds. Springer, 1987]
- [Harary & Palmer. Graphical Enumeration. Academic Press, 1973]

### 历史文献

- [Pólya. Kombinatorische Anzahlbestimmungen für Gruppen, Graphen und chemische Verbindungen. 1937]

### 在线资源

- [Mathlib4 文档 - Group Action](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/GroupAction/Basic.html)

---

*最后更新：2026-04-03 | 版本：v1.0.0*
