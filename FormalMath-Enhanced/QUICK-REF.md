---
title: 📋 快速参考卡片
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-05'
---
# 📋 快速参考卡片

> 常用公式、编码和指令速查手册

---

## 📑 目录

- [📋 快速参考卡片](#-快速参考卡片)
  - [📑 目录](#-目录)
  - [🔢 MSC 编码速查](#-msc-编码速查)
    - [基础数学 (03)](#基础数学-03)
    - [代数结构 (12-22)](#代数结构-12-22)
    - [分析学 (26-47)](#分析学-26-47)
    - [几何学 (51-53)](#几何学-51-53)
    - [拓扑学 (54-57)](#拓扑学-54-57)
    - [MSC 标注格式模板](#msc-标注格式模板)
  - [📐 常用定理速查](#-常用定理速查)
    - [代数学定理](#代数学定理)
    - [分析学定理](#分析学定理)
    - [数论定理](#数论定理)
    - [线性代数定理](#线性代数定理)
    - [拓扑学定理](#拓扑学定理)
  - [🏆 IMO 公式速查](#-imo-公式速查)
    - [常用不等式](#常用不等式)
    - [数论公式](#数论公式)
    - [几何公式](#几何公式)
    - [组合公式](#组合公式)
  - [🔧 Lean4 Tactics 速查](#-lean4-tactics-速查)
    - [基础 Tactics](#基础-tactics)
    - [高级 Tactics](#高级-tactics)
    - [结构化证明](#结构化证明)
    - [常用库引用](#常用库引用)
    - [搜索命令](#搜索命令)
  - [🔗 相关索引](#-相关索引)

---

## 🔢 MSC 编码速查

### 基础数学 (03)

| 编码 | 主题 | 适用内容 |
|------|------|----------|
| `03E10` | 序数与基数 | 集合论基础 |
| `03E25` | 选择公理 | 公理化集合论 |
| `03E30` | ZFC 公理化 | 数学基础 |
| `03E35` | 力迫法 | 独立性证明 |
| `03C45` | 稳定性理论 | 模型论 |

### 代数结构 (12-22)

| 编码 | 主题 | 适用内容 |
|------|------|----------|
| `12F10` | Galois 理论 | 域扩张、方程可解性 |
| `16D40` | 模理论 | 模结构、同调代数 |
| `17B20` | 半单李代数 | 李群李代数 |
| `20D05` | 有限单群分类 | 群论核心 |
| `20E05` | 自由群 | 组合群论 |
| `20G05` | 表示理论 | 群表示 |

### 分析学 (26-47)

| 编码 | 主题 | 适用内容 |
|------|------|----------|
| `26A42` | Lebesgue 积分 | 实分析 |
| `28A25` | 测度与积分 | 测度论 |
| `30C35` | 共形映射 | 复分析 |
| `30D35` | 值分布理论 | Nevanlinna 理论 |
| `47A10` | 谱理论 | 泛函分析 |
| `46L05` | C*-代数 | 算子代数 |

### 几何学 (51-53)

| 编码 | 主题 | 适用内容 |
|------|------|----------|
| `51M05` | 欧氏几何 | 初等几何 |
| `52A20` | 凸体 | 凸几何 |
| `53C20` | Riemann 几何 | 微分几何 |
| `53D05` | 辛几何 | 经典力学 |
| `14H52` | 椭圆曲线 | 代数几何、数论 |
| `14J28` | K3 曲面 | 代数曲面 |

### 拓扑学 (54-57)

| 编码 | 主题 | 适用内容 |
|------|------|----------|
| `54E35` | 度量空间 | 点集拓扑 |
| `54D30` | 紧性 | 拓扑性质 |
| `55N10` | 奇异同调 | 代数拓扑 |
| `55Q40` | 球面同伦群 | 同伦论 |
| `57K10` | 纽结理论 | 低维拓扑 |
| `57R65` | 割补理论 | 微分拓扑 |

### MSC 标注格式模板

```yaml
---
msc_primary: "20D05"      # 主要分类（1个）
msc_secondary:             # 次要分类（0-5个）
  - "20D06"
  - "20C33"
keywords:                  # 关键词（3-8个）
  - 有限单群
  - 分类定理
  - 群论
---
```

---

## 📐 常用定理速查

### 代数学定理

| 定理 | 陈述 | 链接 |
|------|------|------|
| **拉格朗日定理** | 有限群 G 的子群 H，\|H\| 整除 \|G\| | [详情](./02-Mathlib4-Annotations/Algebra/lagrange-theorem.md) |
| **西罗定理** | 对 pⁿ \| \|G\|，存在阶为 pⁿ 的子群 | [详情](./02-Mathlib4-Annotations/Algebra/sylow-theorem.md) |
| **群同态基本定理** | G/ker(φ) ≅ im(φ) | [详情](./02-Mathlib4-Annotations/Algebra/first-isomorphism-theorem.md) |
| **凯莱定理** | 每个群都同构于某个置换群的子群 | [详情](./02-Mathlib4-Annotations/Algebra/cayley-theorem.md) |
| **中国剩余定理** | 模互素理想，同余方程组有唯一解 | [详情](./02-Mathlib4-Annotations/Algebra/chinese-remainder-theorem.md) |

### 分析学定理

| 定理 | 陈述 | 链接 |
|------|------|------|
| **柯西积分公式** | f(a) = ¹⁄₂πᵢ ∮ f(z)/(z-a) dz | [详情](./02-Mathlib4-Annotations/Analysis/cauchy-integral-formula.md) |
| **留数定理** | ∮ f(z)dz = 2πi × (留数之和) | [详情](./02-Mathlib4-Annotations/Analysis/residue-theorem.md) |
| **微分中值定理** | ∃c, f'(c) = (f(b)-f(a))/(b-a) | [详情](./02-Mathlib4-Annotations/Analysis/mean-value-theorem.md) |
| **傅里叶变换** | ̂f(ξ) = ∫ f(x)e⁻²πᵢₓξ dx | [详情](./02-Mathlib4-Annotations/Analysis/fourier-transform.md) |
| **隐函数定理** | Jacobian 可逆 ⇒ 局部显式解存在 | [详情](./02-Mathlib4-Annotations/Analysis/implicit-function-theorem.md) |

### 数论定理

| 定理 | 陈述 | 链接 |
|------|------|------|
| **素数定理** | π(x) ~ x/ln(x) | [详情](./02-Mathlib4-Annotations/NumberTheory/prime-number-theorem.md) |
| **二次互反律** | (p/q)(q/p) = (-1)^((p-1)(q-1)/4) | [详情](./02-Mathlib4-Annotations/NumberTheory/quadratic-reciprocity.md) |
| **费马小定理** | aᵖ⁻¹ ≡ 1 (mod p) | [详情](./02-Mathlib4-Annotations/NumberTheory/fermat-little-theorem.md) |
| **狄利克雷定理** | 等差数列中有无穷多素数 | [详情](./02-Mathlib4-Annotations/NumberTheory/dirichlet-theorem.md) |

### 线性代数定理

| 定理 | 陈述 | 链接 |
|------|------|------|
| **谱定理** | 正规矩阵可酉对角化 | [详情](./02-Mathlib4-Annotations/LinearAlgebra/spectral-theorem.md) |
| **凯莱-哈密顿** | 矩阵满足其特征方程 | [详情](./02-Mathlib4-Annotations/LinearAlgebra/cayley-hamilton-theorem.md) |
| **SVD** | A = UΣV* | [详情](./02-Mathlib4-Annotations/LinearAlgebra/svd-theorem.md) |
| **秩-零化度** | rank(A) + nullity(A) = n | [详情](./02-Mathlib4-Annotations/LinearAlgebra/rank-nullity-theorem.md) |
| **约当标准型** | 复方阵相似于约当块直和 | [详情](./02-Mathlib4-Annotations/LinearAlgebra/jordan-normal-form.md) |

### 拓扑学定理

| 定理 | 陈述 | 链接 |
|------|------|------|
| **布劳威尔不动点** | 连续映射 f: Dⁿ→Dⁿ 有不动点 | [详情](./02-Mathlib4-Annotations/Topology/brouwer-fixed-point.md) |

---

## 🏆 IMO 公式速查

### 常用不等式

| 不等式 | 公式 | 适用场景 |
|--------|------|----------|
| **AM-GM** | (a₁+...+aₙ)/n ≥ ⁿ√(a₁...aₙ) | 正数平均值 |
| **Cauchy-Schwarz** | (∑aᵢbᵢ)² ≤ (∑aᵢ²)(∑bᵢ²) | 内积估计 |
| **Schur** | ∑aᵗ(a-b)(a-c) ≥ 0 | 对称不等式 |
| **Jensen** | f(∑λᵢxᵢ) ≤ ∑λᵢf(xᵢ) | 凸函数 |
| **Holder** | ∑|aᵢbᵢ| ≤ (∑|aᵢ|ᵖ)¹/ᵖ(∑|bᵢ|q)¹/q | 积分和级数 |

### 数论公式

| 公式 | 内容 | 适用场景 |
|------|------|----------|
| **欧拉定理** | a^φ(n) ≡ 1 (mod n) | 模幂运算 |
| **费马小定理** | aᵖ⁻¹ ≡ 1 (mod p) | 素数模 |
| **LTE 引理** | vₚ(aⁿ-bⁿ) = vₚ(a-b) + vₚ(n) | 素因子分析 |
| **Vieta 跳跃** | 对称方程根变换 | 丢番图方程 |

### 几何公式

| 公式 | 内容 | 适用场景 |
|------|------|----------|
| **Euler 线** | O, G, H 共线，OG:GH = 1:2 | 三角形中心 |
| **九点圆** | 通过 9 个特殊点，半径 R/2 | 三角形几何 |
| **Ceva 定理** | (BD/DC)(CE/EA)(AF/FB) = 1 | 共点线 |
| **Menelaus** | (BD/DC)(CE/EA)(AF/FB) = -1 | 共线点 |
| **Ptolemy** | AC·BD = AB·CD + BC·DA | 圆内接四边形 |

### 组合公式

| 公式 | 内容 | 适用场景 |
|------|------|----------|
| **Catalan 数** | Cₙ = ¹⁄ₙ₊₁ C(2n,n) | 括号化、路径计数 |
| **Burnside 引理** | |X/G| = ¹⁄|G| ∑|Xᵍ| | 轨道计数 |
| **容斥原理** | |∪Aᵢ| = ∑|Aᵢ| - ∑|Aᵢ∩Aⱼ| + ... | 并集计数 |

---

## 🔧 Lean4 Tactics 速查

### 基础 Tactics

| Tactic | 功能 | 示例 |
|--------|------|------|
| `intro` | 引入假设 | `intro h` |
| `exact` | 精确匹配目标 | `exact h` |
| `apply` | 应用蕴含 | `apply theorem_name` |
| `rewrite` / `rw` | 重写 | `rw [lemma]` |
| `simp` | 简化 | `simp [defs]` |
| `norm_num` | 数值归一化 | `norm_num` |
| `linarith` | 线性算术 | `linarith` |
| `ring` | 环简化 | `ring` |
| `field_simp` | 域简化 | `field_simp` |

### 高级 Tactics

| Tactic | 功能 | 示例 |
|--------|------|------|
| `induction` | 归纳法 | `induction n with` |
| `cases` | 情况分析 | `cases h with` |
| `constructor` | 构造合取 | `constructor` |
| `have` | 引入中间结论 | `have h : P := ...` |
| `show` | 显式目标 | `show P` |
| `by_contra` | 反证法 | `by_contra h` |
| `use` | 存在量词引入 | `use witness` |
| `refine` | 部分构造 | `refine ⟨a, b, ?_⟩` |

### 结构化证明

```lean
example : P → Q := by
  intro hp          -- 引入假设 P
  have h1 : R := by
    apply lemma1    -- 证明中间结论 R
    exact hp
  have h2 : S := by
    apply lemma2
    exact h1
  exact h2          -- 证明目标 Q
```

### 常用库引用

```lean
import Mathlib.Data.Nat.Basic        -- 自然数
import Mathlib.Algebra.Group.Basic   -- 群论
import Mathlib.Analysis.Complex.Basic -- 复分析
import Mathlib.LinearAlgebra.Basic   -- 线性代数
import Mathlib.Topology.Basic        -- 拓扑学
```

### 搜索命令

| 命令 | 功能 |
|------|------|
| `#check expr` | 检查表达式类型 |
| `#print theorem` | 打印定理定义 |
| `#find_home expr` | 查找表达式所属模块 |
| `library_search` | 搜索 applicable 引理 |
| `suggest` | 建议下一步 tactics |

---

## 🔗 相关索引

- 📍 [中央索引](./INDEX.md) - 项目总览
- 🏷️ [按主题分类索引](./BY-TOPIC.md) - 主题导航
- 📊 [按难度分级索引](./BY-LEVEL.md) - 难度导航
- 🔍 [搜索指南](./SEARCH-GUIDE.md) - 搜索技巧

---

*参考卡片最后更新：2026年4月3日*
