# van Kampen定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 代数拓扑
**难度**: L3

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Seifert-van Kampen定理 |
| **领域** | 代数拓扑 |
| **发现者** | Seifert, van Kampen (1930s) |
| **前置知识** | 基本群、自由积、推送出 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**van Kampen定理**：设X = U₁ ∪ U₂，U₁、U₂、U₁∩U₂都道路连通，x₀ ∈ U₁∩U₂，则：

$$\pi_1(X, x_0) \cong \pi_1(U_1, x_0) *_{\pi_1(U_1 \cap U_2, x_0)} \pi_1(U_2, x_0)$$

其中*表示自由积的推送出（pushout）。

### 1.2 特殊情形

若U₁∩U₂单连通，则：
$$\pi_1(X) \cong \pi_1(U_1) * \pi_1(U_2)$$

### 1.3 Lean 4 形式化

```lean
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

-- van Kampen定理（简化表述）
theorem van_kampen {X : Type*} [TopologicalSpace X]
    {U1 U2 : Set X} (hU1 : IsOpen U1) (hU2 : IsOpen U2)
    (hX : U1 ∪ U2 = Set.univ) (hU12 : IsPathConnected (U1 ∩ U2))
    (x0 : X) (hx0 : x0 ∈ U1 ∩ U2) :
    -- 基本群的推送出结构
    sorry  -- 需要详细的同伦论形式化
```

---

## 二、几何表征（可视化）

### 2.1 空间分解

```text
    X = U₁ ∪ U₂
    ┌──────┬──────┐
    │  U₁  │      │
    │      │  U₂  │
    │  ┌───┴───┐  │
    │  │U₁∩U₂ │  │
    │  └──────┘  │
    └────────────┘

基本群 = U₁和U₂的基本群的"粘合"
```

### 2.2 例子：8字形

```text
8字形 = 两个圆粘在一点
π₁(8) = ℤ * ℤ (两个自由生成元)
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **van Kampen定理**：复杂空间的基本群 = 各部分基本群的"自由组合"，但要考虑重叠部分

### 3.2 拼图类比

- U₁、U₂：两块拼图
- U₁∩U₂：重叠部分
- 基本群：从重叠部分"粘合"两个群的生成元

### 3.3 为什么需要推送出？

重叠部分在两个群中都出现，需要"识别"它们

---

## 四、计算表征（算法）

### 4.1 Python实现（简化：群表示）

```python
from sympy.combinatorics.free_groups import FreeGroup

def van_kampen_compute(G1, G2, G12, i1, i2):
    """
    计算推送出 G1 *_{G12} G2
    G1, G2: 群
    G12: 重叠群
    i1: G12 → G1 的嵌入
    i2: G12 → G2 的嵌入
    """
    # 构造自由积
    F = FreeGroup('a', 'b')  # 简化

    # 添加关系：i1(g) = i2(g) for g in G12
    relations = []
    for g in G12.generators:
        rel = i1(g) * i2(g).inverse()
        relations.append(rel)

    # 商群 = 自由积 / 关系
    return F / relations

# 示例：8字形
# G1 = G2 = ℤ, G12 = {1}
# π₁(8) = ℤ * ℤ
```

---

## 五、范畴表征（抽象）

### 5.1 范畴视角

```text
van Kampen = 推送出（pushout）
    G12 ──i1──> G1
     │           │
    i2           │
     │           ↓
    G2 ──────> G1 *_{G12} G2

在群范畴中的推送出
```

### 5.2 同调版本

Hurewicz定理 + van Kampen ⟹ 一阶同调群的计算

### 5.3 推广

- 高阶同伦群：更复杂
- ∞-群胚：现代推广

---

## 关联定理

| 定理 | 关系 |
|------|------|
| **Hurewicz定理** | 基本群到一阶同调 |
| **覆盖空间理论** | 基本群的应用 |

---

**状态**: ✅ 完成
