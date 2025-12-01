# Seifert-van Kampen定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 代数拓扑
**难度**: L3

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Seifert-van Kampen定理（一般形式） |
| **领域** | 代数拓扑 |
| **发现者** | Seifert, van Kampen (1930s) |
| **前置知识** | 基本群、群胚、推送出 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Seifert-van Kampen定理**：设X = ∪ᵢ Uᵢ，其中{Uᵢ}是开覆盖，所有有限交都道路连通，x₀ ∈ ∩ᵢ Uᵢ，则：

$$\pi_1(X, x_0) \cong \operatorname{colim}_{i} \pi_1(U_i, x_0)$$

即基本群是各Uᵢ的基本群的余极限（colimit）。

### 1.2 特殊情形

两个开集时退化为van Kampen定理。

### 1.3 Lean 4 形式化

```lean
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

-- Seifert-van Kampen（一般形式）
theorem seifert_van_kampen {X : Type*} [TopologicalSpace X]
    {U : ι → Set X} (hU : ∀ i, IsOpen (U i))
    (hX : ⋃ i, U i = Set.univ)
    (hU_fin : ∀ s : Finset ι, IsPathConnected (⋂ i ∈ s, U i))
    (x0 : X) (hx0 : ∀ i, x0 ∈ U i) :
    -- 基本群的余极限结构
    sorry  -- 需要详细的同伦论形式化
```

---

## 二、几何表征（可视化）

### 2.1 多区域覆盖

```text
    X = U₁ ∪ U₂ ∪ U₃
    ┌──────┬──────┐
    │  U₁  │  U₂  │
    │  ┌───┴───┐  │
    │  │U₁∩U₂ │  │
    │  └───┬───┘  │
    │      │  U₃  │
    └──────┴──────┘

基本群 = 所有Uᵢ的基本群的"协调粘合"
```

### 2.2 例子：多圆粘合

```text
多个圆在一点粘合：
π₁ = ℤ * ℤ * ... * ℤ (自由积)
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **Seifert-van Kampen**：复杂空间的基本群 = 所有部分基本群的"协调组合"

### 3.2 拼图类比

- 多个拼图块：U₁, U₂, ...
- 重叠区域：Uᵢ ∩ Uⱼ
- 基本群：所有块的群"协调地"粘合

### 3.3 为什么需要有限交连通？

保证所有重叠区域都有明确的"连接方式"

---

## 四、计算表征（算法）

### 4.1 Python实现（简化）

```python
def seifert_van_kampen_compute(cover, intersections):
    """
    计算多区域覆盖的基本群
    cover: {U_i: G_i} 区域到基本群的映射
    intersections: 重叠关系
    """
    # 构造自由积
    F = FreeProduct(*cover.values())

    # 添加关系：重叠区域的识别
    relations = []
    for (Ui, Uj), Gij in intersections.items():
        Gi, Gj = cover[Ui], cover[Uj]
        # 添加关系：Gij在Gi和Gj中的像相等
        for g in Gij.generators:
            rel = embed(Gi, g) * embed(Gj, g).inverse()
            relations.append(rel)

    return F / relations
```

---

## 五、范畴表征（抽象）

### 5.1 范畴视角

```text
Seifert-van Kampen = 余极限（colimit）

    G₁ ──→ G₁₂ ←── G₂
    │              │
    │              │
    ↓              ↓
    G₁₃ ←── G₃ ──→ G₂₃
    │              │
    └──────→ G ────┘

在群范畴中的余极限
```

### 5.2 群胚版本

更现代的表述使用基本群胚（fundamental groupoid）

### 5.3 推广

- 高阶同伦群：更复杂
- ∞-范畴：现代同伦论框架

---

## 关联定理

| 定理 | 关系 |
|------|------|
| **van Kampen定理** | 两个开集的特殊情形 |
| **覆盖空间** | 基本群的应用 |

---

**状态**: ✅ 完成
