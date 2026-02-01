---
msc_primary: "54C30"
msc_secondary: ["54A05"]
---

# Urysohn引理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 点集拓扑
**难度**: L2

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Urysohn引理 |
| **领域** | 点集拓扑 |
| **发现者** | Pavel Urysohn (1925) |
| **前置知识** | 正规空间、连续函数 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Urysohn引理**：设X是正规拓扑空间，A、B是X中不相交的闭集，则存在连续函数f: X → [0,1]，使得f|_A = 0，f|_B = 1。

$$\exists f \in C(X, [0,1]): f(A) = \{0\}, f(B) = \{1\}$$

### 1.2 等价表述

正规空间可以用连续函数"分离"闭集。

### 1.3 Lean 4 形式化

```lean
import Mathlib.Topology.UrysohnsLemma

theorem exists_continuous_zero_one_of_closed {X : Type*}
    [TopologicalSpace X] [NormalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) :
    ∃ f : X → ℝ, Continuous f ∧ f '' A ⊆ {0} ∧ f '' B ⊆ {1}
        ∧ Set.range f ⊆ Set.Icc (0 : ℝ) 1 := by
  exact exists_continuous_zero_one_of_closed hA hB hAB
```

---

## 二、几何表征（可视化）

### 2.1 分离函数

```text
    X空间
    │
    │  f(x) = 0
    A├──────────┐
    │          │  f连续过渡
    │          │
    │          │  f(x) = 1
    └──────────┴B

f在A上为0，在B上为1，中间连续过渡
```

### 2.2 应用：Tietze扩张

```text
闭集A上的连续函数g
    ↓ (Urysohn构造)
整个空间X上的连续函数f
    ↓
f|_A = g (保持原函数)
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **Urysohn引理**：在"足够好"的空间中，可以用连续函数把两个分离的区域"标记"为0和1

### 3.2 温度类比

- A区域：温度0°C
- B区域：温度1°C
- 中间：温度连续变化（0到1之间）

### 3.3 为什么需要正规性？

正规性保证有"足够空间"来构造连续过渡

---

## 四、计算表征（算法）

### 4.1 Python实现（简化：度量空间）

```python
import numpy as np

def urysohn_function(x, A, B, metric):
    """
    在度量空间中构造Urysohn函数
    f(x) = d(x,A) / (d(x,A) + d(x,B))
    """
    d_A = min(metric(x, a) for a in A)
    d_B = min(metric(x, b) for b in B)

    if d_A + d_B == 0:
        return 0.5  # 边界情况
    return d_A / (d_A + d_B)

# 示例：ℝ²上的分离
def euclidean_metric(x, y):
    return np.sqrt(sum((xi - yi)**2 for xi, yi in zip(x, y)))

A = [(0, 0)]
B = [(2, 2)]

x_test = (1, 1)
f_value = urysohn_function(x_test, A, B, euclidean_metric)
print(f"f({x_test}) = {f_value:.3f}")
```

---

## 五、范畴表征（抽象）

### 5.1 范畴视角

```text
Urysohn引理 = 分离公理 + 连续函数存在性
├─ 正规空间：T4分离公理
├─ 连续函数：拓扑空间到ℝ的态射
└─ 分离性质：用函数"区分"集合
```

### 5.2 万有性质

Urysohn函数是"最自然的"分离函数（在某种意义下）

### 5.3 推广

- Tietze扩张定理：闭集上函数可扩张到全空间
- 单位分解：更精细的分离技术

---

## 关联定理

| 定理 | 关系 |
|------|------|
| **Tietze扩张定理** | Urysohn的推广 |
| **单位分解** | 局部有限版本 |

---

**状态**: ✅ 完成
