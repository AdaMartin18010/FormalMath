---
msc_primary: "20B99"
msc_secondary: ["20A05"]
---

# Cayley定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 群论
**难度**: L1-L2

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Cayley定理 |
| **领域** | 抽象代数、群论 |
| **发现者** | Arthur Cayley (1854) |
| **前置知识** | 群、置换、同构 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Cayley定理**：每个群 G 同构于某个置换群的子群。

$$\phi: G \hookrightarrow \text{Sym}(G), \quad \phi(g) = \lambda_g$$

其中 λ_g(x) = gx 是左乘置换。

### 1.2 Lean 4 形式化

```lean
-- Cayley定理
theorem cayley (G : Type*) [Group G] :
    ∃ f : G →* Equiv.Perm G, Function.Injective f := by
  use MulAction.toPerm
  exact MulAction.toPerm_injective G
```

### 1.3 证明要点

```text
λ_g(x) = gx 是双射（逆为λ_{g⁻¹}）
φ(gh) = λ_{gh} = λ_g ∘ λ_h（同态）
φ(g) = φ(h) ⟹ g = h（单射）
```

---

## 二、几何表征（可视化）

### 2.1 Z/3Z 嵌入 S₃

```text
λ_0: (0,1,2) → (0,1,2)  恒等
λ_1: (0,1,2) → (1,2,0)  三循环
λ_2: (0,1,2) → (2,0,1)  三循环
```

### 2.2 Cayley图

```text
Z/4Z 的 Cayley图：
    0 ──→ 1
    ↑     ↓
    3 ←── 2
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **群 = 打乱自己的方式**

### 3.2 魔方类比

每个魔方操作是群元素，群就是"所有可能的打乱规则"。

---

## 四、计算表征（算法）

```python
def cayley_embedding(elements, op):
    """计算Cayley嵌入"""
    idx = {g: i for i, g in enumerate(elements)}
    return {g: tuple(idx[op(g, x)] for x in elements)
            for g in elements}

# Z/4Z
z4 = [0, 1, 2, 3]
emb = cayley_embedding(z4, lambda a,b: (a+b)%4)
for g, p in emb.items():
    print(f"λ_{g}: {p}")
```

---

## 五、范畴表征（抽象）

群G视为单对象范畴BG，Cayley嵌入是Yoneda嵌入的特例：
$$BG \hookrightarrow [BG^{op}, \mathbf{Set}]$$

---

## 关联定理

| 定理 | 关系 |
|------|------|
| Yoneda引理 | 范畴化推广 |
| 正则表示 | 线性化版本 |

---

**状态**: ✅ 完成
