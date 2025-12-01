# Burnside引理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 组合学/群论
**难度**: L1

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Burnside引理（轨道计数定理） |
| **领域** | 组合学/群论 |
| **发现者** | Cauchy, Frobenius (误归于Burnside) |
| **前置知识** | 群作用、轨道、稳定子 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Burnside引理**：设G作用在集合X上，则轨道数：

$$|X/G| = \frac{1}{|G|} \sum_{g \in G} |X^g|$$

其中X^g = {x∈X : g·x = x}是g的不动点集。

---

## 二、几何表征（可视化）

```text
计算轨道数 = 平均不动点数

    轨道数 = Σ|不动点| / |G|
```

---

## 三、直觉表征（类比）

> **Burnside**：不同本质对象的数量 = 平均每个对称操作"不动"的对象数

---

## 四、计算表征（算法）

```python
def burnside_count_orbits(G, X, action):
    total_fixed = sum(count_fixed_points(g, X, action) for g in G)
    return total_fixed // len(G)
```

---

## 五、范畴表征（抽象）

Burnside引理是轨道-稳定子定理的统计版本。

---

**状态**: ✅ 完成
