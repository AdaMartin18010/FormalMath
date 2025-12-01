# Galois基本定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 域论/Galois理论
**难度**: L3

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Galois基本定理 |
| **领域** | 域论 |
| **发现者** | Évariste Galois (1832) |
| **前置知识** | 域扩张、自同构群 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Galois基本定理**：设L/K是Galois扩张，G = Gal(L/K)，则：

- 中间域E ↔ 子群H ⊂ G的对应是反序双射
- [L:E] = |H|，[E:K] = [G:H]
- E/K正规 ⟺ H正规于G

---

## 二、几何表征（可视化）

```text
域格                  群格
L ──────────── {e}
│              │
E ──────────── H
│              │
K ──────────── G

反序对应
```

---

## 三、直觉表征（类比）

> **Galois基本定理**：中间域与对称性子群一一对应

---

## 四、计算表征（算法）

```python
def galois_correspondence(L, K, G):
    # 计算所有中间域 ↔ 所有子群
    subgroups = all_subgroups(G)
    intermediate_fields = [fixed_field(H, L) for H in subgroups]
    return dict(zip(subgroups, intermediate_fields))
```

---

## 五、范畴表征（抽象）

Galois对应是格反同构，连接域扩张与群论。

---

**状态**: ✅ 完成
