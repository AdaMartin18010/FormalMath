# Weyl特征标公式 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 表示论
**难度**: L3

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Weyl特征标公式 |
| **领域** | 表示论 |
| **发现者** | Hermann Weyl (1925-1926) |
| **前置知识** | Lie群、不可约表示、最高权 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Weyl特征标公式**：设G是紧连通Lie群，Vλ是最高权λ的不可约表示，则特征标：

$$\chi_\lambda(e^H) = \frac{\sum_{w \in W} \det(w) e^{w(\lambda+\rho)(H)}}{\sum_{w \in W} \det(w) e^{w(\rho)(H)}}$$

其中W是Weyl群，ρ是半根和。

---

## 二、几何表征（可视化）

```text
权λ → 不可约表示Vλ → 特征标χλ

    Weyl群轨道求和
         ↓
    对称化公式
```

---

## 三、直觉表征（类比）

> **Weyl公式**：表示的"指纹"（特征标）由权的Weyl群对称性完全确定

---

## 四、计算表征（算法）

```python
def weyl_character(highest_weight, weyl_group, rho, H):
    numerator = sum(det(w) * exp(w(highest_weight + rho)(H))
                   for w in weyl_group)
    denominator = sum(det(w) * exp(w(rho)(H))
                     for w in weyl_group)
    return numerator / denominator
```

---

## 五、范畴表征（抽象）

Weyl公式是表示环R(G)中的结构常数，与K理论相关。

---

**状态**: ✅ 完成
