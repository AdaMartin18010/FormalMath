# Picard-Lindelöf定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 微分方程
**难度**: L2

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Picard-Lindelöf定理（存在唯一性定理） |
| **领域** | 微分方程 |
| **发现者** | Picard, Lindelöf |
| **前置知识** | ODE、Lipschitz条件 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Picard-Lindelöf定理**：设f(t,y)关于y满足Lipschitz条件，则初值问题：

$$y' = f(t, y), \quad y(t_0) = y_0$$

在t₀附近有唯一解。

---

## 二、几何表征（可视化）

```text
Lipschitz条件保证解曲线不相交：

    y
    ↑
    │    唯一解曲线
    │   ╱
    │  ╱
    │●(t₀,y₀)
    └──────────→ t
```

---

## 三、直觉表征（类比）

> **Picard-Lindelöf**：如果方向场"够规则"，从任一点出发只有一条轨迹

---

## 四、计算表征（算法）

```python
def picard_iteration(f, t0, y0, n_iter=10):
    y = lambda t: y0
    for _ in range(n_iter):
        y_prev = y
        y = lambda t: y0 + integrate(lambda s: f(s, y_prev(s)), t0, t)
    return y
```

---

## 五、范畴表征（抽象）

Picard-Lindelöf使用Banach不动点定理，Picard迭代是压缩映射。

---

**状态**: ✅ 完成
