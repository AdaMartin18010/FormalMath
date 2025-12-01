# L'Hôpital法则 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 微积分
**难度**: L1

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | L'Hôpital法则 |
| **领域** | 微积分 |
| **发现者** | L'Hôpital, Johann Bernoulli |
| **前置知识** | 极限、导数 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**L'Hôpital法则**：若lim f(x) = lim g(x) = 0（或∞），且lim f'(x)/g'(x)存在，则：

$$\lim_{x \to a} \frac{f(x)}{g(x)} = \lim_{x \to a} \frac{f'(x)}{g'(x)}$$

---

## 二、几何表征（可视化）

```text
0/0型：用切线斜率比代替函数值比

    f(x)/g(x) → f'(x)/g'(x)
```

---

## 三、直觉表征（类比）

> **L'Hôpital**：当分子分母都趋于0时，比较它们"趋近0的速度"

---

## 四、计算表征（算法）

```python
def lhopital(f, g, a, max_iter=10):
    for _ in range(max_iter):
        if f(a) != 0 or g(a) != 0:
            return f(a) / g(a)
        f, g = derivative(f), derivative(g)
    return None
```

---

## 五、范畴表征（抽象）

L'Hôpital是Taylor展开的推论：比较各阶导数项。

---

**状态**: ✅ 完成
