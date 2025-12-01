# Taylor定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 微积分
**难度**: L1

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Taylor定理 |
| **领域** | 微积分 |
| **发现者** | Brook Taylor (1715) |
| **前置知识** | 导数、多项式逼近 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Taylor定理**：若f在a点n+1次可导，则：

$$f(x) = \sum_{k=0}^n \frac{f^{(k)}(a)}{k!}(x-a)^k + R_n(x)$$

其中Rₙ是余项（Lagrange/Peano形式）。

---

## 二、几何表征（可视化）

```text
函数f被多项式逼近：

    f(x) ≈ f(a) + f'(a)(x-a) + f''(a)(x-a)²/2 + ...
```

---

## 三、直觉表征（类比）

> **Taylor**：光滑函数在局部"像多项式"

---

## 四、计算表征（算法）

```python
def taylor_approx(f_derivs, a, x, n):
    from math import factorial
    return sum(f_derivs[k] * (x-a)**k / factorial(k) for k in range(n+1))
```

---

## 五、范畴表征（抽象）

Taylor展开是函数在形式幂级数环中的像，是解析函数理论的基础。

---

**状态**: ✅ 完成
