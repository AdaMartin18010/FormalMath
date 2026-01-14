# Fubini定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 测度论
**难度**: L2

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Fubini定理 / Fubini-Tonelli定理 |
| **领域** | 测度论 |
| **发现者** | Guido Fubini (1907), Leonida Tonelli |
| **前置知识** | Lebesgue积分、乘积测度 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Fubini定理**：设(X,μ)和(Y,ν)是σ-有限测度空间，f: X×Y→ℝ可积，则：

$$\int_{X \times Y} f \, d(\mu \times \nu) = \int_X \leqqft( \int_Y f(x,y) \, d\nu(y) \right) d\mu(x) = \int_Y \leqqft( \int_X f(x,y) \, d\mu(x) \right) d\nu(y)$$

### 1.2 Tonelli定理（非负版本）

若f ≥ 0可测，则上述等式成立（不要求可积）。

### 1.3 Lean 4 形式化

```lean
import Mathlib.MeasureTheory.Integral.Prod

-- Fubini定理
theorem fubini {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SigmaFinite ν]
    {f : X × Y → ℝ} (hf : Integrable f (μ.prod ν)) :
    ∫ p, f p ∂(μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  exact integral_prod f hf
```

---

## 二、几何表征（可视化）

### 2.1 切片积分

```text
X×Y上的积分 = 沿Y方向切片，再沿X方向积分

    Y
    ↑
    │ ┌───┐
    │ │ f │  ← 固定x，沿y积分
    │ └───┘
    └──────────→ X
       ↑
       沿x积分切片的积分
```

### 2.2 积分顺序

```text
∬f(x,y) dxdy = ∫(∫f(x,y)dy)dx = ∫(∫f(x,y)dx)dy

     │           │             │
     └───────────┴─────────────┘
            三者相等
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **Fubini定理**：多重积分可以"逐层"计算，积分顺序可以交换

### 3.2 体积类比

- 计算立体体积：可以先切成薄片，计算每片面积，再求和
- 无论横切还是竖切，结果相同

### 3.3 为什么需要可积？

可积保证所有切片的积分都有意义，否则可能出现问题

---

## 四、计算表征（算法）

### 4.1 Python实现

```python
import numpy as np
from scipy import integrate

def fubini_verify(f, x_range, y_range):
    """
    验证Fubini定理：比较两种积分顺序
    """
    # 方法1：先对y积分，再对x积分
    def inner_y(x):
        return integrate.quad(lambda y: f(x, y), y_range[0], y_range[1])[0]
    result1 = integrate.quad(inner_y, x_range[0], x_range[1])[0]

    # 方法2：先对x积分，再对y积分
    def inner_x(y):
        return integrate.quad(lambda x: f(x, y), x_range[0], x_range[1])[0]
    result2 = integrate.quad(inner_x, y_range[0], y_range[1])[0]

    # 方法3：直接二重积分
    result3 = integrate.dblquad(f, y_range[0], y_range[1],
                                  x_range[0], x_range[1])[0]

    print(f"∫(∫f dy)dx = {result1:.6f}")
    print(f"∫(∫f dx)dy = {result2:.6f}")
    print(f"∬f dxdy = {result3:.6f}")

    return result1, result2, result3

# 示例：f(x,y) = x*y
f = lambda x, y: x * y
fubini_verify(f, [0, 1], [0, 1])
```

### 4.2 反例（不可积时）

```python
def fubini_counterexample():
    """
    展示不满足Fubini条件时的问题
    f(x,y) = (x²-y²)/(x²+y²)² 在[0,1]×[0,1]上
    """
    def f(x, y):
        if x == 0 and y == 0:
            return 0
        return (x**2 - y**2) / (x**2 + y**2)**2

    # 先对y积分：可能得到+∞
    # 先对x积分：可能得到-∞
    # 两个顺序结果不同！
    print("反例：积分顺序影响结果（函数不可积）")
```

---

## 五、范畴表征（抽象）

### 5.1 范畴视角

```text
Fubini定理 = 乘积测度的泛函性质
├─ 乘积测度μ×ν是μ和ν的"张量积"
├─ 积分交换 ⟺ 张量积的对称性
└─ 在适当的测度空间范畴中成立
```

### 5.2 推广

- **多重积分**：任意有限个测度空间
- **条件期望**：概率论中的推广
- **核积分**：更一般的积分变换

### 5.3 Tonelli vs Fubini

```text
Tonelli：f ≥ 0 可测 ⟹ 等式成立（可能是∞）
Fubini：f可积 ⟹ 等式成立（有限值）
```

---

## 关联定理

| 定理 | 关系 |
|------|------|
| **Tonelli定理** | 非负版本 |
| **卷积定理** | 应用 |
| **变量替换** | 相关技巧 |

---

**状态**: ✅ 完成
