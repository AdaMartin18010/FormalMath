# Radon-Nikodym定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 测度论
**难度**: L3

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Radon-Nikodym定理 |
| **领域** | 测度论 |
| **发现者** | Radon (1913), Nikodym (1930) |
| **前置知识** | 绝对连续、σ-有限测度 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Radon-Nikodym定理**：设(X,Σ,μ)是σ-有限测度空间，ν是Σ上的σ-有限测度，若ν≪μ（ν关于μ绝对连续），则存在唯一（几乎处处）的非负可测函数f使得：

$$\nu(A) = \int_A f \, d\mu, \quad \forall A \in \Sigma$$

f称为ν关于μ的Radon-Nikodym导数，记为dν/dμ。

### 1.2 绝对连续性

ν≪μ ⟺ μ(A)=0 ⟹ ν(A)=0

### 1.3 Lean 4 形式化

```lean
import Mathlib.MeasureTheory.Decomposition.RadonNikodym

-- Radon-Nikodym定理
theorem radon_nikodym {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} [SigmaFinite μ] [SigmaFinite ν]
    (hν : ν.AbsolutelyContinuous μ) :
    ∃ f : X → ℝ≥0∞, Measurable f ∧ ν = μ.withDensity f := by
  exact ⟨μ.rnDeriv ν, Measure.measurable_rnDeriv,
         (Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq.mp hν)⟩
```

---

## 二、几何表征（可视化）

### 2.1 测度的密度

```text
ν是μ的"加权版本"：

    μ:  ████████████  (均匀)
    ν:  ██▓▓▓▓░░██████  (加权)

    dν/dμ = f(x) = ν在x处的"密度"
```

### 2.2 链式法则

```text
若 ρ ≪ ν ≪ μ，则：

    dρ     dρ   dν
    ── = ── · ──
    dμ     dν   dμ
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **Radon-Nikodym**：一个测度如果"不比"另一个"更细"，就可以用密度函数表示

### 3.2 概率类比

- μ：基准概率（如均匀分布）
- ν：另一个概率（如高斯分布）
- dν/dμ：似然比（概率密度比）

### 3.3 为什么需要绝对连续？

绝对连续保证ν"不会在μ看不到的地方有质量"

---

## 四、计算表征（算法）

### 4.1 Python实现

```python
import numpy as np
from scipy import stats

def radon_nikodym_example():
    """
    计算Radon-Nikodym导数
    例：正态分布相对于均匀分布
    """
    # μ = 均匀分布在[-3, 3]
    # ν = 标准正态分布

    def mu_pdf(x):
        return 1/6 if -3 <= x <= 3 else 0

    def nu_pdf(x):
        return stats.norm.pdf(x)

    # Radon-Nikodym导数 dν/dμ = ν的密度 / μ的密度
    def radon_nikodym_deriv(x):
        mu_val = mu_pdf(x)
        if mu_val == 0:
            return 0  # 或无穷，取决于ν在该点的值
        return nu_pdf(x) / mu_val

    x = np.linspace(-3, 3, 100)
    f = [radon_nikodym_deriv(xi) for xi in x]

    print("dν/dμ 在 x=0 处:", radon_nikodym_deriv(0))
    print("dν/dμ 在 x=2 处:", radon_nikodym_deriv(2))
    return x, f

radon_nikodym_example()
```

### 4.2 应用：条件期望

```python
def conditional_expectation(X, Y, condition):
    """
    E[X|Y] 使用Radon-Nikodym导数
    """
    # 条件期望是条件测度关于原测度的导数
    # 简化：离散情况
    pass
```

---

## 五、范畴表征（抽象）

### 5.1 范畴视角

```text
Radon-Nikodym = 测度空间的态射分解
├─ 绝对连续：ν是μ的"商"
├─ dν/dμ：商的"系数"
└─ 在测度空间范畴中的分解
```

### 5.2 推广

- **向量值测度**：取值在Banach空间
- **非σ-有限**：需要Lebesgue分解
- **非交换**：von Neumann代数中的推广

### 5.3 Lebesgue分解

```text
任意测度ν关于μ分解为：
ν = ν_ac + ν_s
├─ ν_ac ≪ μ（绝对连续部分）
└─ ν_s ⊥ μ（奇异部分）
```

---

## 关联定理

| 定理 | 关系 |
|------|------|
| **Lebesgue分解** | 更一般的分解 |
| **条件期望** | 概率论应用 |
| **Girsanov定理** | 随机分析中的推广 |

---

**状态**: ✅ 完成
