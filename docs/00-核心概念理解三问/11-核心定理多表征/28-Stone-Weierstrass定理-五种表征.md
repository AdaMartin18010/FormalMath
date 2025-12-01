# Stone-Weierstrass定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 实分析/泛函分析
**难度**: L2

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Stone-Weierstrass定理 |
| **领域** | 实分析/泛函分析 |
| **发现者** | Weierstrass (1885), Stone (1937) |
| **前置知识** | 紧致空间、连续函数、代数 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Stone-Weierstrass定理**：设K是紧致Hausdorff空间，A ⊂ C(K,ℝ)是包含常函数、分离点的子代数，则A在C(K,ℝ)中稠密（一致范数）。

$$\overline{A} = C(K, \mathbb{R})$$

### 1.2 Weierstrass逼近定理（特例）

多项式在C[a,b]中稠密：
$$\forall f \in C[a,b], \forall \varepsilon > 0, \exists p: \|f - p\|_\infty < \varepsilon$$

### 1.3 Lean 4 形式化

```lean
import Mathlib.Topology.ContinuousFunction.StoneWeierstrass

-- Stone-Weierstrass定理
theorem stone_weierstrass {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (A : Subalgebra ℝ C(X, ℝ))
    (hA_sep : A.SeparatesPoints) (hA_const : (1 : C(X, ℝ)) ∈ A) :
    A.topologicalClosure = ⊤ := by
  exact ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    hA_sep hA_const
```

---

## 二、几何表征（可视化）

### 2.1 多项式逼近

```text
连续函数f被多项式逼近：
    y
    ↑
    │   f(x) ─────
    │  ╱    ╲
    │ ╱  pₙ(x)╲
    │╱          ╲
    └──────────────→ x

多项式pₙ越来越接近f
```

### 2.2 分离点条件

```text
子代数A分离点：

    K:  x₁ ≠ x₂
         │
    存在 f ∈ A 使得 f(x₁) ≠ f(x₂)
         │
    A能"区分"K中的不同点
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **Stone-Weierstrass**：如果一族函数"足够丰富"（分离点+含常数+闭于运算），就能逼近任意连续函数

### 3.2 乐高类比

- A中的函数 = 基础积木
- 分离点 = 积木种类足够多
- 含常数 = 有平地积木
- 代数闭 = 可以组合积木
- 结论：能搭建任何形状

### 3.3 为什么需要紧致？

紧致保证一致收敛，否则只有逐点收敛

---

## 四、计算表征（算法）

### 4.1 Python实现：Bernstein多项式

```python
import numpy as np
from scipy.special import comb

def bernstein_approx(f, n, x):
    """
    Bernstein多项式逼近
    Bₙ(f)(x) = Σ f(k/n) C(n,k) xᵏ (1-x)ⁿ⁻ᵏ
    """
    result = 0
    for k in range(n + 1):
        coeff = comb(n, k, exact=True) * (x ** k) * ((1 - x) ** (n - k))
        result += f(k / n) * coeff
    return result

# 验证：逼近 |x - 0.5|
f = lambda x: np.abs(x - 0.5)
x = np.linspace(0, 1, 100)

for n in [5, 10, 50, 100]:
    approx = np.array([bernstein_approx(f, n, xi) for xi in x])
    error = np.max(np.abs(f(x) - approx))
    print(f"n={n}: max error = {error:.6f}")
```

### 4.2 三角多项式逼近

```python
def fourier_approx(f, n, x):
    """Fourier级数逼近周期函数"""
    from scipy.integrate import quad

    a0 = quad(f, 0, 2*np.pi)[0] / np.pi
    result = a0 / 2

    for k in range(1, n + 1):
        ak = quad(lambda t: f(t) * np.cos(k * t), 0, 2*np.pi)[0] / np.pi
        bk = quad(lambda t: f(t) * np.sin(k * t), 0, 2*np.pi)[0] / np.pi
        result += ak * np.cos(k * x) + bk * np.sin(k * x)

    return result
```

---

## 五、范畴表征（抽象）

### 5.1 范畴视角

```text
Stone-Weierstrass = C(K)的代数结构决定K
├─ K紧致Hausdorff ⟺ C(K)是交换C*-代数
├─ Gelfand对偶：K ↔ C(K)
└─ 分离点子代数→全体的稠密性
```

### 5.2 推广

- **复版本**：自伴子代数在C(K,ℂ)中稠密
- **局部紧版本**：C₀(X)上的版本
- **非交换版本**：C*-代数的稠密性

### 5.3 Gelfand表示

每个交换C*-代数同构于某C(K)，Stone-Weierstrass刻画其子代数

---

## 关联定理

| 定理 | 关系 |
|------|------|
| **Weierstrass逼近** | 特例 |
| **Mercer定理** | 核函数展开 |
| **Gelfand对偶** | 范畴化推广 |

---

**状态**: ✅ 完成
