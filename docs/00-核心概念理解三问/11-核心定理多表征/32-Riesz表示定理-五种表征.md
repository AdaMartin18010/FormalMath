---
msc_primary: "46C05"
msc_secondary: ["28C05"]
---

# Riesz表示定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 泛函分析/测度论
**难度**: L2

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Riesz表示定理 |
| **领域** | 泛函分析/测度论 |
| **发现者** | Frigyes Riesz (1909) |
| **前置知识** | Hilbert空间、正则Borel测度 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述（Hilbert空间版本）

**Riesz表示定理**：设H是Hilbert空间，f: H→ℂ是有界线性泛函，则存在唯一的y∈H使得：

$$f(x) = \langle x, y \rangle, \quad \forall x \in H$$

且 ‖f‖ = ‖y‖。

### 1.2 测度版本

设X是局部紧Hausdorff空间，φ: C_c(X)→ℂ是正线性泛函，则存在唯一的正则Borel测度μ使得：

$$\phi(f) = \int_X f \, d\mu$$

### 1.3 Lean 4 形式化

```lean
import Mathlib.Analysis.InnerProductSpace.Dual

-- Riesz表示定理（Hilbert空间）
theorem riesz_representation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (f : H →L[ℂ] ℂ) :
    ∃! y : H, ∀ x : H, f x = ⟪x, y⟫ := by
  exact InnerProductSpace.toDualEquiv.surjective f
```

---

## 二、几何表征（可视化）

### 2.1 泛函的几何表示

```text
Hilbert空间H中：

    f(x) = ⟨x, y⟩

    x ───→ y的方向上的投影 × ‖y‖

    y是f的"表示元"
```

### 2.2 正交分解

```text
H = ker(f) ⊕ span{y}

    │
    │   y
    │  ╱
    │ ╱  f(x) = ⟨x,y⟩
    │╱
    ├────────ker(f)
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **Riesz表示定理**：Hilbert空间上的每个"线性测量"都可以用与某个向量的内积来表示

### 3.2 投影类比

- f：测量向量x在某方向上的"分量"
- y：那个方向对应的向量
- ⟨x,y⟩：x在y方向上的投影长度 × ‖y‖

### 3.3 为什么重要？

H与H*是等距同构的，对偶空间非常具体

---

## 四、计算表征（算法）

### 4.1 Python实现

```python
import numpy as np

def riesz_representation(f_values, basis):
    """
    找Riesz表示元y
    f_values: f在基向量上的值
    basis: 正交归一基
    """
    # 在正交归一基下，y = Σ conj(f(eᵢ)) eᵢ
    y = sum(np.conj(f_values[i]) * basis[i] for i in range(len(basis)))
    return y

# 示例：ℂⁿ中
n = 3
basis = [np.eye(n)[i] for i in range(n)]

# 定义泛函 f(x) = 2x₁ + 3x₂ + x₃
f_values = [2, 3, 1]

y = riesz_representation(f_values, basis)
print(f"Riesz表示元: y = {y}")

# 验证
x = np.array([1, 2, 3])
f_x = sum(f_values[i] * x[i] for i in range(n))
inner_product = np.dot(x, np.conj(y))
print(f"f(x) = {f_x}, ⟨x,y⟩ = {inner_product}")
```

### 4.2 测度版本的应用

```python
from scipy import integrate

def riesz_measure_example():
    """
    正线性泛函 → 测度
    例：φ(f) = ∫₀¹ f(x)dx 对应Lebesgue测度
    """
    def phi(f, a=0, b=1):
        return integrate.quad(f, a, b)[0]

    # 验证：φ(1) = 1 (常函数1)
    print(f"φ(1) = {phi(lambda x: 1)}")

    # φ(x) = 1/2
    print(f"φ(x) = {phi(lambda x: x)}")

    # 这对应于[0,1]上的Lebesgue测度

riesz_measure_example()
```

---

## 五、范畴表征（抽象）

### 5.1 范畴视角

```text
Riesz表示 = Hilbert空间的自对偶性
├─ H ≅ H* (等距同构)
├─ 对偶函子在Hilbert空间上"平凡"
└─ 内积给出自然同构
```

### 5.2 推广

- **Banach空间**：对偶更复杂，不一定自对偶
- **局部凸空间**：各种对偶理论
- **C*-代数**：Riesz的非交换推广

### 5.3 泛函分析中的地位

```text
Riesz表示定理是核心：
├─ 谱定理的基础
├─ 量子力学的数学基础
└─ 变分法的理论根基
```

---

## 关联定理

| 定理 | 关系 |
|------|------|
| **Lax-Milgram** | 双线性形式版本 |
| **谱定理** | 应用 |
| **Radon-Nikodym** | 测度版本的推广 |

---

**状态**: ✅ 完成
