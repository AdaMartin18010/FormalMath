# Cauchy积分公式 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 复分析
**难度**: L2

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Cauchy积分公式 |
| **领域** | 复分析 |
| **发现者** | Augustin Cauchy (1831) |
| **前置知识** | 解析函数、围道积分 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Cauchy积分公式**：设 f 在单连通区域 D 上解析，C 是 D 内的简单闭曲线（正向），z₀ 在 C 内部，则：

$$f(z_0) = \frac{1}{2\pi i} \oint_C \frac{f(z)}{z - z_0} dz$$

**高阶导数**：
$$f^{(n)}(z_0) = \frac{n!}{2\pi i} \oint_C \frac{f(z)}{(z - z_0)^{n+1}} dz$$

### 1.2 Lean 4 形式化

```lean
import Mathlib.Analysis.Complex.CauchyIntegral

-- Cauchy积分公式
theorem cauchy_integral_formula {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (closedBall z₀ r))
    (hz : z ∈ ball z₀ r) :
    f z = (1 / (2 * π * I)) * ∮ ζ in C(z₀, r), f ζ / (ζ - z) := by
  exact Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul hf hr hz
```

### 1.3 证明要点

```text
        [Cauchy公式证明]
              │
    考虑 g(z) = f(z)/(z-z₀)
              │
    g 在 z₀ 有奇点，其他地方解析
              │
    用小圆 Cε 绕 z₀
              │
    ∮_C g - ∮_Cε g = 0 (Cauchy定理)
              │
    ε → 0: ∮_Cε g → 2πi·f(z₀)
```

---

## 二、几何表征（可视化）

### 2.1 核心图示

```text
        [Cauchy积分公式]

    ┌──────────────────────┐
    │                      │
    │   C (围道)           │
    │  ╭──────────╮        │
    │  │          │        │
    │  │    •z₀   │←f(z₀)由边界值确定
    │  │          │        │
    │  ╰──────────╯        │
    │                      │
    └──────────────────────┘

    内部值 = 边界值的加权平均
```

### 2.2 平均值性质

```text
    圆上取平均：

         ∫₀^2π f(z₀ + re^{iθ}) dθ
    f(z₀) = ─────────────────────────
                    2π

    解析函数值 = 周围值的平均
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **Cauchy公式**：解析函数的内部值完全由边界值决定——"知边界则知内部"

### 3.2 温度场类比

```text
稳态热传导：
├─ 边界温度固定
├─ 内部温度满足Laplace方程
├─ 内部任意点温度 = 边界加权平均
└─ 这正是Cauchy公式的实部！
```

### 3.3 为什么成立？

```text
解析性 = 无穷可微 + Cauchy-Riemann

关键：∂f/∂z̄ = 0

积分只依赖边界（类似保守场）
内部信息"编码"在边界上
```

---

## 四、计算表征（算法）

### 4.1 Python实现

```python
import numpy as np

def cauchy_integral(f, z0, r, n_points=1000):
    """
    数值计算Cauchy积分

    f(z0) = (1/2πi) ∮ f(z)/(z-z0) dz
    """
    theta = np.linspace(0, 2*np.pi, n_points, endpoint=False)
    z = z0 + r * np.exp(1j * theta)
    dz = 1j * r * np.exp(1j * theta) * (2*np.pi / n_points)

    integrand = f(z) / (z - z0)
    integral = np.sum(integrand * dz)

    return integral / (2 * np.pi * 1j)

# 验证：f(z) = z², z0 = 1+i
f = lambda z: z**2
z0 = 1 + 1j
r = 0.5

result = cauchy_integral(f, z0, r)
exact = f(z0)

print(f"Cauchy积分结果: {result:.6f}")
print(f"f(z₀) = z₀² = {exact:.6f}")
print(f"误差: {abs(result - exact):.2e}")
```

### 4.2 高阶导数计算

```python
def cauchy_derivative(f, z0, n, r=0.1, n_points=1000):
    """
    用Cauchy公式计算n阶导数

    f^(n)(z0) = n! / (2πi) ∮ f(z)/(z-z0)^{n+1} dz
    """
    theta = np.linspace(0, 2*np.pi, n_points, endpoint=False)
    z = z0 + r * np.exp(1j * theta)
    dz = 1j * r * np.exp(1j * theta) * (2*np.pi / n_points)

    integrand = f(z) / (z - z0)**(n+1)
    integral = np.sum(integrand * dz)

    from math import factorial
    return factorial(n) * integral / (2 * np.pi * 1j)

# f(z) = e^z, 所有导数都是e^z
f = lambda z: np.exp(z)
z0 = 0

print("f(z) = e^z 在 z=0 的导数:")
for n in range(5):
    deriv = cauchy_derivative(f, z0, n)
    print(f"  f^({n})(0) = {deriv.real:.6f} (理论值: 1)")
```

---

## 五、范畴表征（抽象）

### 5.1 层论视角

```text
解析函数构成层 O_X

Cauchy公式说：
├─ 层的截面由边界数据确定
├─ O_X 是"软层"（flabby）的对偶概念
└─ 与上同调的消没有关
```

### 5.2 泛函分析视角

```text
Cauchy核 K(z, ζ) = 1/(2πi(ζ-z))

├─ 是积分算子的核
├─ Bergman核的前身
└─ 再生核Hilbert空间理论
```

### 5.3 与其他定理关系

```text
        [复分析核心定理]
              │
    ┌─────────┼─────────┐
    │         │         │
[Cauchy定理] [积分公式] [留数定理]
∮f=0        f(z₀)=∮    ∮f=2πi·Σres
    │         │         │
    └─────────┴─────────┘
              │
        都源于解析性
```

---

## 六、应用

### 6.1 数学应用

| 应用 | 说明 |
|------|------|
| **Liouville定理** | 有界整函数是常数 |
| **代数基本定理** | 多项式有根 |
| **最大模原理** | 模在边界取最大 |
| **Taylor展开** | 解析函数的级数 |

### 6.2 物理应用

| 应用 | 领域 |
|------|------|
| **电场计算** | 静电学 |
| **流体力学** | 势流理论 |
| **量子力学** | 传播子计算 |

---

## 关联定理

| 定理 | 关系 |
|------|------|
| **Cauchy定理** | 闭路积分为零 |
| **留数定理** | 奇点贡献 |
| **Morera定理** | 逆定理 |
| **Liouville定理** | 推论 |

---

**状态**: ✅ 完成
