# Noether定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 数学物理/变分法
**难度**: L2

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Noether定理 |
| **领域** | 数学物理/变分法 |
| **发现者** | Emmy Noether (1918) |
| **前置知识** | Lagrange力学、对称性、守恒律 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Noether定理**：若作用量S = ∫L dt在连续对称变换下不变，则存在守恒量。

设δq = εξ(q,t)是无穷小变换，若δS = 0，则：
$$Q = \frac{\partial L}{\partial \dot{q}} \xi - H\tau \quad \text{是守恒量}$$

其中τ是时间变换参数。

### 1.2 基本对应

| 对称性 | 守恒量 |
|--------|--------|
| 时间平移 | 能量 |
| 空间平移 | 动量 |
| 旋转 | 角动量 |

### 1.3 形式化表述

```lean
-- Noether定理（概念性）
theorem noether {M : Type*} [SmoothManifold M]
    (L : TangentBundle M → ℝ) -- Lagrangian
    (X : VectorField M) -- 对称生成元
    (hX : X.IsSymmetry L) : -- X是L的对称性
    ∃ Q : M → ℝ, IsConserved Q L := by
  sorry  -- 需要变分学形式化
```

---

## 二、几何表征（可视化）

### 2.1 对称性与守恒

```text
        对称性              守恒量
          │                   │
    时间平移不变 ─────────→ 能量守恒
    空间平移不变 ─────────→ 动量守恒
    旋转不变 ──────────────→ 角动量守恒
```

### 2.2 作用量曲面

```text
配置空间中的路径：
    q
    ↑
    │    ╱ 物理路径
    │  ╱
    │╱   对称变换后
    └──────────→ t

两条路径给出相同的作用量
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **Noether定理**：每一种对称性都对应一个不变的物理量

### 3.2 节省类比

- 对称性：系统"不关心"某些变化
- 守恒量：因为"不关心"，所以"不变"
- 例：系统不关心今天还是明天 ⟹ 能量守恒

### 3.3 为什么重要？

统一了物理学中所有守恒律的来源

---

## 四、计算表征（算法）

### 4.1 Python实现

```python
import sympy as sp
from sympy import symbols, Function, diff, simplify

def noether_conserved_quantity(L, q, t, xi, tau=0):
    """
    计算Noether守恒量
    L: Lagrangian
    q: 广义坐标
    t: 时间
    xi: 坐标变换 δq = ε*xi
    tau: 时间变换 δt = ε*tau
    """
    qdot = sp.diff(q, t)

    # 守恒量 Q = (∂L/∂qdot) * xi - H * tau
    # 其中 H = qdot * ∂L/∂qdot - L

    dL_dqdot = sp.diff(L, qdot)
    H = qdot * dL_dqdot - L

    Q = dL_dqdot * xi - H * tau
    return simplify(Q)

# 示例：自由粒子 L = (1/2)m*v²
t = symbols('t')
m = symbols('m', positive=True)
x = Function('x')(t)
v = sp.diff(x, t)

L = sp.Rational(1, 2) * m * v**2

# 空间平移对称性: δx = ε (xi = 1, tau = 0)
Q_momentum = noether_conserved_quantity(L, x, t, xi=1, tau=0)
print(f"空间平移守恒量（动量）: {Q_momentum}")

# 时间平移对称性: δt = ε (xi = 0, tau = 1)
Q_energy = noether_conserved_quantity(L, x, t, xi=0, tau=1)
print(f"时间平移守恒量（能量）: {simplify(-Q_energy)}")
```

### 4.2 多自由度系统

```python
def noether_multi_dof(L, qs, t, xis):
    """多自由度系统的Noether守恒量"""
    Q = 0
    for q, xi in zip(qs, xis):
        qdot = sp.diff(q, t)
        Q += sp.diff(L, qdot) * xi
    return simplify(Q)
```

---

## 五、范畴表征（抽象）

### 5.1 范畴视角

```text
Noether定理 = Lie群作用与不变量
├─ 对称群G作用于配置空间M
├─ L在G作用下不变
├─ Lie代数g → 守恒量（矩映射）
└─ 范畴化：辛约化
```

### 5.2 现代几何

```text
辛几何视角：
├─ 相空间(M, ω)是辛流形
├─ Hamilton函数H生成流
├─ 对称性 ⟺ Poisson括号{H, Q} = 0
└─ 矩映射μ: M → g*
```

### 5.3 推广

- **量子Noether**：算符对易
- **场论Noether**：连续守恒律
- **规范理论**：局部对称性

---

## 关联定理

| 定理 | 关系 |
|------|------|
| **Euler-Lagrange方程** | 运动方程 |
| **Hamilton力学** | 等价形式 |
| **矩映射** | 现代推广 |

---

**状态**: ✅ 完成
