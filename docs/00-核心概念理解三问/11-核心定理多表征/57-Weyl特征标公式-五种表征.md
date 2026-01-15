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

**Weyl特征标公式**：设 $G$ 是紧连通半单Lie群，$V_\lambda$ 是最高权为 $\lambda$ 的不可约表示，则特征标为：

$$\chi_\lambda(e^H) = \frac{\sum_{w \in W} \det(w) e^{w(\lambda+\rho)(H)}}{\sum_{w \in W} \det(w) e^{w(\rho)(H)}}$$

其中：
- $W$ 是Weyl群
- $\rho = \frac{1}{2}\sum_{\alpha \in \Phi^+} \alpha$ 是半根和（$\Phi^+$ 是正根集）
- $H$ 是Cartan子代数的元素
- $\det(w)$ 是 $w$ 的符号（Weyl群的符号表示）

### 1.2 分母公式（Weyl分母公式）

分母可以写成：

$$\sum_{w \in W} \det(w) e^{w(\rho)(H)} = \prod_{\alpha \in \Phi^+} (e^{\alpha(H)/2} - e^{-\alpha(H)/2})$$

### 1.3 形式化表述

$$\left[ G \text{ 紧连通半单Lie群 } \land V_\lambda \text{ 最高权 } \lambda \text{ 的不可约表示 } \right] \Rightarrow \chi_\lambda(e^H) = \frac{\sum_{w \in W} \det(w) e^{w(\lambda+\rho)(H)}}{\sum_{w \in W} \det(w) e^{w(\rho)(H)}}$$

---

## 二、几何表征（可视化）

### 2.1 权空间分解

```text
权λ → 不可约表示Vλ → 特征标χλ

    权格
        │
        ├─ λ (最高权)
        ├─ λ - α₁
        ├─ λ - α₁ - α₂
        └─ ...
    
    Weyl群轨道求和
         ↓
    对称化公式
```

### 2.2 Weyl群作用

```text
Weyl群W作用在权格上：

    λ ──w──→ w(λ)
    
    特征标公式：
    分子 = Σ_{w∈W} det(w) e^{w(λ+ρ)}
    分母 = Σ_{w∈W} det(w) e^{w(ρ)}
    
    这是Weyl对称性的体现
```

### 2.3 特征标的对称性

```text
特征标的Weyl对称性：

    χ_λ(e^H) 在Weyl群作用下对称
    
    这反映了表示的对称性
```

---

## 三、直觉表征（类比）

### 3.1 物理类比

> **Weyl公式**：表示的"指纹"（特征标）由权的Weyl群对称性完全确定

**类比1：光谱**

- 特征标 = 光谱
- 权 = 能级
- Weyl群 = 对称性
- Weyl公式 = 光谱的对称性公式

**类比2：晶体结构**

- 表示 = 晶体
- 权 = 原子位置
- Weyl群 = 晶体对称性
- Weyl公式 = 结构的对称性描述

### 3.2 计算类比

**类比**：Weyl公式类似于：
- **Fourier变换**：将对称性转化为公式
- **生成函数**：特征标的生成函数
- **组合恒等式**：对称求和的恒等式

---

## 四、计算表征（算法）

### 4.1 计算特征标

```python
import numpy as np
from itertools import product

def weyl_character_formula(highest_weight, weyl_group, rho, H, root_system):
    """
    计算Weyl特征标公式
    
    参数:
        highest_weight: 最高权 λ
        weyl_group: Weyl群元素列表
        rho: 半根和
        H: Cartan子代数元素
        root_system: 根系统
    
    返回:
        character: 特征标值
    """
    # 计算分子：Σ_{w∈W} det(w) e^{w(λ+ρ)(H)}
    numerator = 0
    for w in weyl_group:
        w_det = weyl_determinant(w)  # det(w)
        w_weight = w.apply(highest_weight + rho)  # w(λ+ρ)
        exponent = np.dot(w_weight, H)
        numerator += w_det * np.exp(exponent)
    
    # 计算分母：Σ_{w∈W} det(w) e^{w(ρ)(H)}
    denominator = 0
    for w in weyl_group:
        w_det = weyl_determinant(w)
        w_rho = w.apply(rho)  # w(ρ)
        exponent = np.dot(w_rho, H)
        denominator += w_det * np.exp(exponent)
    
    character = numerator / denominator
    return character

def weyl_determinant(w):
    """
    计算Weyl群元素的符号
    
    参数:
        w: Weyl群元素
    
    返回:
        det: det(w) = ±1
    """
    # det(w) = (-1)^{反射次数}
    # 简化：假设w是反射的乘积
    return (-1) ** w.reflection_count()

# 例子：SU(2)的情况
# Weyl群 = {id, s}（2个元素）
# 最高权表示：V_n（n维表示）
def su2_character(n, theta):
    """
    SU(2)的特征标（特殊情况）
    
    参数:
        n: 表示维数
        theta: 角度参数
    
    返回:
        character: 特征标值
    """
    # SU(2)的特征标：χ_n(θ) = sin(nθ/2) / sin(θ/2)
    if abs(np.sin(theta/2)) < 1e-10:
        return n  # 极限情况
    return np.sin(n * theta / 2) / np.sin(theta / 2)
```

### 4.2 应用：计算维数

```python
def dimension_via_weyl(highest_weight, root_system):
    """
    使用Weyl维数公式计算表示维数
    
    Weyl维数公式：
    dim V_λ = ∏_{α∈Φ⁺} (λ+ρ, α) / (ρ, α)
    
    参数:
        highest_weight: 最高权
        root_system: 根系统
    
    返回:
        dimension: 表示维数
    """
    rho = compute_rho(root_system)
    positive_roots = root_system.positive_roots()
    
    numerator = 1
    denominator = 1
    
    for alpha in positive_roots:
        inner_lambda_rho = np.dot(highest_weight + rho, alpha)
        inner_rho = np.dot(rho, alpha)
        numerator *= inner_lambda_rho
        denominator *= inner_rho
    
    dimension = numerator // denominator
    return dimension

def compute_rho(root_system):
    """
    计算半根和 ρ
    
    参数:
        root_system: 根系统
    
    返回:
        rho: 半根和
    """
    positive_roots = root_system.positive_roots()
    rho = sum(positive_roots) / 2
    return rho

# 例子：SU(3)的表示
# 可以计算各种不可约表示的维数
```

### 4.3 特征标表

```python
def character_table_via_weyl(group, root_system):
    """
    使用Weyl公式计算特征标表
    
    参数:
        group: Lie群
        root_system: 根系统
    
    返回:
        character_table: 特征标表
    """
    weyl_group = compute_weyl_group(root_system)
    rho = compute_rho(root_system)
    
    # 找到所有支配整权（对应不可约表示）
    dominant_weights = find_dominant_integral_weights(root_system)
    
    character_table = {}
    for weight in dominant_weights:
        # 对每个共轭类，计算特征标
        for H in cartan_elements(group):
            char_value = weyl_character_formula(
                weight, weyl_group, rho, H, root_system
            )
            character_table[(weight, H)] = char_value
    
    return character_table
```

---

## 五、范畴表征（抽象）

### 5.1 表示环

**Weyl特征标公式**在**表示环** $R(G)$ 中的意义：

- **结构常数**：特征标的乘积展开
- **生成元**：基本表示的特征标生成 $R(G)$
- **K理论**：与K理论中的特征标相关

### 5.2 对称函数

在**对称函数理论**中：

- Weyl公式对应Schur函数的公式
- 这是对称函数理论的基础

### 5.3 几何量化

在**几何量化**中：

- Weyl公式对应量子化后的特征标
- 这是几何量化理论的应用

---

## 六、应用实例

### 6.1 经典例子

**例子1**：$SU(2)$ 的表示

- 最高权：$\lambda = n$（$n$ 是非负整数）
- 特征标：$\chi_n(\theta) = \frac{\sin((n+1)\theta/2)}{\sin(\theta/2)}$
- 维数：$\dim V_n = n + 1$

**例子2**：$SU(3)$ 的表示

- 使用Weyl公式计算特征标
- 可以计算各种不可约表示的特征标
- 应用于粒子物理（夸克模型）

**例子3**：$SO(n)$ 的旋量表示

- 使用Weyl公式计算旋量表示的特征标
- 应用于物理中的自旋

### 6.2 物理应用

**例子4**：粒子物理

- 夸克和轻子的表示
- 使用Weyl公式计算粒子多重态
- 这是标准模型的基础

**例子5**：统计物理

- 对称系统的配分函数
- 使用特征标计算
- 这是统计物理的应用

---

## 七、历史背景

### 7.1 发现历史

- **1925-1926年**：Weyl 首次证明
- **现代**：成为表示论的基础
- **应用**：广泛用于物理和数学

### 7.2 现代意义

Weyl特征标公式是：
- Lie群表示论的核心定理
- 物理中对称性分析的工具
- 代数几何和数论的应用

---

## 八、证明思路

### 8.1 标准证明

**证明**（使用几何方法）：

1. **特征标的积分表示**：使用Peter-Weyl定理
2. **Weyl积分公式**：将积分限制到Cartan子群
3. **对称性**：使用Weyl群的对称性
4. **得到公式**：通过计算得到Weyl公式

### 8.2 代数证明

**证明思路**：

- 使用Verma模和BGG分解
- 通过组合方法证明
- 这是更代数的证明

---

## 九、推广与变体

### 9.1 量子群

对于量子群，有量子Weyl特征标公式。

### 9.2 仿射Lie代数

对于仿射Lie代数，有类似的公式。

### 9.3 超对称

对于超Lie代数，有超对称版本的公式。

---

**状态**: ✅ 完成（已深化）
**字数**: 约2,300字
**数学公式数**: 8个
**例子数**: 6个
**最后更新**: 2026年01月02日
