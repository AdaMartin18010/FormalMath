# Gauss-Bonnet定理 - 五种表征

**创建日期**: 2025年12月1日
**领域**: 微分几何
**难度**: L2

---

## 元信息

| 属性 | 内容 |
|------|------|
| **定理** | Gauss-Bonnet定理 |
| **领域** | 微分几何、拓扑学 |
| **历史** | Gauss (局部), Bonnet (整体) |
| **前置知识** | 曲面、曲率、Euler示性数 |

---

## 一、符号表征（形式化）

### 1.1 严格陈述

**Gauss-Bonnet定理**：设 M 是紧致定向二维黎曼流形（无边界），则：

$$\int_M K \, dA = 2\pi \chi(M)$$

其中：

- K = Gauss曲率
- dA = 面积元
- χ(M) = Euler示性数 = V - E + F

### 1.2 带边界版本

设 M 有边界 ∂M，κ_g 是测地曲率，则：

$$\int_M K \, dA + \oint_{\partial M} \kappa_g \, ds = 2\pi \chi(M)$$

### 1.3 Lean 4 形式化

```lean
-- Gauss-Bonnet定理（概念性）
theorem gauss_bonnet {M : Type*} [RiemannianManifold M]
    [CompactSpace M] [TwoDimensional M] [Orientable M] :
    ∫ x, gaussCurvature M x ∂(volumeForm M) =
    2 * Real.pi * (eulerCharacteristic M : ℝ) := by
  sorry  -- 完整证明需要大量微分几何机制
```

### 1.4 证明要点

```text
        [Gauss-Bonnet证明思路]
                │
    ┌───────────┴───────────┐
    │                       │
[局部GB]               [整体化]
三角形内角和            三角剖分
= π + ∫K dA            Σ(局部贡献)
    │                       │
    └───────────┬───────────┘
                │
    内部边抵消，只剩总曲率
    Σ内角 = (V-边界顶点)·2π + 边界角
    结合得 ∫K = 2πχ
```

---

## 二、几何表征（可视化）

### 2.1 不同曲面

```text
        [曲面与Euler数]

    球面 S²           环面 T²          双环面
    χ = 2             χ = 0            χ = -2

     ___              _____
    /   \            / ___ \          ∞∞
   |     |          | |   | |        (两个洞)
    \___/            \_____/

    ∫K = 4π          ∫K = 0          ∫K = -4π
    (正曲率)          (零总曲率)       (负曲率)
```

### 2.2 测地三角形

```text
        [球面三角形]

         A
        /|\
       / | \
      /  |  \
     /   |   \
    B----+----C

    内角和 = π + ∫_△ K dA = π + 面积/R²

    球面上三角形内角和 > π
    （等于 π + 球面三角形面积/R²）
```

### 2.3 曲率直觉

```text
    正曲率（球）     零曲率（柱）     负曲率（马鞍）

       _∩_             |              ___/\___
      /   \            |             /        \
     |     |           |            /          \
      \___/            |

    三角形内角>180°   三角形内角=180°  三角形内角<180°
```

---

## 三、直觉表征（类比）

### 3.1 一句话解释

> **Gauss-Bonnet**：曲面的"总弯曲度"只取决于它的拓扑形状（有几个洞）

### 3.2 披萨定理

```text
平面披萨：切成三角形
├─ 每个顶点周围角度和 = 360°
├─ 总角度 = 顶点数 × 360°
└─ 这是 χ = 1（圆盘）的版本

球面披萨：
├─ 顶点角度和 > 360°（因为弯曲）
├─ "多出来的角度" = 总曲率
└─ 与拓扑有关！
```

### 3.3 虫子爬行

```text
虫子在曲面上走一个闭合路径：
├─ 记录"转向角"
├─ 平面上：回到原点，转了360°
├─ 球面上：转的角度 ≠ 360°
├─ 差值 = 包围区域的总曲率
└─ Gauss-Bonnet！
```

---

## 四、计算表征（算法）

### 4.1 Python计算

```python
import numpy as np

def gauss_bonnet_verification():
    """
    验证Gauss-Bonnet定理
    """
    # 球面 S²: K = 1/R², 面积 = 4πR²
    # ∫K dA = (1/R²) × 4πR² = 4π = 2π × 2 = 2π χ
    R = 1.0
    K_sphere = 1/R**2
    area_sphere = 4 * np.pi * R**2
    integral = K_sphere * area_sphere
    chi_sphere = 2

    print("球面 S²:")
    print(f"  K = 1/R² = {K_sphere}")
    print(f"  面积 = 4πR² = {area_sphere:.4f}")
    print(f"  ∫K dA = {integral:.4f}")
    print(f"  2πχ = 2π × {chi_sphere} = {2*np.pi*chi_sphere:.4f}")
    print()

    # 环面 T²: χ = 0，所以 ∫K = 0
    # 环面有正曲率区域和负曲率区域，正好抵消
    chi_torus = 0
    print("环面 T²:")
    print(f"  χ = {chi_torus}")
    print(f"  ∫K dA = 2πχ = 0（正负曲率抵消）")

gauss_bonnet_verification()
```

### 4.2 离散版本

```python
def discrete_gauss_bonnet(vertices, faces):
    """
    离散Gauss-Bonnet定理

    对于三角网格：
    Σ(2π - 顶点角度和) = 2πχ
    """
    V = len(vertices)
    F = len(faces)
    E = len(set(tuple(sorted([f[i], f[(i+1)%3]]))
                for f in faces for i in range(3)))

    chi = V - E + F

    # 计算每个顶点的角度亏损
    angle_defect = {}
    for v in range(V):
        angle_defect[v] = 2 * np.pi  # 从2π开始减去

    for face in faces:
        # 计算每个顶点处的角度
        for i in range(3):
            v0 = vertices[face[i]]
            v1 = vertices[face[(i+1)%3]]
            v2 = vertices[face[(i+2)%3]]

            # 向量
            vec1 = np.array(v1) - np.array(v0)
            vec2 = np.array(v2) - np.array(v0)

            # 角度
            cos_angle = np.dot(vec1, vec2) / (
                np.linalg.norm(vec1) * np.linalg.norm(vec2))
            angle = np.arccos(np.clip(cos_angle, -1, 1))

            angle_defect[face[i]] -= angle

    total_curvature = sum(angle_defect.values())
    expected = 2 * np.pi * chi

    print(f"V = {V}, E = {E}, F = {F}")
    print(f"χ = V - E + F = {chi}")
    print(f"总角度亏损 = {total_curvature:.4f}")
    print(f"2πχ = {expected:.4f}")

    return chi

# 四面体（球面拓扑）
tetra_v = [(1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1)]
tetra_f = [(0,1,2), (0,2,3), (0,3,1), (1,3,2)]
print("四面体:")
discrete_gauss_bonnet(tetra_v, tetra_f)
```

### 4.3 球面三角形面积

```python
def spherical_triangle_area(angles, R=1):
    """
    球面三角形面积 = R²(A + B + C - π)

    这是Gauss-Bonnet在三角形上的应用
    """
    A, B, C = angles
    excess = A + B + C - np.pi
    area = R**2 * excess

    print(f"角度: A={np.degrees(A):.1f}°, B={np.degrees(B):.1f}°, C={np.degrees(C):.1f}°")
    print(f"角度和: {np.degrees(A+B+C):.1f}°")
    print(f"球面超出: {np.degrees(excess):.1f}°")
    print(f"面积: {area:.4f} (R={R})")

    return area

# 正八面体的一个面（等边球面三角形）
# 在单位球上，角度各为90°
spherical_triangle_area([np.pi/2, np.pi/2, np.pi/2])
```

---

## 五、范畴表征（抽象）

### 5.1 de Rham上同调视角

```text
Gauss-Bonnet 是 ∫: H²(M) → ℝ 的实例

K dA 代表第二陈类 c₁(TM)
∫K dA = ⟨c₁(TM), [M]⟩ = χ(M) × 2π
```

### 5.2 指标定理的先驱

```text
        [Gauss-Bonnet → Atiyah-Singer]
              │
    GB: ∫K = 2πχ（2维）
              │
    推广: ∫Pf(Ω) = χ（2n维）
              │
    更一般: ind(D) = ∫Â × ch
              │
    Atiyah-Singer指标定理
```

### 5.3 特征类

```text
        [示性类视角]
              │
    Euler类 e(TM) ∈ H²ⁿ(M)
              │
    GB: ∫_M e(TM) = χ(M)
              │
    与Stokes定理、de Rham定理联系
```

---

## 六、应用与推广

### 6.1 数学应用

| 应用 | 说明 |
|------|------|
| **曲面分类** | χ决定亏格 |
| **测地线** | 最短路径 |
| **广义相对论** | 时空曲率 |
| **机器人学** | 路径规划 |

### 6.2 高维推广

```text
        [推广层次]
              │
    ┌─────────┼─────────┐
    │         │         │
[Chern-GB]  [Poincaré] [Atiyah-Singer]
4维及更高   Hopf定理    一般流形
    │         │         │
Pfaffian    矢量场零点   椭圆算子指标
```

---

## 关联定理

| 定理 | 关系 |
|------|------|
| **Stokes定理** | 积分基础 |
| **Poincaré-Hopf** | 矢量场零点 |
| **Chern类** | 示性类推广 |
| **Atiyah-Singer** | 终极推广 |

---

**状态**: ✅ 完成
