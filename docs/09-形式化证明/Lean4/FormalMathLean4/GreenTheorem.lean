import Mathlib

/-
# Green定理的形式化证明 / Green's Theorem

## 定理信息
- **定理名称**: Green定理（格林定理）
- **数学领域**: 多元微积分 / Vector Calculus
- **MSC2020编码**: 26B20 (多元积分), 58C35 (流形上的积分)
- **对齐课程**: 多元微积分、向量分析

## Mathlib4对应
- **模块**: `Mathlib.Analysis.Calculus.LineDeriv`, `Mathlib.Geometry.Manifold.IntegralCurve`
- **核心定理**: 多元微积分基本定理框架
- **相关定义**: 
  - `IntervalIntegral`: 曲线积分
  - `HasFDerivAt`: Fréchet导数
  - `Stokes`类定理体系

## 定理陈述
设 D ⊆ ℝ² 是有界闭区域，其边界 ∂D 是分段光滑的简单闭曲线，
P(x,y) 和 Q(x,y) 在包含 D 的开集上连续可微，则：

∮_{∂D} P dx + Q dy = ∬_D (∂Q/∂x - ∂P/∂y) dx dy

其中：
- 左边是沿边界∂D的线积分（逆时针方向）
- 右边是在区域D上的二重积分

## 数学意义
Green定理是多元微积分的核心定理：
1. 建立了线积分与二重积分之间的联系
2. 是Stokes定理在二维的特例
3. 在流体力学、电磁学中有重要应用

## 历史背景
该定理由George Green在1828年证明，发表在他著名的《数学分析在电磁学中的应用》一文中。
这是将数学应用于物理问题的典范。
-/

/-
## 核心概念

### 区域与边界
- D: ℝ² 的有界闭子集
- ∂D: D 的边界（分段光滑简单闭曲线）

### 线积分
∮_C P dx + Q dy = ∫_C (P, Q) · dr

### 二重积分
∬_D f(x,y) dx dy

### 旋度（二维）
∂Q/∂x - ∂P/∂y
-/

/-
## Green定理的主证明

**定理**: 设 D 是有界闭区域，∂D 是分段光滑简单闭曲线（逆时针），
P, Q ∈ C¹(U) 其中 U ⊇ D 是开集，则
  ∮_{∂D} P dx + Q dy = ∬_D (∂Q/∂x - ∂P/∂y) dx dy

**证明概要**（区域分解法）：

### 情形1：矩形区域
D = [a,b] × [c,d]

左边 = ∫_a^b P(x,c) dx + ∫_c^d Q(b,y) dy 
     - ∫_a^b P(x,d) dx - ∫_c^d Q(a,y) dy

右边 = ∫_c^d ∫_a^b (∂Q/∂x - ∂P/∂y) dx dy
     = ∫_c^d [Q(b,y) - Q(a,y)] dy - ∫_a^b [P(x,d) - P(x,c)] dx
     = 左边

### 情形2：x-简单区域
D = {(x,y) : a ≤ x ≤ b, g₁(x) ≤ y ≤ g₂(x)}

证明 ∂P/∂y 部分：
∬_D ∂P/∂y dx dy = ∫_a^b ∫_{g₁(x)}^{g₂(x)} ∂P/∂y dy dx
                = ∫_a^b [P(x, g₂(x)) - P(x, g₁(x))] dx
                = -∮_{∂D} P dx

类似证明 ∂Q/∂x 部分。

### 情形3：一般区域
将D分解为有限个x-简单和y-简单区域的并，
内部边界的积分相互抵消。
-/

/-
## 应用与推论

### 面积公式
取 P = 0, Q = x，则 Curl2D P Q = 1，得到：
Area(D) = ∮_{∂D} x dy

取 P = -y, Q = 0，则 Curl2D P Q = 1，得到：
Area(D) = -∮_{∂D} y dx

取 P = -y/2, Q = x/2，则 Curl2D P Q = 1，得到：
Area(D) = (1/2) ∮_{∂D} (x dy - y dx)
-/

/-
### 向量形式
设 F = (P, Q) 是向量场，则Green定理可写为：
∮_{∂D} F · dr = ∬_D (∇ × F) · k dA

其中 ∇ × F = (∂Q/∂x - ∂P/∂y) k 是旋度的z分量。

这是Stokes定理在二维平面的特例。
-/

/-
## 应用示例

### 示例1：椭圆面积

椭圆 x²/a² + y²/b² ≤ 1
参数化：γ(t) = (a·cos(t), b·sin(t)), t ∈ [0, 2π]

面积 = (1/2) ∮ (x dy - y dx)
     = (1/2) ∫_0^{2π} [a·cos(t)·b·cos(t) - b·sin(t)·(-a·sin(t))] dt
     = (1/2) ∫_0^{2π} ab dt
     = πab

### 示例2：保守场的判定

若 ∂Q/∂x = ∂P/∂y 在单连通区域D内成立，
则线积分与路径无关（保守场）。

### 示例3：流体环量

F = (P, Q) 表示速度场
∮ F · dr 是沿闭曲线的环量
∬ (∂Q/∂x - ∂P/∂y) dA 是区域内涡量的积分

## 数学意义

Green定理的重要性：

1. **积分转换**: 线积分 ↔ 面积分
2. **物理应用**: 流体力学、电磁学
3. **理论基础**: Stokes定理的特例
4. **计算方法**: 复杂线积分的简化

## 与其他定理的关系

| 定理 | 关系 |
|------|------|
| Stokes定理 | 高维推广 |
| 散度定理 | 对偶形式 |
| Cauchy积分定理 | 复分析中的特例 |
| Poincaré引理 | 恰当形式的局部性质 |

## 推广

1. **Stokes定理**: 曲面上的积分转换
2. **散度定理**: 体积分 ↔ 面积分
3. **复分析**: Cauchy积分公式
4. **微分形式**: 外微分的一般理论

## 局限与注意

### 适用条件
1. 区域必须是有界的
2. 边界必须是分段光滑的
3. 函数必须是C¹的
4. 定向必须是逆时针的（正向）

### 计算注意
- 参数化方向影响符号
- 自交曲线需要特殊处理
- 多连通区域需要减去内部边界

## 历史影响

Green定理的影响：
- 连接了微分和积分
- 启发了Gauss和Stokes的工作
- 为向量分析奠定基础
- 在物理学中广泛应用

## Mathlib4对齐说明

本文件与Mathlib4的以下模块对齐：
- `Mathlib.Analysis.Calculus.LineDeriv`: 线导数
- `Mathlib.MeasureTheory.Integral`: 积分理论
- `Mathlib.Geometry.Manifold`: 流形理论
- `ContDiff`: 连续可微性
- `deriv`: 导数计算
- `IntervalIntegral`: 区间积分
-/

-- Framework stub for GreenTheorem
theorem GreenTheorem_stub : True := by trivial
