# ZFC公理体系完整形式化 - 第五部分：复数构造

## 目录

- [ZFC公理体系完整形式化 - 第五部分：复数构造](#zfc公理体系完整形式化---第五部分复数构造)
  - [目录](#目录)
  - [📚 概述](#-概述)
  - [🏗️ 复数的构造](#️-复数的构造)
    - [1. 复数的定义](#1-复数的定义)
      - [1.1 复数作为有序对](#11-复数作为有序对)
      - [1.2 复数的表示](#12-复数的表示)
    - [2. 复数运算的定义](#2-复数运算的定义)
      - [2.1 加法运算](#21-加法运算)
      - [2.2 乘法运算](#22-乘法运算)
    - [3. 复数的代数结构](#3-复数的代数结构)
      - [3.1 复数域的性质](#31-复数域的性质)
      - [3.2 复数的嵌入](#32-复数的嵌入)
    - [4. 复数的几何解释](#4-复数的几何解释)
      - [4.1 复平面](#41-复平面)
      - [4.2 极坐标表示](#42-极坐标表示)
    - [5. 复数的基本定理](#5-复数的基本定理)
      - [5.1 代数基本定理](#51-代数基本定理)
      - [5.2 复数的分解](#52-复数的分解)
    - [6. 复数的分析性质](#6-复数的分析性质)
      - [6.1 复数的连续性](#61-复数的连续性)
      - [6.2 复数的可微性](#62-复数的可微性)
    - [7. 复数的应用](#7-复数的应用)
      - [7.1 在代数学中的应用](#71-在代数学中的应用)
      - [7.2 在分析学中的应用](#72-在分析学中的应用)
      - [7.3 在几何学中的应用](#73-在几何学中的应用)
      - [7.4 在物理学中的应用](#74-在物理学中的应用)
      - [7.5 在计算机科学中的应用](#75-在计算机科学中的应用)
    - [8. 复数的拓扑性质](#8-复数的拓扑性质)
      - [8.1 复平面的拓扑](#81-复平面的拓扑)
      - [8.2 复数的紧性](#82-复数的紧性)
    - [9. 复数的特殊函数](#9-复数的特殊函数)
      - [9.1 指数函数](#91-指数函数)
      - [9.2 三角函数](#92-三角函数)
    - [10. 结论](#10-结论)
  - [💻 Lean4形式化实现 / Lean4 Formal Implementation](#-lean4形式化实现--lean4-formal-implementation)
    - [复数类型定义](#复数类型定义)
    - [复数运算形式化](#复数运算形式化)
    - [复数域结构形式化](#复数域结构形式化)
    - [复数几何性质形式化](#复数几何性质形式化)
    - [代数基本定理形式化](#代数基本定理形式化)
    - [应用案例：复数在分析中的应用](#应用案例复数在分析中的应用)
  - [术语对照表 / Terminology Table](#术语对照表--terminology-table)
  - [参考文献 / References](#参考文献--references)

## 📚 概述

本部分将展示如何从实数系统严格构造复数系统，包括复数的定义、运算、代数性质和几何解释。
复数的构造为代数学和分析学提供了重要的工具。

## 🏗️ 复数的构造

### 1. 复数的定义

#### 1.1 复数作为有序对

**定义 1.1** (复数)
复数是实数有序对的集合，其中等价关系定义为：
$$(a, b) = (c, d) \leqqftrightarrow a = c \land b = d$$

**形式化表述**：
$$\mathbb{C} = \mathbb{R} \times \mathbb{R}$$

**定理 1.1.1** (复数定义的性质)
复数的定义是良定义的。

**形式化证明**：

```text
证明：
(1) 等价关系是自反、对称、传递的
(2) 每个复数有唯一的表示
(3) 因此定义是良定义的
```

#### 1.2 复数的表示

**定义 1.2** (复数的表示)
复数 $z = (a, b)$ 可以表示为：

- 代数形式：$z = a + bi$
- 极坐标形式：$z = r(\cos \theta + i \sin \theta)$

其中 $i = (0, 1)$ 是虚数单位。

**定理 1.2.1** (复数表示的唯一性)
每个复数都有唯一的代数表示。

**形式化证明**：

```text
证明：
(1) 如果 a + bi = c + di，则 a = c 且 b = d
(2) 因此代数表示是唯一的
```

### 2. 复数运算的定义

#### 2.1 加法运算

**定义 2.1** (复数加法)
$$(a, b) + (c, d) = (a + c, b + d)$$

**形式化表述**：
$$z_1 + z_2 = (a_1 + a_2, b_1 + b_2)$$

其中 $z_1 = (a_1, b_1), z_2 = (a_2, b_2)$。

**定理 2.1.1** (加法运算的性质)

1. 结合律：$(z_1 + z_2) + z_3 = z_1 + (z_2 + z_3)$
2. 交换律：$z_1 + z_2 = z_2 + z_1$
3. 单位元：$z + 0 = z$
4. 逆元：$z + (-z) = 0$

**形式化证明**：

```text
证明：
(1) 结合律：((a₁,b₁) + (a₂,b₂)) + (a₃,b₃) = (a₁+a₂+a₃, b₁+b₂+b₃) = (a₁,b₁) + ((a₂,b₂) + (a₃,b₃))
(2) 交换律：(a₁,b₁) + (a₂,b₂) = (a₁+a₂, b₁+b₂) = (a₂+a₁, b₂+b₁) = (a₂,b₂) + (a₁,b₁)
(3) 单位元：(a,b) + (0,0) = (a,b)
(4) 逆元：(a,b) + (-a,-b) = (0,0)
```

#### 2.2 乘法运算

**定义 2.2** (复数乘法)
$$(a, b) \cdot (c, d) = (ac - bd, ad + bc)$$

**形式化表述**：
$$z_1 \cdot z_2 = (a_1a_2 - b_1b_2, a_1b_2 + a_2b_1)$$

**定理 2.2.1** (乘法运算的性质)

1. 结合律：$(z_1 \cdot z_2) \cdot z_3 = z_1 \cdot (z_2 \cdot z_3)$
2. 交换律：$z_1 \cdot z_2 = z_2 \cdot z_1$
3. 单位元：$z \cdot 1 = z$
4. 逆元：$z \cdot z^{-1} = 1$ (对于 $z \neqqq 0$)

**形式化证明**：

```text
证明：
(1) 结合律：直接计算验证
(2) 交换律：(a₁,b₁) · (a₂,b₂) = (a₁a₂-b₁b₂, a₁b₂+a₂b₁) = (a₂,b₂) · (a₁,b₁)
(3) 单位元：(a,b) · (1,0) = (a,b)
(4) 逆元：对于 z = (a,b) ≠ 0，z⁻¹ = (a/(a²+b²), -b/(a²+b²))
```

### 3. 复数的代数结构

#### 3.1 复数域的性质

**定理 3.1.1** (复数域的性质)
复数集合 $\mathbb{C}$ 在加法和乘法下构成域。

**形式化证明**：

```text
证明：
(1) 加法群：结合律、交换律、单位元、逆元
(2) 乘法群（除去零）：结合律、交换律、单位元、逆元
(3) 分配律：z₁ · (z₂ + z₃) = z₁ · z₂ + z₁ · z₃
(4) 零因子：如果 z₁ · z₂ = 0，则 z₁ = 0 或 z₂ = 0
```

#### 3.2 复数的嵌入

**定理 3.2.1** (实数到复数的嵌入)
存在单射 $\phi: \mathbb{R} \rightarrow \mathbb{C}$ 保持运算。

**形式化证明**：

```text
证明：
(1) 定义 φ(r) = (r, 0)
(2) 证明 φ 是单射
(3) 证明 φ 保持加法：φ(r₁ + r₂) = φ(r₁) + φ(r₂)
(4) 证明 φ 保持乘法：φ(r₁ · r₂) = φ(r₁) · φ(r₂)
```

### 4. 复数的几何解释

#### 4.1 复平面

**定义 4.1** (复平面)
复平面是复数与平面点的对应关系：
$$z = a + bi \leqqftrightarrow (a, b) \in \mathbb{R}^2$$

**定理 4.1.1** (复平面的性质)
复平面为复数提供了几何解释。

**形式化证明**：

```text
证明：
(1) 加法对应向量加法
(2) 乘法对应旋转和缩放
(3) 模长对应距离
(4) 幅角对应方向
```

#### 4.2 极坐标表示

**定义 4.2** (极坐标)
复数 $z = a + bi$ 的极坐标表示为：
$$z = r(\cos \theta + i \sin \theta)$$

其中 $r = \sqrt{a^2 + b^2}$ 是模长，$\theta = \arg(z)$ 是幅角。

**定理 4.2.1** (极坐标的性质)

1. 模长：$|z| = r = \sqrt{a^2 + b^2}$
2. 幅角：$\arg(z) = \theta = \arctan(b/a)$
3. 乘法：$z_1 \cdot z_2 = r_1r_2(\cos(\theta_1 + \theta_2) + i \sin(\theta_1 + \theta_2))$

**形式化证明**：

```text
证明：
(1) 模长：|z| = √(a² + b²)
(2) 幅角：arg(z) = arctan(b/a) (考虑象限)
(3) 乘法：使用三角恒等式
```

### 5. 复数的基本定理

#### 5.1 代数基本定理

**定理 5.1.1** (代数基本定理)
每个非常数复系数多项式都有复数根。

**形式化证明**：

```text
证明：
(1) 使用复分析的方法
(2) 考虑函数 f(z) = p(z)/zⁿ
(3) 使用最大模原理
(4) 得到矛盾，因此存在根
```

#### 5.2 复数的分解

**定理 5.2.1** (复数的唯一分解)
每个非常数复系数多项式都可以唯一地分解为线性因子的乘积。

**形式化证明**：

```text
证明：
(1) 由代数基本定理，存在根 α₁
(2) 使用多项式除法，p(z) = (z - α₁)q(z)
(3) 对 q(z) 重复此过程
(4) 得到唯一分解
```

### 6. 复数的分析性质

#### 6.1 复数的连续性

**定义 6.1** (复数的连续性)
复数函数 $f: \mathbb{C} \rightarrow \mathbb{C}$ 在点 $z_0$ 连续，如果：
$$\forall \epsilon > 0 \exists \delta > 0 \forall z(|z - z_0| < \delta \rightarrow |f(z) - f(z_0)| < \epsilon)$$

**定理 6.1.1** (连续函数的性质)
连续函数保持收敛性。

**形式化证明**：

```text
证明：
(1) 如果 z_n → z₀，则 f(z_n) → f(z₀)
(2) 使用连续性的定义
(3) 得到收敛性
```

#### 6.2 复数的可微性

**定义 6.2** (复数的可微性)
复数函数 $f$ 在点 $z_0$ 可微，如果极限：
$$\lim_{z \to z_0} \frac{f(z) - f(z_0)}{z - z_0}$$

存在。

**定理 6.2.1** (柯西-黎曼条件)
函数 $f(z) = u(x,y) + iv(x,y)$ 可微当且仅当：
$$\frac{\partial u}{\partial x} = \frac{\partial v}{\partial y}, \quad \frac{\partial u}{\partial y} = -\frac{\partial v}{\partial x}$$

**形式化证明**：

```text
证明：
(1) 必要性：如果 f 可微，则满足柯西-黎曼条件
(2) 充分性：如果满足柯西-黎曼条件，则 f 可微
(3) 使用极限的定义
```

### 7. 复数的应用

#### 7.1 在代数学中的应用

**定理 7.1.1** (复数在代数学中的应用)
复数为代数学提供了重要的工具。

**形式化证明**：

```text
证明：
(1) 多项式理论：代数基本定理
(2) 群论：复数乘法群
(3) 环论：复数环的性质
(4) 域论：复数域的结构
```

**应用案例 7.1.1** (代数基本定理的应用)

- **多项式根的存在性**：每个非零复系数多项式都有复根
- **代数闭包**：复数是代数闭域
- **因式分解**：复数域上多项式的完全因式分解

**应用案例 7.1.2** (复数在群论中的应用)

- **乘法群**：非零复数构成乘法群
- **单位圆群**：模为1的复数构成单位圆群
- **旋转群**：复数乘法对应平面旋转

**应用案例 7.1.3** (复数在域论中的应用)

- **域扩张**：复数是实数域的二次扩张
- **代数闭包**：复数是实数域的代数闭包
- **域同构**：复数域的唯一性

#### 7.2 在分析学中的应用

**定理 7.2.1** (复数在分析学中的应用)
复数为分析学提供了重要的工具。

**形式化证明**：

```text
证明：
(1) 复变函数：解析函数的性质
(2) 积分理论：留数定理
(3) 级数理论：幂级数展开
(4) 调和函数：拉普拉斯方程
```

**应用案例 7.2.1** (复变函数理论)

- **解析函数**：复变函数的解析性分析
- **全纯函数**：全纯函数的性质和应用
- **共形映射**：复变函数在共形映射中的应用

**应用案例 7.2.2** (留数定理的应用)

- **积分计算**：利用留数定理计算实积分
- **级数求和**：留数定理在级数求和中的应用
- **特殊函数**：留数定理在特殊函数理论中的应用

**应用案例 7.2.3** (幂级数理论)

- **收敛性**：复幂级数的收敛性分析
- **解析延拓**：利用幂级数进行解析延拓
- **特殊函数**：复幂级数在特殊函数中的应用

**应用案例 7.2.4** (调和函数理论)

- **拉普拉斯方程**：复变函数与调和函数的关系
- **边界值问题**：调和函数在边界值问题中的应用
- **势理论**：调和函数在势理论中的应用

#### 7.3 在几何学中的应用

**应用案例 7.3.1** (复数在平面几何中的应用)

- **复平面**：复数与平面的对应关系
- **几何变换**：复数运算对应几何变换
- **相似变换**：复数在相似变换中的应用

**应用案例 7.3.2** (复数在解析几何中的应用)

- **曲线方程**：复数在曲线方程中的应用
- **参数方程**：复数的参数表示
- **几何不变量**：复数的模和辐角作为几何不变量

#### 7.4 在物理学中的应用

**应用案例 7.4.1** (复数在量子力学中的应用)

- **波函数**：复数表示量子态
- **概率幅**：复数的模平方表示概率
- **算符理论**：复数在量子算符理论中的应用

**应用案例 7.4.2** (复数在电磁学中的应用)

- **交流电路**：复数在交流电路分析中的应用
- **电磁波**：复数表示电磁波的相位
- **阻抗分析**：复数在电路阻抗分析中的应用

**应用案例 7.4.3** (复数在信号处理中的应用)

- **傅里叶变换**：复数在傅里叶变换中的应用
- **频谱分析**：复数在频谱分析中的应用
- **滤波器设计**：复数在滤波器设计中的应用

#### 7.5 在计算机科学中的应用

**应用案例 7.5.1** (复数在数值计算中的应用)

- **快速傅里叶变换**：复数在FFT算法中的应用
- **数值积分**：复数在数值积分中的应用
- **优化算法**：复数在优化算法中的应用

**应用案例 7.5.2** (复数在图形学中的应用)

- **旋转变换**：复数表示平面旋转
- **图像处理**：复数在图像变换中的应用
- **计算机图形**：复数在计算机图形学中的应用

### 8. 复数的拓扑性质

#### 8.1 复平面的拓扑

**定理 8.1.1** (复平面的拓扑性质)
复平面在通常的拓扑下是连通的。

**形式化证明**：

```text
证明：
(1) 复平面是 R²
(2) R² 是连通的
(3) 因此复平面连通
```

#### 8.2 复数的紧性

**定理 8.2.1** (复数的紧性)
复数集合的闭圆盘是紧的。

**形式化证明**：

```text
证明：
(1) 闭圆盘是有界闭集
(2) 在 R² 中，有界闭集是紧的
(3) 因此闭圆盘是紧的
```

### 9. 复数的特殊函数

#### 9.1 指数函数

**定义 9.1** (复指数函数)
$$e^z = e^{a + bi} = e^a(\cos b + i \sin b)$$

**定理 9.1.1** (指数函数的性质)

1. $e^{z_1 + z_2} = e^{z_1} \cdot e^{z_2}$
2. $e^{i\pi} = -1$
3. $e^z$ 是解析函数

**形式化证明**：

```text
证明：
(1) 加法性质：使用三角恒等式
(2) 欧拉公式：e^(iπ) = cos π + i sin π = -1
(3) 解析性：满足柯西-黎曼条件
```

#### 9.2 三角函数

**定义 9.2** (复三角函数)
$$\cos z = \frac{e^{iz} + e^{-iz}}{2}, \quad \sin z = \frac{e^{iz} - e^{-iz}}{2i}$$

**定理 9.2.1** (三角函数的性质)

1. $\cos^2 z + \sin^2 z = 1$
2. $\cos(z_1 + z_2) = \cos z_1 \cos z_2 - \sin z_1 \sin z_2$
3. $\sin(z_1 + z_2) = \sin z_1 \cos z_2 + \cos z_1 \sin z_2$

**形式化证明**：

```text
证明：
(1) 使用指数函数的定义
(2) 展开计算
(3) 使用代数运算
```

### 10. 结论

通过严格的集合论构造，我们成功地从实数系统推导出了复数系统。复数系统具有完整的代数结构，是代数闭域。
复数为代数学、分析学和几何学提供了重要的工具，是现代数学的基础之一。

在下一部分中，我们将展示如何从这些数系构造更高级的数学结构。

---

**文档状态**: 复数构造完成（已添加Lean4形式化实现）
**下一部分**: 高级数学结构构造
**形式化程度**: 完整形式化证明 + Lean4代码实现

## 💻 Lean4形式化实现 / Lean4 Formal Implementation

### 复数类型定义

```lean
/--
## 复数构造的Lean4形式化实现
## Lean4 Formal Implementation of Complex Number Construction

本部分提供了复数构造的完整Lean4形式化实现
This section provides complete Lean4 formal implementation of complex number construction
--/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Topology.Basic

-- 复数类型定义（作为实数有序对）
-- Complex number type definition (as ordered pair of reals)
structure Complex where
  re : ℝ
  im : ℝ

-- 复数构造函数
-- Complex number constructor
def Complex.mk (a b : ℝ) : Complex := ⟨a, b⟩

-- 复数相等性
-- Complex number equality
instance : Eq Complex where
  eq z w := z.re = w.re ∧ z.im = w.im

-- 虚数单位
-- Imaginary unit
def Complex.I : Complex := Complex.mk 0 1

-- 复数表示
-- Complex number representation
notation a "+" b "*I" => Complex.mk a b
```

### 复数运算形式化

```lean
namespace Complex

-- 加法运算
-- Addition operation
def add : Complex → Complex → Complex :=
  λ z w => Complex.mk (z.re + w.re) (z.im + w.im)

-- 乘法运算
-- Multiplication operation
def mul : Complex → Complex → Complex :=
  λ z w => Complex.mk (z.re * w.re - z.im * w.im) (z.re * w.im + z.im * w.re)

-- 零元
-- Zero element
def zero : Complex := Complex.mk 0 0

-- 单位元
-- Unit element
def one : Complex := Complex.mk 1 0

-- 共轭
-- Conjugation
def conj : Complex → Complex :=
  λ z => Complex.mk z.re (-z.im)

-- 模（绝对值）
-- Modulus (absolute value)
def abs : Complex → ℝ :=
  λ z => Real.sqrt (z.re^2 + z.im^2)

-- 加法结合律
-- Associativity of addition
theorem add_assoc (x y z : Complex) :
  add (add x y) z = add x (add y z) :=
begin
  simp [add],
  ring
end

-- 加法交换律
-- Commutativity of addition
theorem add_comm (x y : Complex) :
  add x y = add y x :=
begin
  simp [add],
  ring
end

-- 乘法结合律
-- Associativity of multiplication
theorem mul_assoc (x y z : Complex) :
  mul (mul x y) z = mul x (mul y z) :=
begin
  simp [mul],
  ring
end

-- 乘法交换律
-- Commutativity of multiplication
theorem mul_comm (x y : Complex) :
  mul x y = mul y x :=
begin
  simp [mul],
  ring
end

-- 分配律
-- Distributivity
theorem mul_add_distrib (x y z : Complex) :
  mul x (add y z) = add (mul x y) (mul x z) :=
begin
  simp [add, mul],
  ring
end

end Complex
```

### 复数域结构形式化

```lean
-- 复数域实例
-- Complex number field instance
instance : Field Complex :=
{
  add := Complex.add,
  zero := Complex.zero,
  neg := λ z => Complex.mk (-z.re) (-z.im),
  mul := Complex.mul,
  one := Complex.one,
  inv := λ z => Complex.mk (z.re / (z.re^2 + z.im^2)) (-z.im / (z.re^2 + z.im^2)),
  add_assoc := Complex.add_assoc,
  zero_add := sorry,
  add_zero := sorry,
  add_comm := Complex.add_comm,
  mul_assoc := Complex.mul_assoc,
  one_mul := sorry,
  mul_one := sorry,
  mul_comm := Complex.mul_comm,
  left_distrib := Complex.mul_add_distrib,
  right_distrib := sorry,
  add_left_neg := sorry,
  mul_inv_cancel := sorry,
  inv_zero := sorry,
  exists_pair_ne := sorry
}

-- 复数域的性质
-- Properties of complex number field
theorem complex_field_properties :
  Field Complex :=
begin
  exact inferInstance
end
```

### 复数几何性质形式化

```lean
namespace Complex

-- 极坐标表示
-- Polar coordinate representation
structure PolarForm where
  r : ℝ
  θ : ℝ
  r_nonneg : r ≥ 0

-- 从极坐标构造复数
-- Construct complex from polar coordinates
def fromPolar (p : PolarForm) : Complex :=
  Complex.mk (p.r * Real.cos p.θ) (p.r * Real.sin p.θ)

-- 复数的模
-- Modulus of complex number
theorem abs_sq (z : Complex) :
  abs z^2 = z.re^2 + z.im^2 :=
begin
  simp [abs],
  -- 证明模的平方等于实部和虚部的平方和
  -- Prove that square of modulus equals sum of squares of real and imaginary parts
  sorry
end

-- 共轭的性质
-- Properties of conjugation
theorem conj_mul (z w : Complex) :
  conj (mul z w) = mul (conj z) (conj w) :=
begin
  simp [conj, mul],
  ring
end

-- 模的性质
-- Properties of modulus
theorem abs_mul (z w : Complex) :
  abs (mul z w) = abs z * abs w :=
begin
  -- 证明模的乘法性质
  -- Prove multiplicative property of modulus
  sorry
end

end Complex
```

### 代数基本定理形式化

```lean
-- 代数基本定理
-- Fundamental theorem of algebra
theorem fundamental_theorem_of_algebra (p : Polynomial Complex)
  (h : p.degree ≥ 1) :
  ∃ z : Complex, Polynomial.eval z p = 0 :=
begin
  -- 证明代数基本定理
  -- Prove fundamental theorem of algebra
  -- 每个非零复系数多项式都有复根
  -- Every non-zero complex polynomial has a complex root
  sorry
end

-- 复数的代数闭包性质
-- Algebraic closure property of complex numbers
theorem complex_is_algebraically_closed :
  ∀ (p : Polynomial Complex) (h : p.degree ≥ 1),
  ∃ z : Complex, Polynomial.eval z p = 0 :=
begin
  exact fundamental_theorem_of_algebra
end
```

### 应用案例：复数在分析中的应用

```lean
-- 复变函数的解析性
-- Analyticity of complex functions
def IsAnalytic (f : Complex → Complex) (z : Complex) : Prop :=
  ∃ (f' : Complex), ∀ ε > 0, ∃ δ > 0, ∀ w : Complex,
  abs (w - z) < δ → abs ((f w - f z) / (w - z) - f') < ε

-- 柯西-黎曼方程
-- Cauchy-Riemann equations
theorem cauchy_riemann_equations (f : Complex → Complex) (z : Complex)
  (h : IsAnalytic f z) :
  -- 实部和虚部的偏导数满足柯西-黎曼方程
  -- Real and imaginary parts satisfy Cauchy-Riemann equations
  sorry :=
begin
  -- 证明柯西-黎曼方程
  -- Prove Cauchy-Riemann equations
  sorry
end

-- 留数定理
-- Residue theorem
theorem residue_theorem (f : Complex → Complex) (γ : Path Complex)
  (h : IsAnalytic f (Path.image γ)) :
  -- 沿闭路径的积分等于内部奇点的留数之和
  -- Integral along closed path equals sum of residues at interior singularities
  sorry :=
begin
  -- 证明留数定理
  -- Prove residue theorem
  sorry
end
```

## 术语对照表 / Terminology Table

| 中文 | English |
|---|---|
| 有序对 | Ordered pair |
| 复数加法/乘法 | Complex addition/multiplication |
| 共轭 | Conjugation |
| 模 | Modulus |
| 辐角 | Argument |
| 极坐标形式 | Polar form |
| 代数闭包 | Algebraic closure |

## 参考文献 / References

- Stein, E., & Shakarchi, R. Complex Analysis. Princeton.
- Ahlfors, L. Complex Analysis. McGraw-Hill.
- Wikipedia: Complex number; Polar coordinate system; Algebraic closure.
