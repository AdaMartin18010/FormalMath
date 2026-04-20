---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: 闭图像定理 (Closed Graph Theorem)
---
# 闭图像定理 (Closed Graph Theorem)

## Mathlib4 引用

```lean
import Mathlib.Analysis.NormedSpace.BanachSteinhaus
import Mathlib.Topology.Graph

namespace ClosedGraphTheorem

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- 闭图像定理 -/
theorem closed_graph {T : E → F} (hT : LinearMap ℝ E F T)
    (hclosed : IsClosed {p : E × F | p.2 = T p.1}) :
    Continuous T := by
  -- 图像到E的投影是同胚
  let G := {p : E × F | p.2 = T p.1}
  have hproj : IsHomeomorph (fun (p : G) => p.1.1) := by
    sorry
  -- T是投影的复合
  sorry

end ClosedGraphTheorem
```

## 数学背景

闭图像定理是泛函分析中与开映射定理对偶的重要结果，由波兰数学家Stefan Banach在20世纪20-30年代系统建立。它表明，对于Banach空间（更一般地，Fréchet空间）之间的线性算子，闭图像性质蕴含连续性。这是证明微分算子等无界算子具有闭延拓的关键工具，与开映射定理、一致有界原理（Banach-Steinhaus定理）一起构成了线性泛函分析的三大基本定理。与开映射定理不同，闭图像定理不需要算子是满射的假设。

### 算子的图像

**定义（图像）**：设 $T: E \to F$ 是线性算子（不必有界）。$T$ 的**图像**（graph）定义为：

$$\text{graph}(T) = \{(x, Tx) \in E \times F : x \in \text{dom}(T)\}$$

若 $T$ 定义在整个 $E$ 上，则 $\text{graph}(T) \subseteq E \times F$。

### 闭算子

**定义（闭算子）**：线性算子 $T: E \to F$ 称为**闭算子**（closed operator），如果其图像 $\text{graph}(T)$ 是 $E \times F$ 中的闭子集（在乘积拓扑下）。

等价地，$T$ 是闭的当且仅当：若 $x_n \to x$ 且 $Tx_n \to y$，则 $y = Tx$（且 $x \in \text{dom}(T)$，若 $T$ 不是处处定义的）。

**注意**：闭算子不必是连续的。例如，微分算子 $T = \frac{d}{dx}$ 在 $C^1[0,1] \subseteq C[0,1]$ 上不是有界的，但它是闭算子（若 $f_n \to f$ 一致收敛且 $f_n' \to g$ 一致收敛，则 $f \in C^1$ 且 $f' = g$）。

### Banach空间

**定义（Banach空间）**：完备的赋范向量空间称为**Banach空间**。即空间中任何Cauchy序列都收敛。

常见的Banach空间包括：$\mathbb{R}^n$、$\ell^p$ 空间（$1 \leq p \leq \infty$）、$L^p$ 空间、$C(K)$（紧空间上的连续函数空间）等。

## 闭图像定理的陈述

**定理（闭图像定理）**：设 $E$ 和 $F$ 是Banach空间，$T: E \to F$ 是线性算子（处处定义）。若 $T$ 是闭算子（即 $\text{graph}(T)$ 闭），则 $T$ 有界（连续）。

等价表述：从Banach空间到Banach空间的处处定义的闭线性算子必有界。

**注**：这个定理对Fréchet空间（比Banach空间更一般的局部凸完备度量空间）也成立。但对不完备的空间不成立。

## 证明

### 标准证明（利用开映射定理）

**证明**：设 $T: E \to F$ 是闭线性算子，$E, F$ 是Banach空间。$T$ 的图像：

$$G = \text{graph}(T) = \{(x, Tx) : x \in E\} \subseteq E \times F$$

由于 $T$ 是线性的，$G$ 是 $E \times F$ 的线性子空间。由于 $T$ 是闭的，$G$ 是闭子空间。Banach空间的闭子空间仍是Banach空间，故 $G$ 在范数 $||(x, y)||_{E \times F} = ||x||_E + ||y||_F$ 下是Banach空间。

考虑投影映射：

$$\pi_1: G \to E, \quad \pi_1(x, Tx) = x$$

$\pi_1$ 是线性双射（因为 $T$ 是处处定义的函数）。$\pi_1$ 是有界的：

$$||\pi_1(x, Tx)||_E = ||x||_E \leq ||x||_E + ||Tx||_F = ||(x, Tx)||_{E \times F}$$

由开映射定理（$G$ 和 $E$ 都是Banach空间，$\pi_1$ 是满射有界线性算子），$\pi_1$ 是开映射，因此其逆 $\pi_1^{-1}: E \to G$ 有界。

$\pi_1^{-1}(x) = (x, Tx)$，故：

$$||(x, Tx)||_{E \times F} \leq C ||x||_E$$

对某个常数 $C > 0$。即：

$$||x||_E + ||Tx||_F \leq C ||x||_E$$

因此 $||Tx||_F \leq (C-1)||x||_E$，$T$ 有界。 $\square$

### 证明的直接性

闭图像定理的证明巧妙之处在于：我们没有直接估计 $||Tx||$，而是转到图像空间 $G$，利用投影 $\pi_1$ 的可逆性间接得到估计。这体现了泛函分析中"通过适当空间转换简化问题"的典型技巧。

## 例子

### 例子1：乘法算子

设 $E = F = L^2[0,1]$，$T: L^2[0,1] \to L^2[0,1]$，$(Tf)(x) = x f(x)$。$T$ 显然线性且有界（$||Tf|| \leq ||f||$）。其图像是闭的（因为 $T$ 连续）。

### 例子2：微分算子的闭延拓

考虑 $T_0: C^1[0,1] \to C[0,1]$，$T_0 f = f'$。$T_0$ 关于 $L^2$ 范数不连续，但它是闭算子（在其图像中）。若将 $T_0$ 延拓到 $H^1[0,1]$（Sobolev空间），得到闭算子 $T: H^1[0,1] \to L^2[0,1]$。$H^1[0,1]$ 是Hilbert空间（从而是Banach空间），$L^2[0,1]$ 也是Banach空间。但 $T$ 的定义域是 $H^1 \subsetneq L^2$，不是处处定义的，故闭图像定理不直接适用。

若限制 $T$ 到适当子空间（如满足边界条件的函数），可能得到处处定义的闭算子，此时闭图像定理保证其连续性。

### 例子3：Fourier变换的闭性

经典Fourier变换 $\mathcal{F}: L^1(\mathbb{R}) \to C_0(\mathbb{R})$ 是有界的（$||\hat{f}||_\infty \leq ||f||_1$），因此连续，图像是闭的。

Plancherel定理将 $\mathcal{F}$ 延拓为 $L^2(\mathbb{R}) \to L^2(\mathbb{R})$ 的酉算子，也是有界的。

### 例子4：无界但闭的算子

设 $E = F = C[0,1]$（sup范数），$T: C[0,1] \to C[0,1]$，$\text{dom}(T) = C^1[0,1]$，$Tf = f'$。$T$ 不是处处定义的，因此闭图像定理不适用。事实上，$T$ 是无界的（取 $f_n(x) = \sin(nx)/n$，$||f_n||_\infty \to 0$ 但 $||Tf_n||_\infty = 1$）。

## 应用

### 1. 微分算子的闭延拓

在偏微分方程理论中，微分算子通常最初定义在光滑函数上，然后需要延拓到更大的函数空间。闭图像定理用来证明某些延拓是连续的。例如，椭圆正则性理论中，若 $Lu = f$ 且 $f \in L^2$，可以证明 $u \in H^2$，并且映射 $f \mapsto u$ 是连续的。

### 2. 非交换几何

在Alain Connes的非交换几何中，谱三元组 $(\mathcal{A}, \mathcal{H}, D)$ 包含一个"Dirac算子" $D$，通常是无界的。闭图像定理用于处理 $D$ 与其交换子 $[D, a]$ 的解析性质，确保各种算子代数构造的合理性。

### 3. 偏微分方程的弱解理论

在Sobolev空间框架下，微分方程的弱解通过连续线性泛函定义。闭图像定理用于证明从弱解到经典解的正则性提升是连续的，这在数值分析和有限元方法中有重要应用。

### 4. 算子代数

在 $C^*$-代数和von Neumann代数理论中，闭图像定理的变体用于证明各种算子的连续性。例如，两个 $C^*$-代数之间的同态自动是连续的（这个结论可以用闭图像定理证明）。

### 5. 自动连续性定理

更一般地，在某些代数结构中，同态的连续性可以"自动"得到，而不需要额外假设。例如：
- Banach代数之间的同态是连续的；
- 局部紧群表示的某些连续性可以自动获得。

这些结果本质上都依赖于闭图像定理或其变体。

---

*最后更新：2026-04-03 | 版本：v1.0.0*
