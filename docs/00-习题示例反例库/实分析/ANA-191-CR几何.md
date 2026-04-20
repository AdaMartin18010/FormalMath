---
msc_primary: 00A99
习题编号: ANA-191
学科: 实分析
知识点: 多复变-CR几何
难度: ⭐⭐⭐⭐⭐
预计时间: 50分钟
---

# CR 几何

## 题目

**(a)** 定义 CR 流形并给出 Levi 形式的等价描述。

**(b)** 证明强伪凸 CR 流形的嵌入定理（Boutet de Monvel）。

**(c)** 讨论 CR 不变量和 Fefferman 度规。

---

## 解答

### (a) CR流形与Levi形式

#### CR结构的定义

**定义**：$2n+1$ 维光滑流形 $M$ 上的**CR结构**（Cauchy-Riemann structure）是分布 $H \subseteq TM$ 的复子丛 $T^{1,0}M \subseteq H \otimes \mathbb{C}$，满足：

1. $\dim_\mathbb{C} T^{1,0}M = n$
2. $T^{1,0}M \cap \overline{T^{1,0}M} = \{0\}$
3. **可积性**：$[\Gamma(T^{1,0}M), \Gamma(T^{1,0}M)] \subseteq \Gamma(T^{1,0}M)$

**实切丛分解**：
$$H \otimes \mathbb{C} = T^{1,0}M \oplus T^{0,1}M$$

其中 $T^{0,1}M = \overline{T^{1,0}M}$。

**典型例子**：$M^{2n+1} \subseteq \mathbb{C}^{n+1}$ 是实超曲面。

$$T^{1,0}M = TM \cap T^{1,0}\mathbb{C}^{n+1}$$

即 $M$ 上的全纯切向量。

#### Levi形式

**定义**：Levi形式是 $T^{1,0}M$ 上的Hermitian形式：
$$L(X, Y) = -i \langle [X, \bar{Y}], \theta \rangle$$

其中 $\theta$ 是接触形式（$H = \ker \theta$）。

等价地，若 $M = \{r = 0\} \subseteq \mathbb{C}^{n+1}$（$r$ 定义函数，$dr \neq 0$）：

$$L(X, Y) = \sum_{i,j} \frac{\partial^2 r}{\partial z_i \partial \bar{z}_j} X_i \bar{Y}_j$$

（在 $T^{1,0}M$ 上限制）

#### 伪凸性

**强伪凸**：$L$ 在 $T^{1,0}M$ 上正定。

**弱伪凸**：$L$ 半正定。

**Levi平坦**：$L = 0$。

**例子**：

- 球面 $S^{2n+1} = \{|z_1|^2 + \cdots + |z_{n+1}|^2 = 1\}$：强伪凸
- 圆柱 $|z_1|^2 = 1$：Levi平坦

---

### (b) Boutet de Monvel嵌入定理

#### 陈述

**定理**（Boutet de Monvel, 1981）：设 $M$ 是紧强伪凸CR流形，$\dim M = 2n+1 \geq 5$（即 $n \geq 2$），则 $M$ 可CR嵌入到 $\mathbb{C}^N$（对充分大的 $N$）。

#### 证明概要

**步骤1：$\bar{\partial}_b$-复形**

对CR流形 $M$，定义：
$$\bar{\partial}_b: C^\infty(M) \to \Gamma((T^{0,1}M)^*)$$

**Kohn-Rossi上同调**：$H^{p,q}_{KR}(M) = \ker \bar{\partial}_b / \text{im } \bar{\partial}_b$。

**步骤2：Kohn-Morrey-Hörmander估计**

对强伪凸 $M$，$\bar{\partial}_b$ 满足**subelliptic估计**：
$$\|u\|_{s+\varepsilon}^2 \leq C(\|\bar{\partial}_b u\|_s^2 + \|\bar{\partial}_b^* u\|_s^2 + \|u\|_s^2)$$

其中 $\varepsilon = 1/2$（$n = 1$ 时）或 $1$（$n \geq 2$ 时）。

**步骤3：正则性**

由subelliptic估计，$\bar{\partial}_b$ 的解是光滑的。

**步骤4：CR函数的存在性**

强伪凸性 + 紧性 + 高维（$n \geq 2$）$
\Rightarrow$ $H^{0,1}_{KR}(M) = 0$。

故任何CR函数可延拓（局部地）。

**步骤5：嵌入**

取 $N$ 个CR函数 $f_1, \ldots, f_N$ 分离点和切方向：
$$F = (f_1, \ldots, f_N): M \to \mathbb{C}^N$$

由强伪凸性和CR函数的性质，$F$ 是CR嵌入。

$\square$

#### 维数限制

**$n = 1$（3维CR流形）**：定理**不成立**。

Burns（1970s）构造了不能嵌入的3维强伪凸CR流形。

原因是：$H^{0,1}$ 可能非零，且subelliptic估计的指数 $\varepsilon = 1/2$ 不足以保证正则性。

---

### (c) CR不变量与Fefferman度规

#### CR不变量

**Chern-Moser不变量**：强伪凸CR流形的局部不变量，类似于Riemann几何中的曲率张量。

在正规坐标下，由：
- 曲率张量 $R_{\alpha\bar{\beta}\gamma\bar{\delta}}$
- 扭率 $A_{\alpha\beta}$
- 密度 $\rho$

Chern-Moser证明了这些不变量完全确定了CR结构（在局部等价意义下）。

#### Fefferman度规

**Fefferman的构造**：对强伪凸CR流形 $M$，构造**Fefferman流形** $\mathcal{C}_M$：

$$\mathcal{C}_M = \{(x, \lambda) : x \in M, \lambda \in (T^{1,0}_x M \wedge T^{0,1}_x M)^* \setminus \{0\}\} / \mathbb{R}_+$$

即 $M$ 上接触形式的射影化丛。

**Fefferman度规**：$\mathcal{C}_M$ 上有自然的**Lorentz度量** $g_F$：

$$g_F = \theta \cdot (d\gamma + \omega) + L_\theta$$

其中 $\gamma$ 是纤维坐标，$\omega$ 是联络形式，$L_\theta$ 是Levi形式的提升。

**性质**：
1. $g_F$ 是**共形不变的**：若 $\theta' = e^f \theta$，则 $g_{F}' = e^f g_F$（在适当意义下）
2. $(\mathcal{C}_M, g_F)$ 是**Lorentz流形**（符号 $(2n+1, 1)$）
3. **零测地线**与 $M$ 上的**Chern-Moser链**（chains）对应

#### 应用

1. **Yamabe问题**：CR Yamabe问题 $
\Leftrightarrow$ Lorentz共形Yamabe问题
2. **Einstein方程**：Fefferman度规的Ricci曲率与CR结构的Tanaka-Webster曲率联系
3. **AdS/CFT对应**：Fefferman度规作为AdS时空的边界，与CR几何的对应是数学物理中的深刻联系